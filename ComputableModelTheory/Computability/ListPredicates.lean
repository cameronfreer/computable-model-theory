/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.List.Dedup
import ComputableModelTheory.Computability.OraclePred

/-!
# Bounded quantification over a computable list

The scan combinators this library has been writing by hand: `List.all` / `List.any` as folds,
absolutely and relative to an oracle, plus list membership, deduplication and the `Nodup` test.
These replace the repeated typed-`foldr` constructions that have appeared at four separate call
sites.

On top of them sit the public endpoints

```
ComputablePredIn.forall_mem_computableList
ComputablePredIn.exists_mem_computableList
```

which take a uniformly `O`-computable list together with an `O`-computable predicate on
input/element pairs and decide the bounded quantifier — covering carrier tuples, symbol scans and
bounded searches uniformly.

**On equality.** List membership is decided through the *canonical* `Primrec.eq` decision, and
the resulting statement is then transported to ordinary `∈` — not through whatever `DecidableEq`
instance happens to be in scope. Otherwise the statement would look more generic than its
computability proof actually is: a `Decidable` instance carries no computability content, and
agreeing with it extensionally is a separate obligation from computing it.
-/

open Encodable

/-! ### The canonical equality scans

Membership and deduplication are *computed* through equality of encodings — the one equality test
with a computability contract — and only afterwards transported to the ordinary `∈`, `List.dedup`
and `List.Nodup`. These two lemmas are the whole transport; every computability statement below
consumes one of them and nothing else. -/

/-- Scanning a list for a matching **encoding** decides ordinary membership. -/
theorem List.any_encode_eq_decide_mem {β : Type*} [Encodable β] [DecidableEq β] (l : List β)
    (b : β) : (l.any fun y ↦ decide (encode y = encode b)) = decide (b ∈ l) := by
  by_cases h : b ∈ l
  · rw [decide_eq_true h]
    exact List.any_eq_true.2 ⟨b, h, by simp⟩
  · rw [decide_eq_false h, ← Bool.not_eq_true]
    intro hc
    obtain ⟨y, hy, hyy⟩ := List.any_eq_true.1 hc
    exact h ((Encodable.encode_inj.1 (of_decide_eq_true hyy)) ▸ hy)

/-- The right fold that drops an element already present downstream is `List.dedup`. -/
theorem List.foldr_cond_any_encode_eq_dedup {β : Type*} [Encodable β] [DecidableEq β]
    (l : List β) :
    (l.foldr (fun b acc ↦ cond (acc.any fun y ↦ decide (encode y = encode b)) acc (b :: acc))
      []) = l.dedup := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldr_cons, ih, List.any_encode_eq_decide_mem]
    by_cases hb : b ∈ l.dedup
    · rw [decide_eq_true hb, Bool.cond_true, List.dedup_cons_of_mem' hb]
    · rw [decide_eq_false hb, Bool.cond_false, List.dedup_cons_of_notMem' hb]

/-- `List.findIdx` as a right fold. The base case `0 = [].length` is why a failed search
returns the length rather than a sentinel: the fold simply never stops incrementing. -/
theorem List.foldr_cond_eq_findIdx {β : Type*} (p : β → Bool) (l : List β) :
    l.foldr (fun b n ↦ cond (p b) 0 (n + 1)) 0 = l.findIdx p := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, ih, List.findIdx_cons]

namespace Primrec

variable {α β : Type*} [Primcodable α] [Primcodable β]

/-- `List.all` as a fold. -/
theorem list_all {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a ↦ (f a).all (p a) := by
  have h : Primrec fun a ↦ (f a).foldr (fun b r ↦ p a b && r) true :=
    Primrec.list_foldr hf (Primrec.const true)
      ((Primrec.and.comp (hp.comp (Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂)
  refine h.of_eq fun a ↦ ?_
  induction f a with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, ih, List.all_cons]

/-- `List.any` as a fold. -/
theorem list_any {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a ↦ (f a).any (p a) := by
  have h : Primrec fun a ↦ (f a).foldr (fun b r ↦ p a b || r) false :=
    Primrec.list_foldr hf (Primrec.const false)
      ((Primrec.or.comp (hp.comp (Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂)
  refine h.of_eq fun a ↦ ?_
  induction f a with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, ih, List.any_cons]

/-- List membership, decided through the **canonical** `Primrec.eq` decision on encodings and then
transported to ordinary `∈`. -/
theorem list_mem [DecidableEq β] {f : α → List β} {g : α → β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a ↦ decide (g a ∈ f a) := by
  have hcanon : Primrec fun a ↦ (f a).any fun y ↦ decide (encode y = encode (g a)) :=
    Primrec.list_any hf
      (((Primrec.eq (α := ℕ)).decide.comp (Primrec.encode.comp Primrec.snd)
        (Primrec.encode.comp (hg.comp Primrec.fst))).to₂)
  exact hcanon.of_eq fun a ↦ List.any_encode_eq_decide_mem _ _

/-- `List.dedup`, computed by a right fold whose membership test is the canonical encoded
equality. -/
theorem list_dedup [DecidableEq β] : Primrec (List.dedup : List β → List β) := by
  have hmem : Primrec₂ fun (_ : List β) (p : β × List β) ↦
      p.2.any fun y ↦ decide (encode y = encode p.1) :=
    (Primrec.list_any (Primrec.snd.comp Primrec.snd)
      (((Primrec.eq (α := ℕ)).decide.comp (Primrec.encode.comp Primrec.snd)
        (Primrec.encode.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))).to₂)).to₂
  have h : Primrec fun l : List β ↦
      l.foldr
        (fun b acc ↦ _root_.cond (acc.any fun y ↦ decide (encode y = encode b)) acc (b :: acc))
        [] :=
    Primrec.list_foldr Primrec.id (Primrec.const [])
      ((Primrec.cond hmem (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))).to₂)
  exact h.of_eq List.foldr_cond_any_encode_eq_dedup

/-- The `List.Nodup` test, computed as "deduplication changes nothing" — again through canonical
encoded equality, here of the two lists. -/
theorem list_nodup [DecidableEq β] : Primrec fun l : List β ↦ decide l.Nodup := by
  have h : Primrec fun l : List β ↦ decide (encode l.dedup = encode l) :=
    (Primrec.eq (α := ℕ)).decide.comp (Primrec.encode.comp list_dedup) Primrec.encode
  refine h.of_eq fun l ↦ decide_eq_decide.2 ⟨fun hc ↦ ?_, fun hl ↦ ?_⟩
  · exact List.dedup_eq_self.1 (Encodable.encode_inj.1 hc)
  · exact congrArg encode (List.dedup_eq_self.2 hl)

end Primrec

namespace ComputableIn

variable {α β : Type*} [Primcodable α] [Primcodable β] {O : Set (ℕ →. ℕ)}

/-- `List.all`, relative to an oracle. -/
theorem list_all {f : α → List β} {p : α → β → Bool} (hf : ComputableIn O f)
    (hp : ComputableIn₂ O p) : ComputableIn O fun a ↦ (f a).all (p a) := by
  have h : ComputableIn O fun a ↦ (f a).foldr (fun b r ↦ p a b && r) true :=
    ComputableIn.list_foldr hf (ComputableIn.const true)
      (((Primrec.and.to_comp.computableIn₂ (O := O)).comp
        (hp.comp ComputableIn.fst (ComputableIn.fst.comp ComputableIn.snd))
        (ComputableIn.snd.comp ComputableIn.snd)).to₂)
  refine h.of_eq fun a ↦ ?_
  induction f a with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, ih, List.all_cons]

/-- `List.any`, relative to an oracle. -/
theorem list_any {f : α → List β} {p : α → β → Bool} (hf : ComputableIn O f)
    (hp : ComputableIn₂ O p) : ComputableIn O fun a ↦ (f a).any (p a) := by
  have h : ComputableIn O fun a ↦ (f a).foldr (fun b r ↦ p a b || r) false :=
    ComputableIn.list_foldr hf (ComputableIn.const false)
      (((Primrec.or.to_comp.computableIn₂ (O := O)).comp
        (hp.comp ComputableIn.fst (ComputableIn.fst.comp ComputableIn.snd))
        (ComputableIn.snd.comp ComputableIn.snd)).to₂)
  refine h.of_eq fun a ↦ ?_
  induction f a with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, ih, List.any_cons]

/-- `List.findIdx`, relative to an oracle. -/
theorem list_findIdx {f : α → List β} {p : α → β → Bool} (hf : ComputableIn O f)
    (hp : ComputableIn₂ O p) : ComputableIn O fun a ↦ (f a).findIdx (p a) := by
  have h : ComputableIn O fun a ↦
      (f a).foldr (fun b n ↦ _root_.cond (p a b) 0 (n + 1)) 0 :=
    ComputableIn.list_foldr hf (ComputableIn.const 0)
      ((ComputableIn.cond (hp.comp ComputableIn.fst (ComputableIn.fst.comp ComputableIn.snd))
        (ComputableIn.const 0)
        ((Primrec.succ.to_comp.computableIn (O := O)).comp
          (ComputableIn.snd.comp ComputableIn.snd))).to₂)
  exact h.of_eq fun a ↦ List.foldr_cond_eq_findIdx _ _

/-- `List.dedup`, relative to an oracle: the absolute fold composed with a computable list. -/
theorem list_dedup [DecidableEq β] {f : α → List β} (hf : ComputableIn O f) :
    ComputableIn O fun a ↦ (f a).dedup :=
  (Primrec.list_dedup.to_comp.computableIn (O := O)).comp hf

/-- The `List.Nodup` test, relative to an oracle. -/
theorem list_nodup [DecidableEq β] {f : α → List β} (hf : ComputableIn O f) :
    ComputableIn O fun a ↦ decide (f a).Nodup :=
  (Primrec.list_nodup.to_comp.computableIn (O := O)).comp hf

/-- List membership, decided through the **canonical** `Primrec.eq` decision rather than an
ambient `DecidableEq` instance, then transported to ordinary `∈`. -/
theorem list_mem [DecidableEq β] {f : α → List β} {g : α → β} (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O fun a ↦ decide (g a ∈ f a) := by
  have hcanon : ComputableIn O fun a ↦ (f a).any fun y ↦
      decide (encode y = encode (g a)) :=
    ComputableIn.list_any hf
      (((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
        (ComputableIn.encode.comp ComputableIn.snd)
        (ComputableIn.encode.comp (hg.comp ComputableIn.fst))).to₂
  exact hcanon.of_eq fun a ↦ List.any_encode_eq_decide_mem _ _

end ComputableIn

namespace ComputablePredIn

variable {α β : Type*} [Primcodable α] [Primcodable β] {O : Set (ℕ →. ℕ)}

/-! ### Bounded quantification over a computable list

The public endpoints. The decidability is handled by **not** trying to align three instances.
The paired witness is chosen once, the Boolean scan is defined using exactly the point decider
derived from it, and the conclusion's `DecidablePred` is then *defined from the scan's semantic
specification* — so agreement is built into its construction rather than recovered by a
subsingleton transport. No ambient synthesis and no `List.decidableBAll` is involved. -/

/-- **Bounded universal quantification over a computable list.** -/
theorem forall_mem_computableList {l : α → List β} {p : α → β → Prop}
    (hl : ComputableIn O l) (hp : ComputablePredIn O fun q : α × β ↦ p q.1 q.2) :
    ComputablePredIn O fun a ↦ ∀ x ∈ l a, p a x := by
  obtain ⟨Dpair, hcomp⟩ := hp
  let Dpoint : ∀ a b, Decidable (p a b) := fun a b ↦ Dpair (a, b)
  let scan : α → Bool := fun a ↦ (l a).all fun b ↦ @decide (p a b) (Dpoint a b)
  have hspec : ∀ a, scan a = true ↔ ∀ b ∈ l a, p a b := by
    intro a
    show ((l a).all fun b ↦ @decide (p a b) (Dpoint a b)) = true ↔ _
    rw [List.all_eq_true]
    exact ⟨fun h b hb ↦ of_decide_eq_true (h b hb), fun h b hb ↦ decide_eq_true (h b hb)⟩
  have hscan : ComputableIn O scan :=
    ComputableIn.list_all hl ((hcomp.comp (ComputableIn.fst.pair ComputableIn.snd)).to₂)
  exact ⟨fun a ↦ decidable_of_iff (scan a = true) (hspec a),
    hscan.of_eq fun a ↦ Bool.eq_iff_iff.2 ((hspec a).trans
      (@decide_eq_true_iff _ (decidable_of_iff (scan a = true) (hspec a))).symm)⟩

/-- **Bounded existential quantification over a computable list.** -/
theorem exists_mem_computableList {l : α → List β} {p : α → β → Prop}
    (hl : ComputableIn O l) (hp : ComputablePredIn O fun q : α × β ↦ p q.1 q.2) :
    ComputablePredIn O fun a ↦ ∃ x ∈ l a, p a x := by
  obtain ⟨Dpair, hcomp⟩ := hp
  let Dpoint : ∀ a b, Decidable (p a b) := fun a b ↦ Dpair (a, b)
  let scan : α → Bool := fun a ↦ (l a).any fun b ↦ @decide (p a b) (Dpoint a b)
  have hspec : ∀ a, scan a = true ↔ ∃ b ∈ l a, p a b := by
    intro a
    show ((l a).any fun b ↦ @decide (p a b) (Dpoint a b)) = true ↔ _
    rw [List.any_eq_true]
    exact ⟨fun ⟨b, hb, h⟩ ↦ ⟨b, hb, of_decide_eq_true h⟩,
      fun ⟨b, hb, h⟩ ↦ ⟨b, hb, decide_eq_true h⟩⟩
  have hscan : ComputableIn O scan :=
    ComputableIn.list_any hl ((hcomp.comp (ComputableIn.fst.pair ComputableIn.snd)).to₂)
  exact ⟨fun a ↦ decidable_of_iff (scan a = true) (hspec a),
    hscan.of_eq fun a ↦ Bool.eq_iff_iff.2 ((hspec a).trans
      (@decide_eq_true_iff _ (decidable_of_iff (scan a = true) (hspec a))).symm)⟩

end ComputablePredIn
