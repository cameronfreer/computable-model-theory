/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.OraclePred

/-!
# Bounded quantification over a computable list

The scan combinators this library has been writing by hand: `List.all` / `List.any` as folds,
absolutely and relative to an oracle, plus list membership. These replace the repeated typed-`foldr`
constructions that have appeared at four separate call sites.

The `ComputablePredIn.forall_mem_computableList` / `exists_mem_computableList` endpoints built on
top of these are **not** here yet — see the note at the end of the file.

**On equality.** List membership is decided through the *canonical* `Primrec.eq` decision, and
the resulting statement is then transported to ordinary `∈` — not through whatever `DecidableEq`
instance happens to be in scope. Otherwise the statement would look more generic than its
computability proof actually is: a `Decidable` instance carries no computability content, and
agreeing with it extensionally is a separate obligation from computing it.
-/

open Encodable

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
  refine hcanon.of_eq fun a ↦ ?_
  by_cases h : g a ∈ f a
  · rw [decide_eq_true h]
    exact List.any_eq_true.2 ⟨g a, h, by simp⟩
  · rw [decide_eq_false h, ← Bool.not_eq_true]
    intro hc
    obtain ⟨y, hy, hyy⟩ := List.any_eq_true.1 hc
    exact h ((Encodable.encode_inj.1 (of_decide_eq_true hyy)) ▸ hy)

end ComputableIn

/-! ### Not yet: the bounded-quantifier endpoints

`ComputablePredIn.forall_mem_computableList` and `exists_mem_computableList` — taking a uniformly
`O`-computable list and an `O`-computable predicate on input/element pairs and deciding the bounded
quantifier — are the intended public face of this file, and the scans above are exactly what they
need.

What is not yet resolved is the **decidability plumbing**, not the computability. `ComputablePredIn`
bundles a `DecidablePred` witness, and three instances have to be made to agree definitionally: the
one bundled in the hypothesis (at the *paired* type `α × β`), the one bundled in the conclusion (at
`α`), and whichever one `decide` synthesizes inside the `List.all` argument. Supplying the
conclusion's instance as `List.decidableBAll` and the hypothesis's as `hdec (a, x)` leaves a
mismatch against a locally introduced `∀ a x, Decidable (p a x)`; `Decidable` is a subsingleton, so
this is bookkeeping rather than mathematics, but it wants a deliberate pass rather than a hurried
one.
-/
