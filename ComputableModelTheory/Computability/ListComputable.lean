/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.PartrecCode

/-!
# Computable functions are closed under list map

Mathlib's `Computable` layer lacks list-recursion combinators (they exist only for
`Primrec`). This file provides `Computable.list_map` and `Computable.list_flatMap` by
step-bounded evaluation: a code for the mapped function is obtained from
`Nat.Partrec.Code.exists_code`, `mapEvaln` runs it elementwise under the primitive
recursive step-bounded evaluator `evaln`, and `Nat.rfindOpt` searches for a sufficient
step bound, which exists by `evaln_complete` since the function is total. Upstream
candidates for mathlib.
-/

open Encodable Nat.Partrec.Code

namespace Computable

variable {β σ : Type*} [Primcodable β] [Primcodable σ]

/-- Step-bounded elementwise evaluation of a code over a list: `some` exactly when every
element's evaluation halts within `k` steps and its result decodes. -/
private def mapEvaln (c : Nat.Partrec.Code) (k : ℕ) : List β → Option (List σ)
  | [] => some []
  | b :: l => ((evaln k c (encode b)).bind fun e ↦ decode (α := σ) e).bind
      fun x ↦ (mapEvaln c k l).map (x :: ·)

private theorem mapEvaln_mono {c : Nat.Partrec.Code} {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    ∀ {l : List β} {m : List σ}, m ∈ mapEvaln c k₁ l → m ∈ mapEvaln c k₂ l := by
  intro l
  induction l with
  | nil => exact fun h ↦ h
  | cons b l ih =>
    intro m hm
    simp only [mapEvaln, Option.mem_def, Option.bind_eq_some_iff, Option.map_eq_some_iff]
      at hm ⊢
    obtain ⟨x, ⟨e, he, hd⟩, m', hm', rfl⟩ := hm
    exact ⟨x, ⟨e, evaln_mono hk he, hd⟩, m', ih hm', rfl⟩

private theorem mapEvaln_complete {c : Nat.Partrec.Code} {g : β → σ}
    (hc : ∀ b : β, encode (g b) ∈ c.eval (encode b)) (l : List β) :
    ∃ k, l.map g ∈ mapEvaln (β := β) (σ := σ) c k l := by
  induction l with
  | nil => exact ⟨0, rfl⟩
  | cons b l ih =>
    obtain ⟨k₁, hk₁⟩ := evaln_complete.1 (hc b)
    obtain ⟨k₂, hk₂⟩ := ih
    refine ⟨max k₁ k₂, ?_⟩
    simp only [List.map_cons, mapEvaln, Option.mem_def, Option.bind_eq_some_iff,
      Option.map_eq_some_iff]
    exact ⟨g b, ⟨encode (g b), evaln_mono (le_max_left _ _) hk₁, encodek _⟩,
      l.map g, mapEvaln_mono (le_max_right _ _) hk₂, rfl⟩

private theorem primrec₂_mapEvaln (c : Nat.Partrec.Code) :
    Primrec₂ fun (l : List β) (k : ℕ) ↦ mapEvaln (σ := σ) c k l := by
  have hev : Primrec fun r : (List β × ℕ) × β × Option (List σ) ↦
      evaln r.1.2 c (encode r.2.1) :=
    primrec_evaln.comp <|
      ((Primrec.snd.comp Primrec.fst).pair (Primrec.const c)).pair
        (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
  have hdec : Primrec fun r : (List β × ℕ) × β × Option (List σ) ↦
      (evaln r.1.2 c (encode r.2.1)).bind fun e ↦ decode (α := σ) e :=
    Primrec.option_bind hev ((Primrec.decode.comp Primrec.snd).to₂)
  have hmap : Primrec fun a : ((List β × ℕ) × β × Option (List σ)) × σ ↦
      (a.1.2.2).map (a.2 :: ·) :=
    Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      ((Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂)
  have hfold : Primrec fun p : List β × ℕ ↦
      p.1.foldr
        (fun b s ↦ ((evaln p.2 c (encode b)).bind fun e ↦ decode (α := σ) e).bind
          fun x ↦ s.map (x :: ·))
        (some []) :=
    Primrec.list_foldr Primrec.fst (Primrec.const (some []))
      ((Primrec.option_bind hdec hmap.to₂).to₂)
  have h2 : Primrec fun p : List β × ℕ ↦ mapEvaln (σ := σ) c p.2 p.1 := by
    refine hfold.of_eq fun p ↦ ?_
    obtain ⟨l, k⟩ := p
    induction l with
    | nil => rfl
    | cons b l ih => simp only [List.foldr_cons, ih]; rfl
  exact h2

/-- Computable functions are closed under `List.map`. Upstream candidate for mathlib. -/
theorem list_map {g : β → σ} (hg : Computable g) : Computable fun l : List β ↦ l.map g := by
  obtain ⟨c, hc⟩ := exists_code.1 hg
  have key : ∀ b : β, encode (g b) ∈ c.eval (encode b) := fun b ↦ by
    rw [hc]
    simp [encodek]
  have hF : Computable₂ fun (l : List β) (k : ℕ) ↦ mapEvaln (σ := σ) c k l :=
    (primrec₂_mapEvaln c).to_comp
  refine (Partrec.rfindOpt hF).of_eq_tot fun l ↦ ?_
  exact (Nat.rfindOpt_mono fun {a m n} hmn ha ↦ mapEvaln_mono hmn ha).2
    (mapEvaln_complete key l)

/-- Computable functions are closed under `List.flatMap`. Upstream candidate for
mathlib. -/
theorem list_flatMap {g : β → List σ} (hg : Computable g) :
    Computable fun l : List β ↦ l.flatMap g :=
  (Primrec.list_flatten.to_comp.comp (list_map hg)).of_eq fun l ↦ by
    rw [List.flatMap_def]

end Computable
