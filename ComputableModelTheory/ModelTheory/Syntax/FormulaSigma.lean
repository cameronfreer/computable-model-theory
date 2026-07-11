/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.TermSigma

/-!
# The formula alphabet and the formula stack machine

`FormulaSymbol L α` abbreviates the symbol alphabet of mathlib's bounded-formula
encoding; all its components are `Primcodable` for an effective language over a
`Primcodable` variable type, and no new instance is installed (the component instances
synthesize through the abbreviation).

`BoundedFormula.decodeStack` is `BoundedFormula.listDecode` transported to
`listEncode`-images: each decoded formula is represented on the stack by its index
paired with its symbol list (the index must ride along, since the implication,
quantifier, and equality cases branch on it). The bridge
`decodeStack_eq_map_listEncode` states the machine computes exactly `listDecode` in the
pair representation `sigmaRepr`, preserving mathlib's `default` results on every
mismatched-index branch. Primitive recursiveness and the `Primcodable` instances follow
in later sections.
-/

open Encodable

namespace FirstOrder.Language

universe u v u'

variable {L : Language.{u, v}} {α : Type u'}

/-- The symbol alphabet of mathlib's bounded-formula encoding. All components are
`Primcodable` for an effective language over a `Primcodable` variable type; no new
instance is installed. -/
abbrev FormulaSymbol (L : Language.{u, v}) (α : Type u') : Type max u v u' :=
  (Σ k, L.Term (α ⊕ Fin k)) ⊕ ((Σ n, L.Relations n) ⊕ ℕ)

namespace BoundedFormula

/-- The pair representation of a sigma-packaged formula on the shadow stack: its
index together with its symbol list. -/
def sigmaRepr (φ : Σ n, L.BoundedFormula α n) : ℕ × List (FormulaSymbol L α) :=
  (φ.1, φ.2.listEncode)

/-- The shadow of one decoded-stack entry for `sigmaImp`. -/
def imprepr (p q : ℕ × List (FormulaSymbol L α)) : ℕ × List (FormulaSymbol L α) :=
  if p.1 = q.1 then (p.1, Sum.inr (Sum.inr 0) :: p.2 ++ q.2)
  else sigmaRepr default

/-- The shadow of one decoded-stack entry for `sigmaAll`. -/
def allrepr (p : ℕ × List (FormulaSymbol L α)) : ℕ × List (FormulaSymbol L α) :=
  match p.1 with
  | n + 1 => (n, Sum.inr (Sum.inr 1) :: p.2)
  | 0 => sigmaRepr default

/-- The formula stack machine on `listEncode`-images: `listDecode`, with each decoded
formula represented by its index and symbol list. Mirrors the six cases of
`BoundedFormula.listDecode`, including its `default` results on mismatched indices. -/
def decodeStack :
    List (FormulaSymbol L α) → List (ℕ × List (FormulaSymbol L α))
  | Sum.inr (Sum.inr (n + 2)) :: l =>
    (n, [Sum.inr (Sum.inr (n + 2))]) :: decodeStack l
  | Sum.inl ⟨n₁, t₁⟩ :: Sum.inl ⟨n₂, t₂⟩ :: l =>
    (if n₁ = n₂ then (n₁, [Sum.inl ⟨n₁, t₁⟩, Sum.inl ⟨n₂, t₂⟩])
     else sigmaRepr default) :: decodeStack l
  | Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr k) :: l =>
    (if h : ∀ i : Fin n, (l.map Sum.getLeft?)[i]?.join.isSome then
       if ∀ i, (Option.get _ (h i)).1 = k then
         (k, Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr k) :: l.take n)
       else sigmaRepr default
     else sigmaRepr default) :: decodeStack (l.drop n)
  | Sum.inr (Sum.inr 0) :: l =>
    if h : 2 ≤ (decodeStack l).length then
      imprepr ((decodeStack l)[0]'(by omega)) ((decodeStack l)[1]'(by omega)) ::
        (decodeStack l).drop 2
    else []
  | Sum.inr (Sum.inr 1) :: l =>
    if h : 1 ≤ (decodeStack l).length then
      allrepr ((decodeStack l)[0]'(by omega)) :: (decodeStack l).drop 1
    else []
  | _ => []
  termination_by l => l.length

theorem sigmaRepr_imp (p q : Σ n, L.BoundedFormula α n) :
    sigmaRepr (sigmaImp p q) = imprepr (sigmaRepr p) (sigmaRepr q) := by
  rcases p with ⟨m, φ⟩
  rcases q with ⟨n, ψ⟩
  by_cases h : m = n
  · subst h
    rw [sigmaImp_apply]
    simp [sigmaRepr, imprepr, listEncode]
  · rw [sigmaImp]
    simp [sigmaRepr, imprepr, h]
    rw [dif_neg h]

theorem sigmaRepr_all (p : Σ n, L.BoundedFormula α n) :
    sigmaRepr (sigmaAll p) = allrepr (sigmaRepr p) := by
  rcases p with ⟨(- | n), φ⟩
  · simp [sigmaAll, allrepr, sigmaRepr]
  · simp [sigmaAll, allrepr, sigmaRepr, listEncode]

/-- The shadow computes `listDecode` in the pair representation: the exact bridge
between the machine and mathlib's decoder, preserving the `default` behavior on all
mismatched-index branches. -/
theorem decodeStack_eq_map_listEncode (l : List (FormulaSymbol L α)) :
    decodeStack l = (listDecode l).map sigmaRepr := by
  induction hl : l.length using Nat.strong_induction_on generalizing l with
  | _ len ih =>
  subst hl
  match l with
  | [] => simp [decodeStack, listDecode]
  | Sum.inr (Sum.inr (n + 2)) :: l =>
    rw [decodeStack, listDecode, List.map_cons, ih l.length (by simp) l rfl]
    rfl
  | [Sum.inl ⟨n₁, t₁⟩] => simp [decodeStack, listDecode]
  | Sum.inl ⟨n₁, t₁⟩ :: Sum.inl ⟨n₂, t₂⟩ :: l =>
    rw [decodeStack, listDecode, List.map_cons, ih l.length (by simp) l rfl]
    congr 1
    by_cases h : n₁ = n₂
    · subst h
      rw [if_pos rfl, dif_pos rfl]
      rfl
    · rw [if_neg h, dif_neg h]
  | Sum.inl ⟨n₁, t₁⟩ :: Sum.inr g :: l =>
    simp [decodeStack, listDecode]
  | Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr k) :: l =>
    rw [decodeStack, listDecode, List.map_cons, ih (l.drop n).length
      (by simp; omega) (l.drop n) rfl]
    congr 1
    by_cases h : ∀ i : Fin n, (l.map Sum.getLeft?)[i]?.join.isSome
    · rw [dif_pos h, dif_pos h]
      by_cases h' : ∀ i, (Option.get _ (h i)).1 = k
      · rw [if_pos h', dif_pos h']
        simp only [sigmaRepr, listEncode]
        refine congrArg (fun x ↦ (k, x)) ?_
        show Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr k) :: l.take n =
          [Sum.inr (Sum.inl ⟨n, R⟩), Sum.inr (Sum.inr k)] ++
            (List.finRange n).map fun i ↦
              Sum.inl ⟨k, Eq.mp (by rw [h' i]) (Option.get _ (h i)).2⟩
        simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and]
        have key : ∀ i : Fin n, (i : ℕ) < l.length := by
          intro i
          have h0 := h i
          rcases ho : (List.map Sum.getLeft? l)[i]? with - | v
          · rw [ho] at h0
            simp at h0
          · have ho' : (List.map Sum.getLeft? l)[(i : ℕ)]? = some v := ho
            have := (List.getElem?_eq_some_iff.1 ho').1
            simpa using this
        have hlen : n ≤ l.length := by
          by_contra hc
          exact absurd (key ⟨l.length, by omega⟩) (by simp)
        have htake : l.take n = (List.finRange n).map fun j : Fin n ↦ l[(j : ℕ)]'(key j) := by
          refine List.ext_getElem ?_ fun i hi₁ hi₂ ↦ ?_
          · simp [hlen]
          · simp [List.getElem_take]
        rw [htake]
        refine List.map_congr_left fun j hj ↦ ?_
        rcases hli : l[(j : ℕ)]'(key j) with s | g
        · have hgl : (List.map Sum.getLeft? l)[(j : ℕ)]?.join = some s := by
            simp [List.getElem?_eq_getElem (by simpa using key j :
              (j : ℕ) < (List.map Sum.getLeft? l).length), hli]
          have hw : Option.get _ (h j) = s := by
            apply Option.get_of_mem
            exact Option.mem_def.2 hgl
          have hfst : s.fst = k := by
            rw [← hw]
            exact h' j
          subst hw
          congr 1
          refine Sigma.ext hfst ?_
          dsimp only
          exact (cast_heq _ _).symm
        · exfalso
          have hnone : (List.map Sum.getLeft? l)[(j : ℕ)]?.join = none := by
            simp [List.getElem?_eq_getElem (by simpa using key j :
              (j : ℕ) < (List.map Sum.getLeft? l).length), hli]
          have h0 := h j
          rw [show ((List.map Sum.getLeft? l)[j]?) =
            (List.map Sum.getLeft? l)[(j : ℕ)]? from rfl, hnone] at h0
          simp at h0
      · rw [if_neg h', dif_neg h']
    · rw [dif_neg h, dif_neg h]
  | Sum.inr (Sum.inl ⟨n, R⟩) :: ([] : List (FormulaSymbol L α)) =>
    simp [decodeStack, listDecode]
  | Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inl x :: l =>
    simp [decodeStack, listDecode]
  | Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inl y) :: l =>
    simp [decodeStack, listDecode]
  | Sum.inr (Sum.inr 0) :: l =>
    have hd := ih l.length (by simp) l rfl
    rw [decodeStack, listDecode]
    simp only [hd, List.length_map, List.getElem_map]
    by_cases h : 2 ≤ (listDecode (L := L) (α := α) l).length
    · rw [dif_pos h, dif_pos h, List.map_cons, ← List.map_drop, sigmaRepr_imp]
      rfl
    · rw [dif_neg h, dif_neg h]
      rfl
  | Sum.inr (Sum.inr 1) :: l =>
    have hd := ih l.length (by simp) l rfl
    rw [decodeStack, listDecode]
    simp only [hd, List.length_map, List.getElem_map]
    by_cases h : 1 ≤ (listDecode (L := L) (α := α) l).length
    · rw [dif_pos h, dif_pos h, List.map_cons, ← List.map_drop, sigmaRepr_all]
      rfl
    · rw [dif_neg h, dif_neg h]
      rfl

end BoundedFormula

end FirstOrder.Language
