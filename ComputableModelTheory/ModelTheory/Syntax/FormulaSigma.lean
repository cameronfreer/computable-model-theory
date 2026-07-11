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
mismatched-index branch. `primrec_decodeStack` proves the machine primitive recursive by
course-of-values recursion on the suffix length (`decodeStackAux` is the length-guarded
suffix evaluation, `decodeStackStepAux` the course-of-values step); the `Primcodable`
instances for formulas build on it.
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
  · rw [sigmaImp, dif_neg h, imprepr]
    simp only [sigmaRepr]
    rw [if_neg h]

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

/-! ### The guarded suffix machine

Course-of-values recursion on the suffix length: `decodeStackAux l m` evaluates the
machine on the length-`m` suffix of `l` (and returns `[]` on out-of-range indices, so
that every recursive dependency sits at a strictly smaller index), and
`decodeStackStepAux` computes one step from the table of all shorter-suffix values. -/

/-- The length-guarded suffix evaluation of the formula stack machine. -/
def decodeStackAux (l : List (FormulaSymbol L α)) (m : ℕ) :
    List (ℕ × List (FormulaSymbol L α)) :=
  if m ≤ l.length then decodeStack (l.drop (l.length - m)) else []

/-- At the full length, the guarded suffix evaluation is the machine itself. -/
theorem decodeStackAux_length (l : List (FormulaSymbol L α)) :
    decodeStackAux l l.length = decodeStack l := by
  rw [decodeStackAux, if_pos le_rfl]
  simp

/-- In range, the guarded suffix evaluation is the machine on the suffix. -/
theorem decodeStackAux_of_le {l : List (FormulaSymbol L α)} {m : ℕ} (hm : m ≤ l.length) :
    decodeStackAux l m = decodeStack (l.drop (l.length - m)) := by
  rw [decodeStackAux, if_pos hm]

/-- Whether a symbol is a term letter with the given variable index. -/
def isTermLetterAt (k : ℕ) : FormulaSymbol L α → Bool
  | Sum.inl s => s.1 = k
  | _ => false

/-- One backward step of the guarded machine, reading previous values: the
course-of-values candidate for `Primrec.nat_strong_rec`. `prev` holds
`decodeStackAux l j` for `j < prev.length`. -/
private def decodeStackStepAux (l : List (FormulaSymbol L α))
    (prev : List (List (ℕ × List (FormulaSymbol L α)))) :
    Option (List (ℕ × List (FormulaSymbol L α))) :=
  let m := prev.length
  if m ≤ l.length then
    match l.drop (l.length - m) with
    | [] => some []
    | Sum.inr (Sum.inr (n + 2)) :: _ =>
      (prev[m - 1]?).map fun rest ↦ (n, [Sum.inr (Sum.inr (n + 2))]) :: rest
    | Sum.inl s₁ :: Sum.inl s₂ :: _ =>
      (prev[m - 2]?).map fun rest ↦
        (if s₁.1 = s₂.1 then (s₁.1, [Sum.inl s₁, Sum.inl s₂])
         else sigmaRepr default) :: rest
    | Sum.inr (Sum.inl r) :: Sum.inr (Sum.inr k) :: s' =>
      (prev[m - 2 - r.1]?).map fun rest ↦
        (if (s'.take r.1).length = r.1 ∧ (s'.take r.1).all (isTermLetterAt k) then
          (k, Sum.inr (Sum.inl r) :: Sum.inr (Sum.inr k) :: s'.take r.1)
         else sigmaRepr default) :: rest
    | Sum.inr (Sum.inr 0) :: _ =>
      (prev[m - 1]?).map fun D ↦
        if 2 ≤ D.length then imprepr D[0]! D[1]! :: D.drop 2 else []
    | Sum.inr (Sum.inr 1) :: _ =>
      (prev[m - 1]?).map fun D ↦
        if 1 ≤ D.length then allrepr D[0]! :: D.drop 1 else []
    | _ :: _ => some []
  else some []

/-- The Boolean relation-argument condition matches mathlib's two dite guards. -/
theorem rel_cond_iff (s' : List (FormulaSymbol L α)) (n k : ℕ) :
    ((s'.take n).length = n ∧ (s'.take n).all (isTermLetterAt k)) ↔
      ∃ h : ∀ i : Fin n, ((s'.map Sum.getLeft?)[i]?.join).isSome,
        ∀ i, (Option.get _ (h i)).1 = k := by
  constructor
  · rintro ⟨hlen, hall⟩
    have hle : n ≤ s'.length := by
      by_contra hc
      simp [List.length_take] at hlen
      omega
    have hget : ∀ i : Fin n, ∃ s : Σ k', L.Term (α ⊕ Fin k'),
        s'[(i : ℕ)]'(by omega) = Sum.inl s ∧ s.1 = k := by
      intro i
      have hti : (i : ℕ) < (s'.take n).length := by
        simp [List.length_take]
        omega
      have hmem : s'[(i : ℕ)]'(by omega) ∈ s'.take n := by
        rw [← List.getElem_take (h := hti)]
        exact List.getElem_mem _
      have := List.all_eq_true.1 hall _ hmem
      rcases hli : s'[(i : ℕ)]'(by omega) with s | g
      · rw [hli] at this
        exact ⟨s, rfl, by simpa [isTermLetterAt] using this⟩
      · rw [hli] at this
        simp [isTermLetterAt] at this
    have h : ∀ i : Fin n, ((s'.map Sum.getLeft?)[i]?.join).isSome := by
      intro i
      obtain ⟨s, hs, -⟩ := hget i
      simp [List.getElem?_eq_getElem (show (i : ℕ) < (s'.map Sum.getLeft?).length by
        simp; omega), hs]
    refine ⟨h, fun i ↦ ?_⟩
    obtain ⟨s, hs, hk⟩ := hget i
    have : Option.get _ (h i) = s := by
      apply Option.get_of_mem
      have : (s'.map Sum.getLeft?)[(i : ℕ)]?.join = some s := by
        simp [List.getElem?_eq_getElem (show (i : ℕ) < (s'.map Sum.getLeft?).length by
          simp; omega), hs]
      exact Option.mem_def.2 this
    rw [this]
    exact hk
  · rintro ⟨h, h'⟩
    have hle : ∀ i : Fin n, (i : ℕ) < s'.length := by
      intro i
      have h0 := h i
      rcases ho : (s'.map Sum.getLeft?)[i]? with - | v
      · rw [ho] at h0
        simp at h0
      · have ho' : (s'.map Sum.getLeft?)[(i : ℕ)]? = some v := ho
        have := (List.getElem?_eq_some_iff.1 ho').1
        simpa using this
    have hlen : n ≤ s'.length := by
      by_contra hc
      exact absurd (hle ⟨s'.length, by omega⟩) (by simp)
    refine ⟨by simp [hlen], List.all_eq_true.2 fun c hc ↦ ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hi' : i < n := by simpa [hlen] using hi
    rw [List.getElem_take]
    have h0 := h ⟨i, hi'⟩
    rcases hli : s'[i]'(by omega) with s | g
    · have hgl : (s'.map Sum.getLeft?)[i]?.join = some s := by
        simp [List.getElem?_eq_getElem (show i < (s'.map Sum.getLeft?).length by
          simp; omega), hli]
      have hw : Option.get _ (h ⟨i, hi'⟩) = s := by
        apply Option.get_of_mem
        exact Option.mem_def.2 hgl
      have := h' ⟨i, hi'⟩
      rw [hw] at this
      simp [isTermLetterAt, this]
    · exfalso
      have hnone : (s'.map Sum.getLeft?)[i]?.join = none := by
        simp [List.getElem?_eq_getElem (show i < (s'.map Sum.getLeft?).length by
          simp; omega), hli]
      rw [show ((s'.map Sum.getLeft?)[(⟨i, hi'⟩ : Fin n)]?) =
        (s'.map Sum.getLeft?)[i]? from rfl, hnone] at h0
      simp at h0

/-- The relation branch of `decodeStack` in Boolean-condition form. -/
theorem rel_branch_eq (s' : List (FormulaSymbol L α)) (n k : ℕ) (R : L.Relations n) :
    (if h : ∀ i : Fin n, ((s'.map Sum.getLeft?)[i]?.join).isSome then
       if ∀ i, (Option.get _ (h i)).1 = k then
         ((k, Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr k) :: s'.take n) :
           ℕ × List (FormulaSymbol L α))
       else sigmaRepr default
     else sigmaRepr default) =
    (if (s'.take n).length = n ∧ (s'.take n).all (isTermLetterAt k) then
       (k, Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr k) :: s'.take n)
     else sigmaRepr default) := by
  by_cases hb : (s'.take n).length = n ∧ (s'.take n).all (isTermLetterAt k)
  · obtain ⟨h, h'⟩ := (rel_cond_iff s' n k).1 hb
    rw [if_pos hb, dif_pos h, if_pos h']
  · rw [if_neg hb]
    by_cases h : ∀ i : Fin n, ((s'.map Sum.getLeft?)[i]?.join).isSome
    · rw [dif_pos h]
      by_cases h' : ∀ i, (Option.get _ (h i)).1 = k
      · exact absurd ((rel_cond_iff s' n k).2 ⟨h, h'⟩) hb
      · rw [if_neg h']
    · rw [dif_neg h]

/-- The `imp` case of `decodeStack` in `getElem!` form (no dependent proofs). -/
theorem decodeStack_imp_eq (s : List (FormulaSymbol L α)) :
    decodeStack (Sum.inr (Sum.inr 0) :: s) =
      if 2 ≤ (decodeStack s).length then
        imprepr (decodeStack s)[0]! (decodeStack s)[1]! :: (decodeStack s).drop 2
      else [] := by
  rw [decodeStack]
  by_cases h : 2 ≤ (decodeStack s).length
  · rw [dif_pos h, if_pos h, getElem!_pos _ _ (by omega), getElem!_pos _ _ (by omega)]
  · rw [dif_neg h, if_neg h]

/-- The `all` case of `decodeStack` in `getElem!` form (no dependent proofs). -/
theorem decodeStack_all_eq (s : List (FormulaSymbol L α)) :
    decodeStack (Sum.inr (Sum.inr 1) :: s) =
      if 1 ≤ (decodeStack s).length then
        allrepr (decodeStack s)[0]! :: (decodeStack s).drop 1
      else [] := by
  rw [decodeStack]
  by_cases h : 1 ≤ (decodeStack s).length
  · rw [dif_pos h, if_pos h, getElem!_pos _ _ (by omega)]
  · rw [dif_neg h, if_neg h]

/-- The `rel` case of `decodeStack` in Boolean-condition form. -/
theorem decodeStack_rel_eq (n : ℕ) (R : L.Relations n) (k : ℕ)
    (s' : List (FormulaSymbol L α)) :
    decodeStack (Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr k) :: s') =
      (if (s'.take n).length = n ∧ (s'.take n).all (isTermLetterAt k) then
        (k, Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr k) :: s'.take n)
       else sigmaRepr default) :: decodeStack (s'.drop n) := by
  rw [decodeStack, rel_branch_eq]

/-- The step function meets the course-of-values specification. -/
private theorem decodeStackStepAux_spec (l : List (FormulaSymbol L α)) (m : ℕ) :
    decodeStackStepAux l ((List.range m).map (decodeStackAux l)) =
      some (decodeStackAux l m) := by
  have hprev : ∀ j, j < m →
      ((List.range m).map (decodeStackAux l))[j]? = some (decodeStackAux l j) := by
    intro j hj
    simp [hj]
  rw [decodeStackStepAux]
  simp only [List.length_map, List.length_range]
  by_cases hm : m ≤ l.length
  · rw [if_pos hm]
    rcases hs : l.drop (l.length - m) with - | ⟨c, s⟩
    · have hm0 : m = 0 := by
        have := congrArg List.length hs
        simp at this
        omega
      subst hm0
      rw [decodeStackAux, if_pos hm, hs]
      simp [decodeStack]
    · have hmlen : m = (l.drop (l.length - m)).length := by simp; omega
      have hm1 : 1 ≤ m := by
        rw [hs] at hmlen
        simp at hmlen
        omega
      have hstail : s = l.drop (l.length - (m - 1)) := by
        have h1 := congrArg List.tail hs
        rw [List.tail_drop] at h1
        have h2 : l.length - m + 1 = l.length - (m - 1) := by omega
        rw [h2] at h1
        exact h1.symm
      have hds1 : decodeStack s = decodeStackAux l (m - 1) := by
        rw [decodeStackAux_of_le (show m - 1 ≤ l.length by omega), ← hstail]
      rw [decodeStackAux_of_le hm, hs]
      match c, s with
      | Sum.inr (Sum.inr (n + 2)), s =>
        rw [hprev (m - 1) (by omega), decodeStack, hds1]
        rfl
      | Sum.inl ⟨n₁, t₁⟩, [] =>
        simp [decodeStack]
      | Sum.inl ⟨n₁, t₁⟩, Sum.inl ⟨n₂, t₂⟩ :: s'' =>
        rw [hs] at hmlen
        simp only [List.length_cons] at hmlen
        have hstail2 : s'' = l.drop (l.length - (m - 2)) := by
          have h1 := congrArg List.tail hstail
          rw [List.tail_drop] at h1
          have h2 : l.length - (m - 1) + 1 = l.length - (m - 2) := by omega
          rw [h2] at h1
          simpa using h1
        have hds2 : decodeStack s'' = decodeStackAux l (m - 2) := by
          rw [decodeStackAux_of_le (show m - 2 ≤ l.length by omega), ← hstail2]
        rw [hprev (m - 2) (by omega), decodeStack, hds2]
        rfl
      | Sum.inl ⟨n₁, t₁⟩, Sum.inr g :: s'' =>
        simp [decodeStack]
      | Sum.inr (Sum.inl ⟨n, R⟩), [] =>
        simp [decodeStack]
      | Sum.inr (Sum.inl ⟨n, R⟩), Sum.inl x :: s'' =>
        simp [decodeStack]
      | Sum.inr (Sum.inl ⟨n, R⟩), Sum.inr (Sum.inl y) :: s'' =>
        simp [decodeStack]
      | Sum.inr (Sum.inl ⟨n, R⟩), Sum.inr (Sum.inr k) :: s' =>
        rw [hs] at hmlen
        simp only [List.length_cons] at hmlen
        have hstail2 : s' = l.drop (l.length - (m - 2)) := by
          have h1 := congrArg List.tail hstail
          rw [List.tail_drop] at h1
          have h2 : l.length - (m - 1) + 1 = l.length - (m - 2) := by omega
          rw [h2] at h1
          simpa using h1
        have hdsr : decodeStack (s'.drop n) = decodeStackAux l (m - 2 - n) := by
          by_cases hn : n ≤ m - 2
          · rw [decodeStackAux_of_le (show m - 2 - n ≤ l.length by omega), hstail2,
              List.drop_drop, show l.length - (m - 2) + n = l.length - (m - 2 - n) by omega]
          · rw [List.drop_eq_nil_of_le (by omega), show m - 2 - n = 0 by omega,
              decodeStackAux, if_pos (Nat.zero_le _), Nat.sub_zero, List.drop_length]
        show Option.map
            (fun rest ↦
              (if (s'.take n).length = n ∧ (s'.take n).all (isTermLetterAt k) then
                (k, Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr k) :: s'.take n)
               else sigmaRepr default) :: rest)
            (((List.range m).map (decodeStackAux l))[m - 2 - n]?) =
          some (decodeStack (Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr k) :: s'))
        rw [hprev (m - 2 - n) (by omega), decodeStack_rel_eq, hdsr]
        rfl
      | Sum.inr (Sum.inr 0), s =>
        rw [hprev (m - 1) (by omega), decodeStack_imp_eq, hds1]
        rfl
      | Sum.inr (Sum.inr 1), s =>
        rw [hprev (m - 1) (by omega), decodeStack_all_eq, hds1]
        rfl
  · rw [if_neg hm, decodeStackAux, if_neg hm]

/-! ### Primitive recursiveness of the step function -/

/-- The falsum branch of the step function. -/
private def stepFalsum (prev : List (List (ℕ × List (FormulaSymbol L α)))) (n : ℕ) :
    Option (List (ℕ × List (FormulaSymbol L α))) :=
  (prev[prev.length - 1]?).map fun rest ↦ (n, [Sum.inr (Sum.inr (n + 2))]) :: rest

/-- The equality branch of the step function. -/
private def stepEqual (prev : List (List (ℕ × List (FormulaSymbol L α))))
    (s₁ s₂ : Σ k, L.Term (α ⊕ Fin k)) : Option (List (ℕ × List (FormulaSymbol L α))) :=
  (prev[prev.length - 2]?).map fun rest ↦
    (if s₁.1 = s₂.1 then (s₁.1, [Sum.inl s₁, Sum.inl s₂]) else sigmaRepr default) :: rest

/-- The relation branch of the step function. -/
private def stepRel (prev : List (List (ℕ × List (FormulaSymbol L α))))
    (r : Σ n, L.Relations n) (k : ℕ) (s' : List (FormulaSymbol L α)) :
    Option (List (ℕ × List (FormulaSymbol L α))) :=
  (prev[prev.length - 2 - r.1]?).map fun rest ↦
    (if (s'.take r.1).length = r.1 ∧ (s'.take r.1).all (isTermLetterAt k) then
      (k, Sum.inr (Sum.inl r) :: Sum.inr (Sum.inr k) :: s'.take r.1)
     else sigmaRepr default) :: rest

/-- The implication branch of the step function. -/
private def stepImp (prev : List (List (ℕ × List (FormulaSymbol L α)))) :
    Option (List (ℕ × List (FormulaSymbol L α))) :=
  (prev[prev.length - 1]?).map fun D ↦
    if 2 ≤ D.length then imprepr D[0]! D[1]! :: D.drop 2 else []

/-- The quantifier branch of the step function. -/
private def stepAll (prev : List (List (ℕ × List (FormulaSymbol L α)))) :
    Option (List (ℕ × List (FormulaSymbol L α))) :=
  (prev[prev.length - 1]?).map fun D ↦
    if 1 ≤ D.length then allrepr D[0]! :: D.drop 1 else []

/-- The step function as a tree of `casesOn` dispatches to the branch functions: the
combinator-friendly form behind `primrec₂_decodeStackStepAux`. -/
private theorem decodeStackStepAux_eq_cases (l : List (FormulaSymbol L α))
    (prev : List (List (ℕ × List (FormulaSymbol L α)))) :
    decodeStackStepAux l prev =
      if prev.length ≤ l.length then
        List.casesOn (List.drop (l.length - prev.length) l)
          (some ([] : List (ℕ × List (FormulaSymbol L α))))
          (fun c tail ↦
            Sum.casesOn c
              (fun s₁ ↦ List.casesOn tail (some [])
                fun c₂ _ ↦ Sum.casesOn c₂ (fun s₂ ↦ stepEqual prev s₁ s₂)
                  fun _ ↦ some [])
              fun g ↦ Sum.casesOn g
                (fun r ↦ List.casesOn tail (some [])
                  fun c₂ s' ↦ Sum.casesOn c₂ (fun _ ↦ some [])
                    fun g₂ ↦ Sum.casesOn g₂ (fun _ ↦ some []) fun k ↦ stepRel prev r k s')
                fun j ↦ Nat.casesOn j (stepImp prev)
                  fun j' ↦ Nat.casesOn j' (stepAll prev) fun n ↦ stepFalsum prev n)
      else some [] := by
  rw [decodeStackStepAux]
  by_cases hg : prev.length ≤ l.length
  · rw [if_pos hg, if_pos hg]
    rcases l.drop (l.length - prev.length) with - | ⟨c, tail⟩
    · rfl
    · rcases c with s₁ | g
      · rcases tail with - | ⟨c₂, tail₂⟩
        · rfl
        · rcases c₂ with s₂ | g₂ <;> rfl
      · rcases g with r | j
        · rcases tail with - | ⟨c₂, s'⟩
          · rfl
          · rcases c₂ with x | g₂
            · rfl
            · rcases g₂ with y | k <;> rfl
        · rcases j with - | j'
          · rfl
          · rcases j' with - | n <;> rfl
  · rw [if_neg hg, if_neg hg]

section PrimrecStep

variable [Primcodable α] [L.EffectiveLanguage]

/-- The `sigmaImp` shadow on stack entries is primitive recursive. -/
theorem primrec₂_imprepr : Primrec₂ (imprepr (L := L) (α := α)) := by
  have h : Primrec fun p :
      (ℕ × List (FormulaSymbol L α)) × ℕ × List (FormulaSymbol L α) ↦
      if p.1.1 = p.2.1 then (p.1.1, (Sum.inr (Sum.inr 0) :: p.1.2) ++ p.2.2)
      else sigmaRepr (L := L) (α := α) default :=
    Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.list_append.comp
          (Primrec.list_cons.comp (Primrec.const _) (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd)))
      (Primrec.const _)
  exact h.of_eq fun p ↦ by rw [imprepr]

/-- The `sigmaAll` shadow on stack entries is primitive recursive. -/
theorem primrec_allrepr : Primrec (allrepr (L := L) (α := α)) := by
  have h : Primrec fun p : ℕ × List (FormulaSymbol L α) ↦
      Nat.casesOn (motive := fun _ ↦ ℕ × List (FormulaSymbol L α)) p.1
        (sigmaRepr (L := L) (α := α) default)
        fun n ↦ (n, Sum.inr (Sum.inr 1) :: p.2) :=
    Primrec.nat_casesOn Primrec.fst (Primrec.const _)
      ((Primrec.pair Primrec.snd
        (Primrec.list_cons.comp (Primrec.const _) (Primrec.snd.comp Primrec.fst))).to₂)
  exact h.of_eq fun p ↦ by rcases p with ⟨- | n, s⟩ <;> rfl

/-- The term-letter-with-index test is primitive recursive. -/
theorem primrec₂_isTermLetterAt : Primrec₂ (isTermLetterAt (L := L) (α := α)) := by
  have h : Primrec fun p : ℕ × FormulaSymbol L α ↦
      Sum.casesOn (motive := fun _ ↦ Bool) p.2 (fun s ↦ decide (s.1 = p.1)) fun _ ↦ false :=
    Primrec.sumCasesOn Primrec.snd
      ((Primrec.eq.decide.comp ((Term.primrec_sigmaTerm_fst L α).comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst)).to₂)
      ((Primrec.const false).to₂)
  exact h.of_eq fun p ↦ by rcases p with ⟨k, s | g⟩ <;> rfl

private theorem list_all_eq_foldr {β : Type*} (f : β → Bool) (l : List β) :
    l.all f = l.foldr (fun b r ↦ f b && r) true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.all_cons, ih]

/-- The all-letters-have-index condition of the relation branch is primitive
recursive. -/
theorem primrec₂_all_isTermLetterAt :
    Primrec₂ fun (k : ℕ) (s : List (FormulaSymbol L α)) ↦ s.all (isTermLetterAt k) := by
  have h : Primrec fun p : ℕ × List (FormulaSymbol L α) ↦
      p.2.foldr (fun b r ↦ isTermLetterAt p.1 b && r) true :=
    Primrec.list_foldr Primrec.snd (Primrec.const true)
      ((Primrec.and.comp
        (primrec₂_isTermLetterAt.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂)
  exact h.of_eq fun p ↦ (list_all_eq_foldr _ _).symm

private theorem primrec₂_stepFalsum : Primrec₂ (stepFalsum (L := L) (α := α)) := by
  have hget : Primrec fun q : List (List (ℕ × List (FormulaSymbol L α))) × ℕ ↦
      q.1[q.1.length - 1]? :=
    Primrec.list_getElem?.comp Primrec.fst
      (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 1))
  exact (Primrec.option_map hget
    ((Primrec.list_cons.comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst)
        (Primrec.list_cons.comp
          (Primrec.sumInr.comp (Primrec.sumInr.comp
            (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 2))))
          (Primrec.const [])))
      Primrec.snd).to₂)).of_eq fun q ↦ rfl

private theorem primrec_stepEqual :
    Primrec fun q : List (List (ℕ × List (FormulaSymbol L α))) ×
        (Σ k, L.Term (α ⊕ Fin k)) × (Σ k, L.Term (α ⊕ Fin k)) ↦
      stepEqual q.1 q.2.1 q.2.2 := by
  have hget : Primrec fun q : List (List (ℕ × List (FormulaSymbol L α))) ×
      (Σ k, L.Term (α ⊕ Fin k)) × (Σ k, L.Term (α ⊕ Fin k)) ↦ q.1[q.1.length - 2]? :=
    Primrec.list_getElem?.comp Primrec.fst
      (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 2))
  have hval : Primrec fun q : List (List (ℕ × List (FormulaSymbol L α))) ×
      (Σ k, L.Term (α ⊕ Fin k)) × (Σ k, L.Term (α ⊕ Fin k)) ↦
      if q.2.1.1 = q.2.2.1 then (q.2.1.1, [Sum.inl q.2.1, Sum.inl q.2.2])
      else sigmaRepr (L := L) (α := α) default :=
    Primrec.ite
      (Primrec.eq.comp
        ((Term.primrec_sigmaTerm_fst L α).comp (Primrec.fst.comp Primrec.snd))
        ((Term.primrec_sigmaTerm_fst L α).comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.pair ((Term.primrec_sigmaTerm_fst L α).comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_cons.comp (Primrec.sumInl.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.list_cons.comp (Primrec.sumInl.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.const []))))
      (Primrec.const _)
  exact (Primrec.option_map hget
    ((Primrec.list_cons.comp (hval.comp Primrec.fst) Primrec.snd).to₂)).of_eq fun q ↦ rfl

private theorem primrec_stepRel :
    Primrec fun q : List (List (ℕ × List (FormulaSymbol L α))) ×
        (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L α) ↦
      stepRel q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hr1 : Primrec fun q : List (List (ℕ × List (FormulaSymbol L α))) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L α) ↦ q.2.1.1 :=
    (primrec_relationSymbol_arity (L := L)).comp (Primrec.fst.comp Primrec.snd)
  have hk : Primrec fun q : List (List (ℕ × List (FormulaSymbol L α))) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L α) ↦ q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hs' : Primrec fun q : List (List (ℕ × List (FormulaSymbol L α))) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L α) ↦ q.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have htake : Primrec fun q : List (List (ℕ × List (FormulaSymbol L α))) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L α) ↦ q.2.2.2.take q.2.1.1 :=
    Primrec.list_take.comp hr1 hs'
  have hget : Primrec fun q : List (List (ℕ × List (FormulaSymbol L α))) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L α) ↦
      q.1[q.1.length - 2 - q.2.1.1]? :=
    Primrec.list_getElem?.comp Primrec.fst
      (Primrec.nat_sub.comp
        (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 2))
        hr1)
  have hval : Primrec fun q : List (List (ℕ × List (FormulaSymbol L α))) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L α) ↦
      if (q.2.2.2.take q.2.1.1).length = q.2.1.1 ∧
          (q.2.2.2.take q.2.1.1).all (isTermLetterAt q.2.2.1) then
        (q.2.2.1, Sum.inr (Sum.inl q.2.1) :: Sum.inr (Sum.inr q.2.2.1) ::
          q.2.2.2.take q.2.1.1)
      else sigmaRepr (L := L) (α := α) default :=
    Primrec.ite
      (PrimrecPred.and (Primrec.eq.comp (Primrec.list_length.comp htake) hr1)
        (Primrec.eq.comp (primrec₂_all_isTermLetterAt.comp hk htake) (Primrec.const true)))
      (Primrec.pair hk
        (Primrec.list_cons.comp
          (Primrec.sumInr.comp (Primrec.sumInl.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.list_cons.comp (Primrec.sumInr.comp (Primrec.sumInr.comp hk)) htake)))
      (Primrec.const _)
  exact (Primrec.option_map hget
    ((Primrec.list_cons.comp (hval.comp Primrec.fst) Primrec.snd).to₂)).of_eq fun q ↦ rfl

private theorem primrec_getElemBang (i : ℕ) :
    Primrec fun D : List (ℕ × List (FormulaSymbol L α)) ↦ D[i]! :=
  (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id (Primrec.const i))
    (Primrec.const default)).of_eq fun _ ↦ List.getElem!_eq_getElem?_getD.symm

private theorem primrec_stepImp : Primrec (stepImp (L := L) (α := α)) := by
  have hget : Primrec fun prev : List (List (ℕ × List (FormulaSymbol L α))) ↦
      prev[prev.length - 1]? :=
    Primrec.list_getElem?.comp Primrec.id
      (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1))
  have hbody : Primrec fun D : List (ℕ × List (FormulaSymbol L α)) ↦
      if 2 ≤ D.length then imprepr D[0]! D[1]! :: D.drop 2 else [] :=
    Primrec.ite (Primrec.nat_le.comp (Primrec.const 2) Primrec.list_length)
      (Primrec.list_cons.comp
        (primrec₂_imprepr.comp (primrec_getElemBang 0) (primrec_getElemBang 1))
        (Primrec.list_drop.comp (Primrec.const 2) Primrec.id))
      (Primrec.const [])
  exact (Primrec.option_map hget ((hbody.comp Primrec.snd).to₂)).of_eq fun prev ↦ rfl

private theorem primrec_stepAll : Primrec (stepAll (L := L) (α := α)) := by
  have hget : Primrec fun prev : List (List (ℕ × List (FormulaSymbol L α))) ↦
      prev[prev.length - 1]? :=
    Primrec.list_getElem?.comp Primrec.id
      (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1))
  have hbody : Primrec fun D : List (ℕ × List (FormulaSymbol L α)) ↦
      if 1 ≤ D.length then allrepr D[0]! :: D.drop 1 else [] :=
    Primrec.ite (Primrec.nat_le.comp (Primrec.const 1) Primrec.list_length)
      (Primrec.list_cons.comp (primrec_allrepr.comp (primrec_getElemBang 0))
        (Primrec.list_drop.comp (Primrec.const 1) Primrec.id))
      (Primrec.const [])
  exact (Primrec.option_map hget ((hbody.comp Primrec.snd).to₂)).of_eq fun prev ↦ rfl

private theorem primrec₂_decodeStackStepAux :
    Primrec₂ (decodeStackStepAux (L := L) (α := α)) := by
  have hEqCase : Primrec fun q : List (List (ℕ × List (FormulaSymbol L α))) ×
      List (FormulaSymbol L α) × (Σ k, L.Term (α ⊕ Fin k)) ↦
      List.casesOn (motive := fun _ ↦ Option (List (ℕ × List (FormulaSymbol L α)))) q.2.1
        (some [])
        fun c₂ _ ↦ Sum.casesOn c₂ (fun s₂ ↦ stepEqual q.1 q.2.2 s₂) fun _ ↦ some [] :=
    Primrec.list_casesOn (Primrec.fst.comp Primrec.snd) (Primrec.const _)
      ((Primrec.sumCasesOn (Primrec.fst.comp Primrec.snd)
        ((primrec_stepEqual.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
            Primrec.snd))).to₂)
        ((Primrec.const (some [])).to₂)).to₂)
  have hRelCase : Primrec fun q : List (List (ℕ × List (FormulaSymbol L α))) ×
      List (FormulaSymbol L α) × (Σ n, L.Relations n) ↦
      List.casesOn (motive := fun _ ↦ Option (List (ℕ × List (FormulaSymbol L α)))) q.2.1
        (some [])
        fun c₂ s' ↦ Sum.casesOn c₂ (fun _ ↦ some [])
          fun g₂ ↦ Sum.casesOn g₂ (fun _ ↦ some []) fun k ↦ stepRel q.1 q.2.2 k s' :=
    Primrec.list_casesOn (Primrec.fst.comp Primrec.snd) (Primrec.const _)
      ((Primrec.sumCasesOn (Primrec.fst.comp Primrec.snd)
        ((Primrec.const (some [])).to₂)
        ((Primrec.sumCasesOn Primrec.snd
          ((Primrec.const (some [])).to₂)
          ((primrec_stepRel.comp (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            (Primrec.pair
              (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
              (Primrec.pair Primrec.snd
                (Primrec.snd.comp (Primrec.snd.comp
                  (Primrec.fst.comp Primrec.fst))))))).to₂)).to₂)).to₂)
  have hNatCase : Primrec fun q : List (List (ℕ × List (FormulaSymbol L α))) × ℕ ↦
      Nat.casesOn (motive := fun _ ↦ Option (List (ℕ × List (FormulaSymbol L α)))) q.2
        (stepImp q.1)
        fun j' ↦ Nat.casesOn j' (stepAll q.1) fun n ↦ stepFalsum q.1 n :=
    Primrec.nat_casesOn Primrec.snd (primrec_stepImp.comp Primrec.fst)
      ((Primrec.nat_casesOn Primrec.snd
        (primrec_stepAll.comp (Primrec.fst.comp Primrec.fst))
        ((primrec₂_stepFalsum.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂)).to₂)
  have hmain : Primrec fun p : List (FormulaSymbol L α) ×
      List (List (ℕ × List (FormulaSymbol L α))) ↦
      if p.2.length ≤ p.1.length then
        List.casesOn (motive := fun _ ↦ Option (List (ℕ × List (FormulaSymbol L α))))
          (List.drop (p.1.length - p.2.length) p.1)
          (some [])
          (fun c tail ↦
            Sum.casesOn c
              (fun s₁ ↦ List.casesOn tail (some [])
                fun c₂ _ ↦ Sum.casesOn c₂ (fun s₂ ↦ stepEqual p.2 s₁ s₂)
                  fun _ ↦ some [])
              fun g ↦ Sum.casesOn g
                (fun r ↦ List.casesOn tail (some [])
                  fun c₂ s' ↦ Sum.casesOn c₂ (fun _ ↦ some [])
                    fun g₂ ↦ Sum.casesOn g₂ (fun _ ↦ some []) fun k ↦ stepRel p.2 r k s')
                fun j ↦ Nat.casesOn j (stepImp p.2)
                  fun j' ↦ Nat.casesOn j' (stepAll p.2) fun n ↦ stepFalsum p.2 n)
      else some [] := by
    have hdrop : Primrec fun p : List (FormulaSymbol L α) ×
        List (List (ℕ × List (FormulaSymbol L α))) ↦
        List.drop (p.1.length - p.2.length) p.1 :=
      Primrec.list_drop.comp
        (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.fst)
          (Primrec.list_length.comp Primrec.snd)) Primrec.fst
    have hbr := (Primrec.sumCasesOn
      (Primrec.fst.comp Primrec.snd :
        Primrec fun x : (List (FormulaSymbol L α) ×
            List (List (ℕ × List (FormulaSymbol L α)))) ×
            FormulaSymbol L α × List (FormulaSymbol L α) ↦ x.2.1)
      ((hEqCase.comp (Primrec.pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd))).to₂)
      ((Primrec.sumCasesOn Primrec.snd
        ((hRelCase.comp (Primrec.pair
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
            Primrec.snd))).to₂)
        ((hNatCase.comp (Primrec.pair
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          Primrec.snd)).to₂)).to₂)).to₂
    exact Primrec.ite
      (Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.list_length.comp Primrec.fst))
      (Primrec.list_casesOn hdrop (Primrec.const _) hbr)
      (Primrec.const _)
  exact hmain.of_eq fun p ↦ (decodeStackStepAux_eq_cases p.1 p.2).symm

/-- The guarded suffix evaluation of the formula stack machine is primitive recursive,
by course-of-values recursion on the suffix length. -/
theorem primrec₂_decodeStackAux : Primrec₂ (decodeStackAux (L := L) (α := α)) :=
  Primrec.nat_strong_rec _ primrec₂_decodeStackStepAux decodeStackStepAux_spec

/-- The formula stack machine is primitive recursive: the heart of the `Primcodable`
instance for formulas. -/
theorem primrec_decodeStack : Primrec (decodeStack (L := L) (α := α)) :=
  (primrec₂_decodeStackAux.comp Primrec.id Primrec.list_length).of_eq
    decodeStackAux_length

end PrimrecStep

end BoundedFormula

end FirstOrder.Language
