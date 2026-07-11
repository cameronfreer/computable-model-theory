/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.AtomicSatisfaction

/-!
# Computable quantifier-free satisfaction

The remainder of roadmap PR 7: in an ω-presented computable structure, satisfaction of
quantifier-free formulas is a computable predicate. The satisfaction stack machine
`satStack` runs over `listEncode` symbol lists in parallel with mathlib's
`BoundedFormula.listDecode`, carrying for each decoded entry a payload of its sigma
index, its quantifier-freeness flag, and its satisfaction flag. Equality and relation
leaves are decided through term evaluation and the structure's relation decider,
implications combine the flags of their subformulas Booleanly, and every
mismatched-index `default` and every quantifier receives the satisfaction flag `false`.

The bridge `satStack_eq_map_listDecode` identifies the machine with the noncomputable
specification payload `flagOf` mapped over `listDecode`, mirroring
`decodeStack_eq_map_listEncode`; the head corollary `qfSatBool_iff` shows the machine
decides quantifier-freeness together with satisfaction on formulas.
-/

open Encodable FirstOrder Language Language.BoundedFormula

namespace FirstOrder.Language

variable {L : Language} [L.EffectiveLanguage] [L.Structure ℕ] {k : ℕ}

section QFSatisfaction

omit [L.EffectiveLanguage] in
private theorem realize_relabelElim (t : L.Term (Fin k ⊕ Fin 0)) (v : Fin k → ℕ)
    (xs : Fin 0 → ℕ) :
    (t.relabel (Sum.elim id Fin.elim0)).realize v = t.realize (Sum.elim v xs) := by
  rw [Term.realize_relabel]
  congr 1
  funext x
  rcases x with x | x
  · rfl
  · exact x.elim0

/-- The equality-leaf satisfaction flag: both letters must be bound-zero terms, decided
by evaluating and comparing. -/
def eqFlag (v : Fin k → ℕ) (c₁ c₂ : FormulaSymbol L (Fin k)) : Bool :=
  match termOfSymbol? c₁, termOfSymbol? c₂ with
  | some t₁, some t₂ => decide (t₁.realize v = t₂.realize v)
  | _, _ => false

/-- The relation-leaf satisfaction flag: the recorded bound must be zero and the
argument letters must be bound-zero terms of the relation's arity, packaged as uniform
relation application data and decided by the structure. -/
def relFlag [DecidablePred (RelationApplicationData.relMap (L := L) (M := ℕ))]
    (v : Fin k → ℕ) (r : L.RelationSymbol) (b : ℕ)
    (letters : List (FormulaSymbol L (Fin k))) : Bool :=
  if b = 0 then
    Option.casesOn (motive := fun _ ↦ Bool)
      (RelationApplicationData.ofSymbolArgs?
        (r, (letters.filterMap termOfSymbol?).map fun t ↦ t.realize v)) false
      fun d ↦ decide d.relMap
  else false

/-- The flag-payload shadow of `sigmaImp`. -/
def impFlag (p q : ℕ × Bool × Bool) : ℕ × Bool × Bool :=
  if p.1 = q.1 then
    (p.1, p.2.1 && q.2.1,
      if p.1 = 0 then (p.2.1 && q.2.1) && (!p.2.2 || q.2.2) else false)
  else (0, true, false)

/-- The flag-payload shadow of `sigmaAll`. -/
def allFlag (p : ℕ × Bool × Bool) : ℕ × Bool × Bool :=
  match p.1 with
  | n + 1 => (n, false, false)
  | 0 => (0, true, false)

/-- The satisfaction stack machine: `BoundedFormula.listDecode` with each decoded
formula represented by its index, its quantifier-freeness flag, and its satisfaction
flag. Mirrors the six cases of the decoder, including its `default` results on
mismatched indices, which receive the payload `(0, true, false)` of the default
`⟨0, falsum⟩`. -/
def satStack [DecidablePred (RelationApplicationData.relMap (L := L) (M := ℕ))]
    (v : Fin k → ℕ) : List (FormulaSymbol L (Fin k)) → List (ℕ × Bool × Bool)
  | Sum.inr (Sum.inr (n + 2)) :: l => (n, true, false) :: satStack v l
  | Sum.inl ⟨n₁, t₁⟩ :: Sum.inl ⟨n₂, t₂⟩ :: l =>
    (if n₁ = n₂ then
       (n₁, true, eqFlag v (Sum.inl ⟨n₁, t₁⟩) (Sum.inl ⟨n₂, t₂⟩))
     else (0, true, false)) :: satStack v l
  | Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr b) :: l =>
    (if h : ∀ i : Fin n, (l.map Sum.getLeft?)[i]?.join.isSome then
       if ∀ i, (Option.get _ (h i)).1 = b then (b, true, relFlag v ⟨n, R⟩ b (l.take n))
       else (0, true, false)
     else (0, true, false)) :: satStack v (l.drop n)
  | Sum.inr (Sum.inr 0) :: l =>
    if h : 2 ≤ (satStack v l).length then
      impFlag ((satStack v l)[0]'(by omega)) ((satStack v l)[1]'(by omega)) ::
        (satStack v l).drop 2
    else []
  | Sum.inr (Sum.inr 1) :: l =>
    if h : 1 ≤ (satStack v l).length then
      allFlag ((satStack v l)[0]'(by omega)) :: (satStack v l).drop 1
    else []
  | _ => []
  termination_by l => l.length

omit [L.EffectiveLanguage] in
open Classical in
/-- The specification payload of one decoded entry: its sigma index, its
quantifier-freeness flag, and its satisfaction flag — `true` exactly when the entry is
a bound-zero quantifier-free formula realized under `v`. Noncomputable specification
only; the machine `satStack` computes it. -/
noncomputable def flagOf (v : Fin k → ℕ) :
    (Σ n, L.BoundedFormula (Fin k) n) → ℕ × Bool × Bool
  | ⟨0, ψ⟩ => (0, isQFBool ψ, decide (ψ.IsQF ∧ Formula.Realize ψ v))
  | ⟨n + 1, ψ⟩ => (n + 1, isQFBool ψ, false)

omit [L.EffectiveLanguage] in
theorem flagOf_fst (v : Fin k → ℕ) (s : Σ n, L.BoundedFormula (Fin k) n) :
    (flagOf v s).1 = s.1 := by
  rcases s with ⟨(- | n), ψ⟩ <;> rfl

omit [L.EffectiveLanguage] in
open Classical in
theorem flagOf_default (v : Fin k → ℕ) :
    flagOf v (default : Σ n, L.BoundedFormula (Fin k) n) = (0, true, false) := by
  show flagOf v ⟨0, falsum⟩ = (0, true, false)
  rw [flagOf]
  refine congrArg (fun b ↦ ((0 : ℕ), true, b)) (decide_eq_false fun h ↦ ?_)
  exact h.2

omit [L.EffectiveLanguage] in
theorem flagOf_falsum (v : Fin k → ℕ) (n : ℕ) :
    flagOf v (⟨n, falsum⟩ : Σ n, L.BoundedFormula (Fin k) n) = (n, true, false) := by
  cases n with
  | zero => exact flagOf_default v
  | succ n => rfl

omit [L.EffectiveLanguage] in
open Classical in
theorem flagOf_imp (v : Fin k → ℕ) (p q : Σ n, L.BoundedFormula (Fin k) n) :
    flagOf v (sigmaImp p q) = impFlag (flagOf v p) (flagOf v q) := by
  rcases p with ⟨m, φ⟩
  rcases q with ⟨n, ψ⟩
  by_cases h : m = n
  · subst h
    rw [sigmaImp_apply, impFlag, if_pos (by rw [flagOf_fst, flagOf_fst])]
    have hq : (φ.imp ψ).IsQF ↔ φ.IsQF ∧ ψ.IsQF := by
      rw [← isQFBool_iff, ← isQFBool_iff, ← isQFBool_iff,
        show isQFBool (φ.imp ψ) = (isQFBool φ && isQFBool ψ) from rfl, Bool.and_eq_true]
    cases m with
    | zero =>
      rw [flagOf, flagOf, flagOf]
      refine congrArg (fun r ↦ ((0 : ℕ), isQFBool φ && isQFBool ψ, r)) ?_
      rw [if_pos (by trivial)]
      have hr : Formula.Realize (φ.imp ψ) v ↔
          (Formula.Realize φ v → Formula.Realize ψ v) := by
        rw [Formula.Realize, Formula.Realize, Formula.Realize]
        exact realize_imp
      refine Bool.eq_iff_iff.2 ?_
      simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, isQFBool_iff, hq, hr]
      constructor
      · rintro ⟨⟨h₁, h₂⟩, h₃⟩
        refine ⟨⟨h₁, h₂⟩, ?_⟩
        by_cases hφ : Formula.Realize φ v
        · exact Or.inr ⟨h₂, h₃ hφ⟩
        · exact Or.inl fun hc ↦ hφ hc.2
      · rintro ⟨⟨h₁, h₂⟩, h₃ | h₃⟩
        · exact ⟨⟨h₁, h₂⟩, fun hφ ↦ absurd ⟨h₁, hφ⟩ h₃⟩
        · exact ⟨⟨h₁, h₂⟩, fun _ ↦ h₃.2⟩
    | succ m =>
      rw [flagOf, flagOf, flagOf]
      rw [if_neg (Nat.succ_ne_zero m)]
      rfl
  · rw [sigmaImp, dif_neg h, impFlag, if_neg (by rw [flagOf_fst, flagOf_fst]; exact h),
      flagOf_default]

omit [L.EffectiveLanguage] in
open Classical in
theorem flagOf_all (v : Fin k → ℕ) (p : Σ n, L.BoundedFormula (Fin k) n) :
    flagOf v (sigmaAll p) = allFlag (flagOf v p) := by
  rcases p with ⟨(- | m), ψ⟩
  · rw [show sigmaAll (⟨0, ψ⟩ : Σ n, L.BoundedFormula (Fin k) n) = default from rfl,
      flagOf_default]
    rfl
  · rw [sigmaAll_apply]
    cases m with
    | zero =>
      show flagOf v ⟨0, ψ.all⟩ = ((0 : ℕ), false, false)
      rw [flagOf]
      refine congrArg (fun r ↦ ((0 : ℕ), false, r)) (decide_eq_false fun h ↦ ?_)
      have := (isQFBool_iff (φ := ψ.all)).2 h.1
      simp [isQFBool] at this
    | succ m =>
      show flagOf v ⟨m + 1, ψ.all⟩ = ((m + 1 : ℕ), false, false)
      rfl

private theorem filterMap_eq_map_of_forall_some {β γ : Type*} {f : β → Option γ}
    {g : β → γ} : ∀ l : List β, (∀ x ∈ l, f x = some (g x)) → l.filterMap f = l.map g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons, h x (by simp), List.map_cons,
      filterMap_eq_map_of_forall_some l fun y hy ↦ h y (List.mem_cons_of_mem x hy)]

omit [L.EffectiveLanguage] in
private theorem eqFlag_zero (v : Fin k → ℕ) (t₁ t₂ : L.Term (Fin k ⊕ Fin 0)) :
    eqFlag v (Sum.inl ⟨0, t₁⟩) (Sum.inl ⟨0, t₂⟩) =
      decide ((t₁.relabel (Sum.elim id Fin.elim0)).realize v =
        (t₂.relabel (Sum.elim id Fin.elim0)).realize v) :=
  rfl

omit [L.EffectiveLanguage] in
open Classical in
private theorem relFlag_zero
    [DecidablePred (RelationApplicationData.relMap (L := L) (M := ℕ))]
    (v : Fin k → ℕ) {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term (Fin k ⊕ Fin 0)) :
    relFlag v ⟨n, R⟩ 0 ((List.finRange n).map fun i ↦
        (Sum.inl ⟨0, ts i⟩ : FormulaSymbol L (Fin k))) =
      decide ((BoundedFormula.rel (α := Fin k) R ts).IsQF ∧
        Formula.Realize (BoundedFormula.rel (α := Fin k) R ts) v) := by
  have hfm : List.filterMap termOfSymbol? ((List.finRange n).map fun i ↦
      (Sum.inl ⟨0, ts i⟩ : FormulaSymbol L (Fin k))) =
      (List.finRange n).map fun i ↦ (ts i).relabel (Sum.elim id Fin.elim0) := by
    rw [List.filterMap_map]
    exact filterMap_eq_map_of_forall_some _ fun i _ ↦ termOfSymbol?_inl (ts i)
  rw [relFlag, if_pos rfl, hfm,
    RelationApplicationData.ofSymbolArgs?_of_length_eq _ (by simp [RelationSymbol.arity])]
  show decide _ = _
  refine Bool.eq_iff_iff.2 ?_
  simp only [decide_eq_true_eq]
  rw [RelationApplicationData.relMap_equivSubtype_symm]
  constructor
  · intro hX
    refine ⟨(IsAtomic.rel R ts).isQF, ?_⟩
    rw [Formula.Realize]
    refine BoundedFormula.realize_rel.2 ?_
    convert hX using 2
    rw [List.get_eq_getElem, List.getElem_map, List.getElem_map, List.getElem_finRange]
    exact (realize_relabelElim _ v _).symm
  · rintro ⟨-, hreal⟩
    rw [Formula.Realize] at hreal
    have hX := BoundedFormula.realize_rel.1 hreal
    convert hX using 2
    rw [List.get_eq_getElem, List.getElem_map, List.getElem_map, List.getElem_finRange]
    exact realize_relabelElim _ v _

omit [L.EffectiveLanguage] in
open Classical in
/-- The machine computes the specification payloads of `listDecode`: the exact bridge
between the satisfaction stack and mathlib's decoder, preserving the `default`
behavior on all mismatched-index branches. Mirrors `decodeStack_eq_map_listEncode`. -/
theorem satStack_eq_map_listDecode
    [DecidablePred (RelationApplicationData.relMap (L := L) (M := ℕ))]
    (v : Fin k → ℕ) (l : List (FormulaSymbol L (Fin k))) :
    satStack v l = (listDecode l).map (flagOf v) := by
  induction hl : l.length using Nat.strong_induction_on generalizing l with
  | _ len ih =>
  subst hl
  match l with
  | [] => simp [satStack, listDecode]
  | Sum.inr (Sum.inr (n + 2)) :: l =>
    rw [satStack, listDecode, List.map_cons, ih l.length (by simp) l rfl, flagOf_falsum]
  | [Sum.inl ⟨n₁, t₁⟩] => simp [satStack, listDecode]
  | Sum.inl ⟨n₁, t₁⟩ :: Sum.inl ⟨n₂, t₂⟩ :: l =>
    rw [satStack, listDecode, List.map_cons, ih l.length (by simp) l rfl]
    congr 1
    by_cases h : n₁ = n₂
    · subst h
      rw [if_pos rfl, dif_pos rfl]
      cases n₁ with
      | zero =>
        show ((0 : ℕ), true, eqFlag v (Sum.inl ⟨0, t₁⟩) (Sum.inl ⟨0, t₂⟩)) =
          flagOf v ⟨0, equal t₁ t₂⟩
        rw [eqFlag_zero, flagOf]
        refine congrArg (fun r ↦ ((0 : ℕ), true, r)) ?_
        refine Bool.eq_iff_iff.2 ?_
        rw [decide_eq_true_eq, decide_eq_true_eq,
          and_iff_right (show (equal t₁ t₂ : L.BoundedFormula (Fin k) 0).IsQF from
            (IsAtomic.equal t₁ t₂).isQF)]
        constructor
        · intro heq
          rw [Formula.Realize]
          refine (realize_bdEqual t₁ t₂).2 ?_
          rw [← realize_relabelElim t₁ v, ← realize_relabelElim t₂ v]
          exact heq
        · intro hreal
          rw [Formula.Realize] at hreal
          have h2 := (realize_bdEqual t₁ t₂).1 hreal
          rw [← realize_relabelElim t₁ v, ← realize_relabelElim t₂ v] at h2
          exact h2
      | succ m => rfl
    · rw [if_neg h, dif_neg h, flagOf_default]
  | Sum.inl ⟨n₁, t₁⟩ :: Sum.inr g :: l =>
    simp [satStack, listDecode]
  | Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr b) :: l =>
    rw [satStack, listDecode, List.map_cons, ih (l.drop n).length
      (by simp; omega) (l.drop n) rfl]
    congr 1
    by_cases h : ∀ i : Fin n, (l.map Sum.getLeft?)[i]?.join.isSome
    · rw [dif_pos h, dif_pos h]
      by_cases h' : ∀ i, (Option.get _ (h i)).1 = b
      · rw [if_pos h', dif_pos h']
        cases b with
        | succ m => rfl
        | zero =>
          have key : ∀ i : Fin n, (i : ℕ) < l.length := by
            intro i
            have h0 := h i
            rcases ho : (List.map Sum.getLeft? l)[i]? with - | w
            · rw [ho] at h0
              simp at h0
            · have ho' : (List.map Sum.getLeft? l)[(i : ℕ)]? = some w := ho
              have := (List.getElem?_eq_some_iff.1 ho').1
              simpa using this
          have htake : l.take n = (List.finRange n).map fun i : Fin n ↦
              (Sum.inl ⟨0, Eq.mp (by rw [h' i]) (Option.get _ (h i)).2⟩ :
                FormulaSymbol L (Fin k)) := by
            have hlen : n ≤ l.length := by
              by_contra hc
              exact absurd (key ⟨l.length, by omega⟩) (by simp)
            have htk : l.take n = (List.finRange n).map fun j : Fin n ↦
                l[(j : ℕ)]'(key j) := by
              refine List.ext_getElem ?_ fun i hi₁ hi₂ ↦ ?_
              · simp [hlen]
              · simp [List.getElem_take]
            rw [htk]
            refine List.map_congr_left fun j hj ↦ ?_
            rcases hli : l[(j : ℕ)]'(key j) with s | g
            · have hgl : (List.map Sum.getLeft? l)[(j : ℕ)]?.join = some s := by
                simp [List.getElem?_eq_getElem (by simpa using key j :
                  (j : ℕ) < (List.map Sum.getLeft? l).length), hli]
              have hw : Option.get _ (h j) = s := by
                apply Option.get_of_mem
                exact Option.mem_def.2 hgl
              have hfst : s.fst = 0 := by
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
          rw [htake, relFlag_zero, flagOf]
          rfl
      · rw [if_neg h', dif_neg h', flagOf_default]
    · rw [dif_neg h, dif_neg h, flagOf_default]
  | Sum.inr (Sum.inl ⟨n, R⟩) :: ([] : List (FormulaSymbol L (Fin k))) =>
    simp [satStack, listDecode]
  | Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inl x :: l =>
    simp [satStack, listDecode]
  | Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inl y) :: l =>
    simp [satStack, listDecode]
  | Sum.inr (Sum.inr 0) :: l =>
    have hd := ih l.length (by simp) l rfl
    rw [satStack, listDecode]
    simp only [hd, List.length_map, List.getElem_map]
    by_cases h : 2 ≤ (listDecode (L := L) (α := Fin k) l).length
    · rw [dif_pos h, dif_pos h, List.map_cons, ← List.map_drop, flagOf_imp]
      rfl
    · rw [dif_neg h, dif_neg h]
      rfl
  | Sum.inr (Sum.inr 1) :: l =>
    have hd := ih l.length (by simp) l rfl
    rw [satStack, listDecode]
    simp only [hd, List.length_map, List.getElem_map]
    by_cases h : 1 ≤ (listDecode (L := L) (α := Fin k) l).length
    · rw [dif_pos h, dif_pos h, List.map_cons, ← List.map_drop, flagOf_all]
      rfl
    · rw [dif_neg h, dif_neg h]
      rfl

/-- The quantifier-free satisfaction decider: the satisfaction flag at the head of the
machine run on the formula's symbol list. -/
def qfSatBool [DecidablePred (RelationApplicationData.relMap (L := L) (M := ℕ))]
    (p : L.Formula (Fin k) × (Fin k → ℕ)) : Bool :=
  (((satStack p.2 ((p.1 : L.BoundedFormula (Fin k) 0).listEncode)).head?).map
    fun q ↦ q.2.2).getD false

omit [L.EffectiveLanguage] in
open Classical in
/-- The decider decides quantifier-freeness together with satisfaction. -/
theorem qfSatBool_iff [DecidablePred (RelationApplicationData.relMap (L := L) (M := ℕ))]
    (p : L.Formula (Fin k) × (Fin k → ℕ)) :
    qfSatBool p = true ↔ (p.1 : L.BoundedFormula (Fin k) 0).IsQF ∧ p.1.Realize p.2 := by
  have hdec : listDecode ((p.1 : L.BoundedFormula (Fin k) 0).listEncode) =
      [⟨0, p.1⟩] := by
    have h := listDecode_encode_list (L := L) (α := Fin k) [⟨0, p.1⟩]
    rwa [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
  rw [qfSatBool, satStack_eq_map_listDecode, hdec, List.map_cons, List.map_nil]
  show ((flagOf p.2 ⟨0, p.1⟩).2.2 = true) ↔ _
  rw [flagOf]
  exact decide_eq_true_iff

/-! ### The guarded suffix machine

Course-of-values recursion on the suffix length, mirroring the `decodeStackAux`
machinery: `satStackAux x m` evaluates the machine on the length-`m` suffix (and
returns `[]` out of range), and `satStackStepAux` computes one step from the table of
all shorter-suffix values. -/

variable [DecidablePred (RelationApplicationData.relMap (L := L) (M := ℕ))]

/-- The length-guarded suffix evaluation of the satisfaction stack machine. -/
def satStackAux (x : (Fin k → ℕ) × List (FormulaSymbol L (Fin k))) (m : ℕ) :
    List (ℕ × Bool × Bool) :=
  if m ≤ x.2.length then satStack x.1 (x.2.drop (x.2.length - m)) else []

omit [L.EffectiveLanguage] in
/-- At the full length, the guarded suffix evaluation is the machine itself. -/
theorem satStackAux_length (x : (Fin k → ℕ) × List (FormulaSymbol L (Fin k))) :
    satStackAux x x.2.length = satStack x.1 x.2 := by
  rw [satStackAux, if_pos le_rfl]
  simp

omit [L.EffectiveLanguage] in
/-- In range, the guarded suffix evaluation is the machine on the suffix. -/
theorem satStackAux_of_le {x : (Fin k → ℕ) × List (FormulaSymbol L (Fin k))} {m : ℕ}
    (hm : m ≤ x.2.length) :
    satStackAux x m = satStack x.1 (x.2.drop (x.2.length - m)) := by
  rw [satStackAux, if_pos hm]

/-- The falsum branch of the step function. -/
private def stepFalsumSat (prev : List (List (ℕ × Bool × Bool))) (n : ℕ) :
    Option (List (ℕ × Bool × Bool)) :=
  (prev[prev.length - 1]?).map fun rest ↦ (n, true, false) :: rest

/-- The equality branch of the step function. -/
private def stepEqualSat (v : Fin k → ℕ) (prev : List (List (ℕ × Bool × Bool)))
    (s₁ s₂ : Σ m, L.Term (Fin k ⊕ Fin m)) : Option (List (ℕ × Bool × Bool)) :=
  (prev[prev.length - 2]?).map fun rest ↦
    (if s₁.1 = s₂.1 then (s₁.1, true, eqFlag v (Sum.inl s₁) (Sum.inl s₂))
     else (0, true, false)) :: rest

/-- The relation branch of the step function. -/
private def stepRelSat (v : Fin k → ℕ) (prev : List (List (ℕ × Bool × Bool)))
    (r : Σ n, L.Relations n) (b : ℕ) (s' : List (FormulaSymbol L (Fin k))) :
    Option (List (ℕ × Bool × Bool)) :=
  (prev[prev.length - 2 - r.1]?).map fun rest ↦
    (if (s'.take r.1).length = r.1 ∧ (s'.take r.1).all (isTermLetterAt b) then
      (b, true, relFlag v r b (s'.take r.1))
     else (0, true, false)) :: rest

/-- The implication branch of the step function. -/
private def stepImpSat (prev : List (List (ℕ × Bool × Bool))) :
    Option (List (ℕ × Bool × Bool)) :=
  (prev[prev.length - 1]?).map fun D ↦
    if 2 ≤ D.length then impFlag D[0]! D[1]! :: D.drop 2 else []

/-- The quantifier branch of the step function. -/
private def stepAllSat (prev : List (List (ℕ × Bool × Bool))) :
    Option (List (ℕ × Bool × Bool)) :=
  (prev[prev.length - 1]?).map fun D ↦
    if 1 ≤ D.length then allFlag D[0]! :: D.drop 1 else []

/-- One backward step of the guarded machine, reading previous values: the
course-of-values candidate for `ComputableIn.nat_strong_rec`. `prev` holds
`satStackAux x j` for `j < prev.length`. -/
private def satStackStepAux (x : (Fin k → ℕ) × List (FormulaSymbol L (Fin k)))
    (prev : List (List (ℕ × Bool × Bool))) : Option (List (ℕ × Bool × Bool)) :=
  let m := prev.length
  if m ≤ x.2.length then
    match x.2.drop (x.2.length - m) with
    | [] => some []
    | Sum.inr (Sum.inr (n + 2)) :: _ =>
      (prev[m - 1]?).map fun rest ↦ (n, true, false) :: rest
    | Sum.inl s₁ :: Sum.inl s₂ :: _ =>
      (prev[m - 2]?).map fun rest ↦
        (if s₁.1 = s₂.1 then (s₁.1, true, eqFlag x.1 (Sum.inl s₁) (Sum.inl s₂))
         else (0, true, false)) :: rest
    | Sum.inr (Sum.inl r) :: Sum.inr (Sum.inr b) :: s' =>
      (prev[m - 2 - r.1]?).map fun rest ↦
        (if (s'.take r.1).length = r.1 ∧ (s'.take r.1).all (isTermLetterAt b) then
          (b, true, relFlag x.1 r b (s'.take r.1))
         else (0, true, false)) :: rest
    | Sum.inr (Sum.inr 0) :: _ =>
      (prev[m - 1]?).map fun D ↦
        if 2 ≤ D.length then impFlag D[0]! D[1]! :: D.drop 2 else []
    | Sum.inr (Sum.inr 1) :: _ =>
      (prev[m - 1]?).map fun D ↦
        if 1 ≤ D.length then allFlag D[0]! :: D.drop 1 else []
    | _ :: _ => some []
  else some []

omit [L.EffectiveLanguage] in
/-- The relation branch of `satStack` in Boolean-condition form. -/
theorem satStack_rel_eq (v : Fin k → ℕ) {n : ℕ} (R : L.Relations n) (b : ℕ)
    (s' : List (FormulaSymbol L (Fin k))) :
    satStack v (Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr b) :: s') =
      (if (s'.take n).length = n ∧ (s'.take n).all (isTermLetterAt b) then
        (b, true, relFlag v ⟨n, R⟩ b (s'.take n))
       else (0, true, false)) :: satStack v (s'.drop n) := by
  rw [satStack]
  congr 1
  by_cases hb : (s'.take n).length = n ∧ (s'.take n).all (isTermLetterAt b)
  · obtain ⟨h, h'⟩ := (rel_cond_iff s' n b).1 hb
    rw [dif_pos h, if_pos h', if_pos hb]
  · rw [if_neg hb]
    by_cases h : ∀ i : Fin n, ((s'.map Sum.getLeft?)[i]?.join).isSome
    · rw [dif_pos h]
      by_cases h' : ∀ i, (Option.get _ (h i)).1 = b
      · exact absurd ((rel_cond_iff s' n b).2 ⟨h, h'⟩) hb
      · rw [if_neg h']
    · rw [dif_neg h]

omit [L.EffectiveLanguage] in
/-- The `imp` case of `satStack` in `getElem!` form (no dependent proofs). -/
theorem satStack_imp_eq (v : Fin k → ℕ) (s : List (FormulaSymbol L (Fin k))) :
    satStack v (Sum.inr (Sum.inr 0) :: s) =
      if 2 ≤ (satStack v s).length then
        impFlag (satStack v s)[0]! (satStack v s)[1]! :: (satStack v s).drop 2
      else [] := by
  rw [satStack]
  by_cases h : 2 ≤ (satStack v s).length
  · rw [dif_pos h, if_pos h, getElem!_pos _ _ (by omega), getElem!_pos _ _ (by omega)]
  · rw [dif_neg h, if_neg h]

omit [L.EffectiveLanguage] in
/-- The `all` case of `satStack` in `getElem!` form (no dependent proofs). -/
theorem satStack_all_eq (v : Fin k → ℕ) (s : List (FormulaSymbol L (Fin k))) :
    satStack v (Sum.inr (Sum.inr 1) :: s) =
      if 1 ≤ (satStack v s).length then
        allFlag (satStack v s)[0]! :: (satStack v s).drop 1
      else [] := by
  rw [satStack]
  by_cases h : 1 ≤ (satStack v s).length
  · rw [dif_pos h, if_pos h, getElem!_pos _ _ (by omega)]
  · rw [dif_neg h, if_neg h]

omit [L.EffectiveLanguage] in
/-- The step function meets the course-of-values specification. -/
private theorem satStackStepAux_spec (x : (Fin k → ℕ) × List (FormulaSymbol L (Fin k)))
    (m : ℕ) :
    satStackStepAux x ((List.range m).map (satStackAux x)) =
      some (satStackAux x m) := by
  have hprev : ∀ j, j < m →
      ((List.range m).map (satStackAux x))[j]? = some (satStackAux x j) := by
    intro j hj
    simp [hj]
  rw [satStackStepAux]
  simp only [List.length_map, List.length_range]
  by_cases hm : m ≤ x.2.length
  · rw [if_pos hm]
    rcases hs : x.2.drop (x.2.length - m) with - | ⟨c, s⟩
    · have hm0 : m = 0 := by
        have := congrArg List.length hs
        simp at this
        omega
      subst hm0
      rw [satStackAux, if_pos hm, hs]
      simp [satStack]
    · have hmlen : m = (x.2.drop (x.2.length - m)).length := by simp; omega
      have hm1 : 1 ≤ m := by
        rw [hs] at hmlen
        simp at hmlen
        omega
      have hstail : s = x.2.drop (x.2.length - (m - 1)) := by
        have h1 := congrArg List.tail hs
        rw [List.tail_drop] at h1
        have h2 : x.2.length - m + 1 = x.2.length - (m - 1) := by omega
        rw [h2] at h1
        exact h1.symm
      have hds1 : satStack x.1 s = satStackAux x (m - 1) := by
        rw [satStackAux_of_le (show m - 1 ≤ x.2.length by omega), ← hstail]
      rw [satStackAux_of_le hm, hs]
      match c, s with
      | Sum.inr (Sum.inr (n + 2)), s =>
        rw [hprev (m - 1) (by omega), satStack, hds1]
        rfl
      | Sum.inl ⟨n₁, t₁⟩, [] =>
        simp [satStack]
      | Sum.inl ⟨n₁, t₁⟩, Sum.inl ⟨n₂, t₂⟩ :: s'' =>
        rw [hs] at hmlen
        simp only [List.length_cons] at hmlen
        have hstail2 : s'' = x.2.drop (x.2.length - (m - 2)) := by
          have h1 := congrArg List.tail hstail
          rw [List.tail_drop] at h1
          have h2 : x.2.length - (m - 1) + 1 = x.2.length - (m - 2) := by omega
          rw [h2] at h1
          simpa using h1
        have hds2 : satStack x.1 s'' = satStackAux x (m - 2) := by
          rw [satStackAux_of_le (show m - 2 ≤ x.2.length by omega), ← hstail2]
        rw [hprev (m - 2) (by omega), satStack, hds2]
        rfl
      | Sum.inl ⟨n₁, t₁⟩, Sum.inr g :: s'' =>
        simp [satStack]
      | Sum.inr (Sum.inl ⟨n, R⟩), [] =>
        simp [satStack]
      | Sum.inr (Sum.inl ⟨n, R⟩), Sum.inl y :: s'' =>
        simp [satStack]
      | Sum.inr (Sum.inl ⟨n, R⟩), Sum.inr (Sum.inl y) :: s'' =>
        simp [satStack]
      | Sum.inr (Sum.inl ⟨n, R⟩), Sum.inr (Sum.inr b) :: s' =>
        rw [hs] at hmlen
        simp only [List.length_cons] at hmlen
        have hstail2 : s' = x.2.drop (x.2.length - (m - 2)) := by
          have h1 := congrArg List.tail hstail
          rw [List.tail_drop] at h1
          have h2 : x.2.length - (m - 1) + 1 = x.2.length - (m - 2) := by omega
          rw [h2] at h1
          simpa using h1
        have hdsr : satStack x.1 (s'.drop n) = satStackAux x (m - 2 - n) := by
          by_cases hn : n ≤ m - 2
          · rw [satStackAux_of_le (show m - 2 - n ≤ x.2.length by omega), hstail2,
              List.drop_drop,
              show x.2.length - (m - 2) + n = x.2.length - (m - 2 - n) by omega]
          · rw [List.drop_eq_nil_of_le (by omega), show m - 2 - n = 0 by omega,
              satStackAux, if_pos (Nat.zero_le _), Nat.sub_zero, List.drop_length]
        show Option.map
            (fun rest ↦
              (if (s'.take n).length = n ∧ (s'.take n).all (isTermLetterAt b) then
                (b, true, relFlag x.1 ⟨n, R⟩ b (s'.take n))
               else (0, true, false)) :: rest)
            (((List.range m).map (satStackAux x))[m - 2 - n]?) =
          some (satStack x.1 (Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr b) :: s'))
        rw [hprev (m - 2 - n) (by omega), satStack_rel_eq, hdsr]
        rfl
      | Sum.inr (Sum.inr 0), s =>
        rw [hprev (m - 1) (by omega), satStack_imp_eq, hds1]
        rfl
      | Sum.inr (Sum.inr 1), s =>
        rw [hprev (m - 1) (by omega), satStack_all_eq, hds1]
        rfl
  · rw [if_neg hm, satStackAux, if_neg hm]

/-! ### Oracle computability of the step function -/

omit [L.EffectiveLanguage] [L.Structure ℕ] in
private theorem eqFlag_eq_casesOn (v : Fin k → ℕ) (c₁ c₂ : FormulaSymbol L (Fin k))
    [L.Structure ℕ] :
    eqFlag v c₁ c₂ = Option.casesOn (motive := fun _ ↦ Bool) (termOfSymbol? c₁) false
      fun t₁ ↦ Option.casesOn (motive := fun _ ↦ Bool) (termOfSymbol? c₂) false
        fun t₂ ↦ decide (t₁.realize v = t₂.realize v) := by
  rcases h₁ : termOfSymbol? c₁ with - | t₁ <;>
    rcases h₂ : termOfSymbol? c₂ with - | t₂ <;>
    simp [eqFlag, h₁, h₂]

private theorem primrec₂_impFlag : Primrec₂ impFlag := by
  have h : Primrec fun p : (ℕ × Bool × Bool) × ℕ × Bool × Bool ↦
      if p.1.1 = p.2.1 then
        (p.1.1, p.1.2.1 && p.2.2.1,
          if p.1.1 = 0 then (p.1.2.1 && p.2.2.1) && (!p.1.2.2 || p.2.2.2) else false)
      else ((0 : ℕ), true, false) :=
    Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.and.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.ite
            (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0))
            (Primrec.and.comp
              (Primrec.and.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
                (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
              (Primrec.or.comp
                (Primrec.not.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
                (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
            (Primrec.const false))))
      (Primrec.const _)
  exact h.of_eq fun p ↦ by rw [impFlag]

private theorem primrec_allFlag : Primrec allFlag := by
  have h : Primrec fun p : ℕ × Bool × Bool ↦
      Nat.casesOn (motive := fun _ ↦ ℕ × Bool × Bool) p.1 ((0 : ℕ), true, false)
        fun n ↦ (n, false, false) :=
    Primrec.nat_casesOn Primrec.fst (Primrec.const _)
      ((Primrec.pair Primrec.snd (Primrec.const (false, false))).to₂)
  exact h.of_eq fun p ↦ by rcases p with ⟨- | n, q⟩ <;> rfl

private theorem primrec₂_stepFalsumSat : Primrec₂ stepFalsumSat := by
  have hget : Primrec fun q : List (List (ℕ × Bool × Bool)) × ℕ ↦
      q.1[q.1.length - 1]? :=
    Primrec.list_getElem?.comp Primrec.fst
      (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 1))
  exact (Primrec.option_map hget
    ((Primrec.list_cons.comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.const (true, false)))
      Primrec.snd).to₂)).of_eq fun q ↦ rfl

private theorem primrec_getElemBangP (i : ℕ) :
    Primrec fun D : List (ℕ × Bool × Bool) ↦ D[i]! :=
  (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id (Primrec.const i))
    (Primrec.const default)).of_eq fun _ ↦ List.getElem!_eq_getElem?_getD.symm

private theorem primrec_stepImpSat : Primrec stepImpSat := by
  have hget : Primrec fun prev : List (List (ℕ × Bool × Bool)) ↦
      prev[prev.length - 1]? :=
    Primrec.list_getElem?.comp Primrec.id
      (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1))
  have hbody : Primrec fun D : List (ℕ × Bool × Bool) ↦
      if 2 ≤ D.length then impFlag D[0]! D[1]! :: D.drop 2 else [] :=
    Primrec.ite (Primrec.nat_le.comp (Primrec.const 2) Primrec.list_length)
      (Primrec.list_cons.comp
        (primrec₂_impFlag.comp (primrec_getElemBangP 0) (primrec_getElemBangP 1))
        (Primrec.list_drop.comp (Primrec.const 2) Primrec.id))
      (Primrec.const [])
  exact (Primrec.option_map hget ((hbody.comp Primrec.snd).to₂)).of_eq fun prev ↦ rfl

private theorem primrec_stepAllSat : Primrec stepAllSat := by
  have hget : Primrec fun prev : List (List (ℕ × Bool × Bool)) ↦
      prev[prev.length - 1]? :=
    Primrec.list_getElem?.comp Primrec.id
      (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1))
  have hbody : Primrec fun D : List (ℕ × Bool × Bool) ↦
      if 1 ≤ D.length then allFlag D[0]! :: D.drop 1 else [] :=
    Primrec.ite (Primrec.nat_le.comp (Primrec.const 1) Primrec.list_length)
      (Primrec.list_cons.comp (primrec_allFlag.comp (primrec_getElemBangP 0))
        (Primrec.list_drop.comp (Primrec.const 1) Primrec.id))
      (Primrec.const [])
  exact (Primrec.option_map hget ((hbody.comp Primrec.snd).to₂)).of_eq fun prev ↦ rfl

section OracleStep

variable (O : Set (ℕ →. ℕ)) [IsComputableStructureIn O L]

omit [DecidablePred (RelationApplicationData.relMap (L := L) (M := ℕ))] in
set_option maxHeartbeats 1000000 in
private theorem computableIn_eqFlag (k : ℕ) :
    ComputableIn O fun y : (Fin k → ℕ) ×
        (Σ m, L.Term (Fin k ⊕ Fin m)) × (Σ m, L.Term (Fin k ⊕ Fin m)) ↦
      eqFlag y.1 (Sum.inl y.2.1) (Sum.inl y.2.2) := by
  have hcmp : ComputableIn O fun y : (L.Term (Fin k) × (Fin k → ℕ)) ×
      (L.Term (Fin k) × (Fin k → ℕ)) ↦
      decide (y.1.1.realize y.1.2 = y.2.1.realize y.2.2) :=
    (Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂.comp
      ((Term.realize_computableIn O (m := k)).comp ComputableIn.fst)
      ((Term.realize_computableIn O (m := k)).comp ComputableIn.snd)
  have h₁ : ComputableIn O fun y : (Fin k → ℕ) ×
      (Σ m, L.Term (Fin k ⊕ Fin m)) × (Σ m, L.Term (Fin k ⊕ Fin m)) ↦
      termOfSymbol? (Sum.inl y.2.1 : FormulaSymbol L (Fin k)) :=
    (primrec_termOfSymbol?.comp
      (Primrec.sumInl.comp (Primrec.fst.comp Primrec.snd))).to_comp.computableIn
  have h₂ : ComputableIn O fun z : ((Fin k → ℕ) ×
      (Σ m, L.Term (Fin k ⊕ Fin m)) × (Σ m, L.Term (Fin k ⊕ Fin m))) ×
      L.Term (Fin k) ↦
      termOfSymbol? (Sum.inl z.1.2.2 : FormulaSymbol L (Fin k)) :=
    (primrec_termOfSymbol?.comp
      (Primrec.sumInl.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).to_comp.computableIn
  have hproj : ComputableIn O fun w : (((Fin k → ℕ) ×
      (Σ m, L.Term (Fin k ⊕ Fin m)) × (Σ m, L.Term (Fin k ⊕ Fin m))) ×
      L.Term (Fin k)) × L.Term (Fin k) ↦
      ((w.1.2, w.1.1.1), (w.2, w.1.1.1)) :=
    ((ComputableIn.snd.comp ComputableIn.fst).pair
      (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst))).pair
      (ComputableIn.snd.pair
        (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)))
  have hinner : ComputableIn O fun w : (((Fin k → ℕ) ×
      (Σ m, L.Term (Fin k ⊕ Fin m)) × (Σ m, L.Term (Fin k ⊕ Fin m))) ×
      L.Term (Fin k)) × L.Term (Fin k) ↦
      decide (w.1.2.realize w.1.1.1 = w.2.realize w.1.1.1) :=
    (hcmp.comp hproj).of_eq fun _ ↦ rfl
  exact (ComputableIn.option_casesOn h₁ (ComputableIn.const false)
    ((ComputableIn.option_casesOn h₂ (ComputableIn.const false)
      hinner.to₂).to₂)).of_eq fun y ↦ by
        rw [eqFlag_eq_casesOn]

omit [DecidablePred (RelationApplicationData.relMap (L := L) (M := ℕ))] in
set_option maxHeartbeats 1000000 in
private theorem computableIn_stepEqualSat (k : ℕ) :
    ComputableIn O fun q : ((Fin k → ℕ) × List (List (ℕ × Bool × Bool))) ×
        (Σ m, L.Term (Fin k ⊕ Fin m)) × (Σ m, L.Term (Fin k ⊕ Fin m)) ↦
      stepEqualSat q.1.1 q.1.2 q.2.1 q.2.2 := by
  have hget : ComputableIn O fun q : ((Fin k → ℕ) × List (List (ℕ × Bool × Bool))) ×
      (Σ m, L.Term (Fin k ⊕ Fin m)) × (Σ m, L.Term (Fin k ⊕ Fin m)) ↦
      q.1.2[q.1.2.length - 2]? :=
    (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.nat_sub.comp
        (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.const 2))).to_comp.computableIn
  have hflag : ComputableIn O fun q : ((Fin k → ℕ) × List (List (ℕ × Bool × Bool))) ×
      (Σ m, L.Term (Fin k ⊕ Fin m)) × (Σ m, L.Term (Fin k ⊕ Fin m)) ↦
      eqFlag q.1.1 (Sum.inl q.2.1) (Sum.inl q.2.2) :=
    ((computableIn_eqFlag O k).comp
      ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd)).of_eq
      fun _ ↦ rfl
  have hval : ComputableIn O fun q : ((Fin k → ℕ) × List (List (ℕ × Bool × Bool))) ×
      (Σ m, L.Term (Fin k ⊕ Fin m)) × (Σ m, L.Term (Fin k ⊕ Fin m)) ↦
      if q.2.1.1 = q.2.2.1 then
        (q.2.1.1, true, eqFlag q.1.1 (Sum.inl q.2.1) (Sum.inl q.2.2))
      else ((0 : ℕ), true, false) :=
    ComputableIn.ite
      ((Primrec.eq.comp
        ((Term.primrec_sigmaTerm_fst L (Fin k)).comp (Primrec.fst.comp Primrec.snd))
        ((Term.primrec_sigmaTerm_fst L (Fin k)).comp
          (Primrec.snd.comp Primrec.snd))).decide.to_comp.computableIn)
      ((((Term.primrec_sigmaTerm_fst L (Fin k)).comp
        (Primrec.fst.comp Primrec.snd)).to_comp.computableIn).pair
        ((ComputableIn.const true).pair hflag))
      (ComputableIn.const _)
  exact (ComputableIn.option_map hget
    (((Computable.list_cons.computableIn₂ (O := O)).comp
      (hval.comp ComputableIn.fst) ComputableIn.snd).to₂)).of_eq fun q ↦ rfl

set_option maxHeartbeats 1000000 in
private theorem computableIn_relFlag (k : ℕ)
    (hcomp : ComputableIn O fun d : RelationApplicationData L ℕ ↦ decide d.relMap) :
    ComputableIn O fun z : (Fin k → ℕ) ×
        (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L (Fin k)) ↦
      relFlag z.1 z.2.1 z.2.2.1 z.2.2.2 := by
  have hfm : ComputableIn O fun z : (Fin k → ℕ) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L (Fin k)) ↦
      z.2.2.2.filterMap termOfSymbol? :=
    (Primrec.listFilterMap (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      ((primrec_termOfSymbol?.comp Primrec.snd).to₂)).to_comp.computableIn
  have hvalues : ComputableIn O fun z : (Fin k → ℕ) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L (Fin k)) ↦
      (z.2.2.2.filterMap termOfSymbol?).map fun t ↦ t.realize z.1 :=
    ComputableIn.list_map hfm
      (((Term.realize_computableIn O (m := k)).comp
        (ComputableIn.snd.pair (ComputableIn.fst.comp ComputableIn.fst))).to₂)
  have hofs : ComputableIn O fun z : (Fin k → ℕ) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L (Fin k)) ↦
      RelationApplicationData.ofSymbolArgs?
        (z.2.1, (z.2.2.2.filterMap termOfSymbol?).map fun t ↦ t.realize z.1) :=
    (RelationApplicationData.primrec_ofSymbolArgs?.to_comp.computableIn).comp
      (((Primrec.fst.comp Primrec.snd).to_comp.computableIn).pair hvalues)
  exact ComputableIn.ite
    ((Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const 0)).decide.to_comp.computableIn)
    (ComputableIn.option_casesOn hofs (ComputableIn.const false)
      ((hcomp.comp ComputableIn.snd).to₂))
    (ComputableIn.const false)

set_option maxHeartbeats 1000000 in
private theorem computableIn_stepRelSat (k : ℕ)
    (hcomp : ComputableIn O fun d : RelationApplicationData L ℕ ↦ decide d.relMap) :
    ComputableIn O fun q : ((Fin k → ℕ) × List (List (ℕ × Bool × Bool))) ×
        (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L (Fin k)) ↦
      stepRelSat q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2 := by
  have hr1 : Primrec fun q : ((Fin k → ℕ) × List (List (ℕ × Bool × Bool))) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L (Fin k)) ↦ q.2.1.1 :=
    (primrec_relationSymbol_arity (L := L)).comp (Primrec.fst.comp Primrec.snd)
  have htake : Primrec fun q : ((Fin k → ℕ) × List (List (ℕ × Bool × Bool))) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L (Fin k)) ↦
      q.2.2.2.take q.2.1.1 :=
    Primrec.list_take.comp hr1 (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hget : ComputableIn O fun q : ((Fin k → ℕ) × List (List (ℕ × Bool × Bool))) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L (Fin k)) ↦
      q.1.2[q.1.2.length - 2 - q.2.1.1]? :=
    (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.nat_sub.comp
        (Primrec.nat_sub.comp
          (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.const 2))
        hr1)).to_comp.computableIn
  have hguard : ComputableIn O fun q : ((Fin k → ℕ) × List (List (ℕ × Bool × Bool))) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L (Fin k)) ↦
      decide ((q.2.2.2.take q.2.1.1).length = q.2.1.1 ∧
        (q.2.2.2.take q.2.1.1).all (isTermLetterAt q.2.2.1)) := by
    have hB : ComputableIn O fun q : ((Fin k → ℕ) ×
        List (List (ℕ × Bool × Bool))) ×
        (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L (Fin k)) ↦
        (decide ((q.2.2.2.take q.2.1.1).length = q.2.1.1) &&
          (q.2.2.2.take q.2.1.1).all (isTermLetterAt q.2.2.1)) :=
      (Primrec.and.comp
        ((Primrec.eq.comp (Primrec.list_length.comp htake) hr1).decide)
        (primrec₂_all_isTermLetterAt.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          htake)).to_comp.computableIn
    refine hB.of_eq fun q ↦ ?_
    rcases hall : (q.2.2.2.take q.2.1.1).all (isTermLetterAt q.2.2.1) <;>
      by_cases hlen : (q.2.2.2.take q.2.1.1).length = q.2.1.1 <;>
      simp_all
  have hflag : ComputableIn O fun q : ((Fin k → ℕ) × List (List (ℕ × Bool × Bool))) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L (Fin k)) ↦
      relFlag q.1.1 q.2.1 q.2.2.1 (q.2.2.2.take q.2.1.1) :=
    ((computableIn_relFlag O k hcomp).comp
      ((ComputableIn.fst.comp ComputableIn.fst).pair
        (((Primrec.fst.comp Primrec.snd).to_comp.computableIn).pair
          (((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).to_comp.computableIn).pair
            htake.to_comp.computableIn)))).of_eq fun _ ↦ rfl
  have hval : ComputableIn O fun q : ((Fin k → ℕ) × List (List (ℕ × Bool × Bool))) ×
      (Σ n, L.Relations n) × ℕ × List (FormulaSymbol L (Fin k)) ↦
      if (q.2.2.2.take q.2.1.1).length = q.2.1.1 ∧
          (q.2.2.2.take q.2.1.1).all (isTermLetterAt q.2.2.1) then
        (q.2.2.1, true, relFlag q.1.1 q.2.1 q.2.2.1 (q.2.2.2.take q.2.1.1))
      else ((0 : ℕ), true, false) :=
    ComputableIn.ite hguard
      (((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).to_comp.computableIn).pair
        ((ComputableIn.const true).pair hflag))
      (ComputableIn.const _)
  exact (ComputableIn.option_map hget
    (((Computable.list_cons.computableIn₂ (O := O)).comp
      (hval.comp ComputableIn.fst) ComputableIn.snd).to₂)).of_eq fun q ↦ rfl

end OracleStep

omit [L.EffectiveLanguage] in
/-- The step function as a tree of `casesOn` dispatches through `head?` and `tail`:
the combinator-friendly form behind its oracle computability. -/
private theorem satStackStepAux_eq_cases
    (x : (Fin k → ℕ) × List (FormulaSymbol L (Fin k)))
    (prev : List (List (ℕ × Bool × Bool))) :
    satStackStepAux x prev =
      if prev.length ≤ x.2.length then
        Option.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool)))
          (x.2.drop (x.2.length - prev.length)).head? (some [])
          fun c ↦
            Sum.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) c
              (fun s₁ ↦
                Option.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool)))
                  (x.2.drop (x.2.length - prev.length)).tail.head? (some [])
                  fun c₂ ↦
                    Sum.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) c₂
                      (fun s₂ ↦ stepEqualSat x.1 prev s₁ s₂) fun _ ↦ some [])
              fun g ↦
                Sum.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) g
                  (fun r ↦
                    Option.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool)))
                      (x.2.drop (x.2.length - prev.length)).tail.head? (some [])
                      fun c₂ ↦
                        Sum.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool)))
                          c₂ (fun _ ↦ some [])
                          fun g₂ ↦
                            Sum.casesOn
                              (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) g₂
                              (fun _ ↦ some [])
                              fun b ↦ stepRelSat x.1 prev r b
                                (x.2.drop (x.2.length - prev.length)).tail.tail)
                  fun j ↦
                    Nat.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) j
                      (stepImpSat prev)
                      fun j' ↦
                        Nat.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool)))
                          j' (stepAllSat prev) fun n ↦ stepFalsumSat prev n
      else some [] := by
  rw [satStackStepAux]
  by_cases hg : prev.length ≤ x.2.length
  · rw [if_pos hg, if_pos hg]
    rcases x.2.drop (x.2.length - prev.length) with - | ⟨c, tail⟩
    · rfl
    · rcases c with s₁ | g
      · rcases tail with - | ⟨c₂, tail₂⟩
        · rfl
        · rcases c₂ with s₂ | g₂ <;> rfl
      · rcases g with r | j
        · rcases tail with - | ⟨c₂, s'⟩
          · rfl
          · rcases c₂ with y | g₂
            · rfl
            · rcases g₂ with z | b <;> rfl
        · rcases j with - | j'
          · rfl
          · rcases j' with - | n <;> rfl
  · rw [if_neg hg, if_neg hg]

section OracleAssembly

variable (O : Set (ℕ →. ℕ)) [IsComputableStructureIn O L]

omit [L.Structure ℕ] [DecidablePred (RelationApplicationData.relMap (L := L) (M := ℕ))] in
private theorem primrec_dropSuffix (k : ℕ) :
    Primrec fun p : ((Fin k → ℕ) × List (FormulaSymbol L (Fin k))) ×
      List (List (ℕ × Bool × Bool)) ↦
      p.1.2.drop (p.1.2.length - p.2.length) :=
  Primrec.list_drop.comp
    (Primrec.nat_sub.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_length.comp Primrec.snd))
    (Primrec.snd.comp Primrec.fst)

omit [DecidablePred (RelationApplicationData.relMap (L := L) (M := ℕ))] in
set_option maxHeartbeats 1000000 in
private theorem computableIn_eqArm (k : ℕ) :
    ComputableIn O fun w : ((((Fin k → ℕ) ×
    List (FormulaSymbol L (Fin k))) × List (List (ℕ × Bool × Bool))) ×
    FormulaSymbol L (Fin k)) × (Σ m, L.Term (Fin k ⊕ Fin m)) ↦
    Option.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool)))
      (w.1.1.1.2.drop (w.1.1.1.2.length - w.1.1.2.length)).tail.head? (some [])
      fun c₂ ↦ Sum.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) c₂
        (fun s₂ ↦ stepEqualSat w.1.1.1.1 w.1.1.2 w.2 s₂) fun _ ↦ some [] := by
  have hproj : ComputableIn O fun z : (((((((Fin k → ℕ) ×
      List (FormulaSymbol L (Fin k))) × List (List (ℕ × Bool × Bool))) ×
      FormulaSymbol L (Fin k)) × (Σ m, L.Term (Fin k ⊕ Fin m))) ×
      FormulaSymbol L (Fin k)) × (Σ m, L.Term (Fin k ⊕ Fin m))) ↦
      ((z.1.1.1.1.1.1, z.1.1.1.1.2), (z.1.1.2, z.2)) :=
    ((ComputableIn.fst.comp (ComputableIn.fst.comp (ComputableIn.fst.comp
      (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst))))).pair
      (ComputableIn.snd.comp (ComputableIn.fst.comp (ComputableIn.fst.comp
        (ComputableIn.fst.comp ComputableIn.fst))))).pair
      ((ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
        ComputableIn.snd)
  have harm : ComputableIn O fun z : (((((((Fin k → ℕ) ×
      List (FormulaSymbol L (Fin k))) × List (List (ℕ × Bool × Bool))) ×
      FormulaSymbol L (Fin k)) × (Σ m, L.Term (Fin k ⊕ Fin m))) ×
      FormulaSymbol L (Fin k)) × (Σ m, L.Term (Fin k ⊕ Fin m))) ↦
      stepEqualSat z.1.1.1.1.1.1 z.1.1.1.1.2 z.1.1.2 z.2 :=
    ((computableIn_stepEqualSat O k).comp hproj).of_eq fun _ ↦ rfl
  exact ComputableIn.option_casesOn
    ((Primrec.list_head?.comp (Primrec.list_tail.comp
      ((primrec_dropSuffix (L := L) k).comp
        (Primrec.fst.comp Primrec.fst)))).to_comp.computableIn)
    (ComputableIn.const _)
    ((ComputableIn.sumCasesOn ComputableIn.snd harm.to₂
      ((ComputableIn.const (some [])).to₂)).to₂)

set_option maxHeartbeats 1000000 in
private theorem computableIn_relArm (k : ℕ)
    (hcomp : ComputableIn O fun d : RelationApplicationData L ℕ ↦ decide d.relMap) :
    ComputableIn O fun w : ((((Fin k → ℕ) ×
    List (FormulaSymbol L (Fin k))) × List (List (ℕ × Bool × Bool))) ×
    FormulaSymbol L (Fin k)) × (Σ n, L.Relations n) ↦
    Option.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool)))
      (w.1.1.1.2.drop (w.1.1.1.2.length - w.1.1.2.length)).tail.head? (some [])
      fun c₂ ↦ Sum.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) c₂
        (fun _ ↦ some [])
        fun g₂ ↦ Sum.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) g₂
          (fun _ ↦ some [])
          fun b ↦ stepRelSat w.1.1.1.1 w.1.1.2 w.2 b
            (w.1.1.1.2.drop (w.1.1.1.2.length - w.1.1.2.length)).tail.tail := by
  have hproj : ComputableIn O fun z : (((((((Fin k → ℕ) ×
      List (FormulaSymbol L (Fin k))) × List (List (ℕ × Bool × Bool))) ×
      FormulaSymbol L (Fin k)) × (Σ n, L.Relations n)) × FormulaSymbol L (Fin k)) ×
      ((Σ n, L.Relations n) ⊕ ℕ)) × ℕ ↦
      ((z.1.1.1.1.1.1.1, z.1.1.1.1.1.2),
        (z.1.1.1.2, (z.2,
          (z.1.1.1.1.1.1.2.drop
            (z.1.1.1.1.1.1.2.length - z.1.1.1.1.1.2.length)).tail.tail))) :=
    ((ComputableIn.fst.comp (ComputableIn.fst.comp (ComputableIn.fst.comp
      (ComputableIn.fst.comp (ComputableIn.fst.comp (ComputableIn.fst.comp
        ComputableIn.fst)))))).pair
      (ComputableIn.snd.comp (ComputableIn.fst.comp (ComputableIn.fst.comp
        (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)))))).pair
      ((ComputableIn.snd.comp (ComputableIn.fst.comp
        (ComputableIn.fst.comp ComputableIn.fst))).pair
        (ComputableIn.snd.pair
          (((Primrec.list_tail.comp (Primrec.list_tail.comp
            ((primrec_dropSuffix (L := L) k).comp
              Primrec.id))).to_comp.computableIn).comp
            (ComputableIn.fst.comp (ComputableIn.fst.comp (ComputableIn.fst.comp
              (ComputableIn.fst.comp ComputableIn.fst)))))))
  have harm : ComputableIn O fun z : (((((((Fin k → ℕ) ×
      List (FormulaSymbol L (Fin k))) × List (List (ℕ × Bool × Bool))) ×
      FormulaSymbol L (Fin k)) × (Σ n, L.Relations n)) × FormulaSymbol L (Fin k)) ×
      ((Σ n, L.Relations n) ⊕ ℕ)) × ℕ ↦
      stepRelSat z.1.1.1.1.1.1.1 z.1.1.1.1.1.2 z.1.1.1.2 z.2
        (z.1.1.1.1.1.1.2.drop
          (z.1.1.1.1.1.1.2.length - z.1.1.1.1.1.2.length)).tail.tail :=
    ((computableIn_stepRelSat O k hcomp).comp hproj).of_eq fun _ ↦ rfl
  exact ComputableIn.option_casesOn
    ((Primrec.list_head?.comp (Primrec.list_tail.comp
      ((primrec_dropSuffix (L := L) k).comp
        (Primrec.fst.comp Primrec.fst)))).to_comp.computableIn)
    (ComputableIn.const _)
    ((ComputableIn.sumCasesOn ComputableIn.snd
      ((ComputableIn.const (some [])).to₂)
      ((ComputableIn.sumCasesOn ComputableIn.snd
        ((ComputableIn.const (some [])).to₂)
        harm.to₂).to₂)).to₂)

omit [L.Structure ℕ] [IsComputableStructureIn O L]
  [DecidablePred (RelationApplicationData.relMap (L := L) (M := ℕ))] in
set_option maxHeartbeats 1000000 in
private theorem computableIn_natArm (k : ℕ) :
    ComputableIn O fun w : ((((Fin k → ℕ) ×
    List (FormulaSymbol L (Fin k))) × List (List (ℕ × Bool × Bool))) ×
    FormulaSymbol L (Fin k)) × ℕ ↦
    Nat.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) w.2
      (stepImpSat w.1.1.2)
      fun j' ↦ Nat.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) j'
        (stepAllSat w.1.1.2) fun n ↦ stepFalsumSat w.1.1.2 n :=
  ComputableIn.nat_casesOn ComputableIn.snd
    ((primrec_stepImpSat.to_comp.computableIn).comp
      (ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)))
    ((ComputableIn.nat_casesOn ComputableIn.snd
      ((primrec_stepAllSat.to_comp.computableIn).comp
        (ComputableIn.snd.comp (ComputableIn.fst.comp
          (ComputableIn.fst.comp ComputableIn.fst))))
      ((primrec₂_stepFalsumSat.to_comp.computableIn₂.comp
        (ComputableIn.snd.comp (ComputableIn.fst.comp
          (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst))))
        ComputableIn.snd).to₂)).to₂)

set_option maxHeartbeats 1000000 in
private theorem computableIn₂_satStackStepAux (k : ℕ)
    (hcomp : ComputableIn O fun d : RelationApplicationData L ℕ ↦ decide d.relMap) :
    ComputableIn₂ O (satStackStepAux (L := L) (k := k)) := by
  have hmain : ComputableIn O fun p : ((Fin k → ℕ) ×
      List (FormulaSymbol L (Fin k))) × List (List (ℕ × Bool × Bool)) ↦
      if p.2.length ≤ p.1.2.length then
        Option.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool)))
          (p.1.2.drop (p.1.2.length - p.2.length)).head? (some [])
          fun c ↦
            Sum.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) c
              (fun s₁ ↦
                Option.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool)))
                  (p.1.2.drop (p.1.2.length - p.2.length)).tail.head? (some [])
                  fun c₂ ↦
                    Sum.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) c₂
                      (fun s₂ ↦ stepEqualSat p.1.1 p.2 s₁ s₂) fun _ ↦ some [])
              fun g ↦
                Sum.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) g
                  (fun r ↦
                    Option.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool)))
                      (p.1.2.drop (p.1.2.length - p.2.length)).tail.head? (some [])
                      fun c₂ ↦
                        Sum.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool)))
                          c₂ (fun _ ↦ some [])
                          fun g₂ ↦
                            Sum.casesOn
                              (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) g₂
                              (fun _ ↦ some [])
                              fun b ↦ stepRelSat p.1.1 p.2 r b
                                (p.1.2.drop (p.1.2.length - p.2.length)).tail.tail)
                  fun j ↦
                    Nat.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool))) j
                      (stepImpSat p.2)
                      fun j' ↦
                        Nat.casesOn (motive := fun _ ↦ Option (List (ℕ × Bool × Bool)))
                          j' (stepAllSat p.2) fun n ↦ stepFalsumSat p.2 n
      else some [] := by
    refine ComputableIn.ite
      ((Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.list_length.comp
          (Primrec.snd.comp Primrec.fst))).decide.to_comp.computableIn)
      (ComputableIn.option_casesOn
        ((Primrec.list_head?.comp (primrec_dropSuffix (L := L) k)).to_comp.computableIn)
        (ComputableIn.const _)
        ((ComputableIn.sumCasesOn ComputableIn.snd
          ((computableIn_eqArm O k).to₂)
          ((ComputableIn.sumCasesOn ComputableIn.snd
            (((computableIn_relArm O k hcomp).comp
              ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd)).to₂)
            (((computableIn_natArm O k).comp
              ((ComputableIn.fst.comp ComputableIn.fst).pair
                ComputableIn.snd)).to₂)).to₂)).to₂))
      (ComputableIn.const _)
  exact hmain.of_eq fun p ↦ (satStackStepAux_eq_cases p.1 p.2).symm

/-- The guarded suffix evaluation of the satisfaction stack machine is oracle
computable, by strong recursion on the suffix length. -/
private theorem computableIn₂_satStackAux (k : ℕ)
    (hcomp : ComputableIn O fun d : RelationApplicationData L ℕ ↦ decide d.relMap) :
    ComputableIn₂ O (satStackAux (L := L) (k := k)) :=
  ComputableIn.nat_strong_rec _ (computableIn₂_satStackStepAux O k hcomp)
    satStackStepAux_spec

set_option maxHeartbeats 1000000 in
/-- The quantifier-free satisfaction decider is oracle computable. -/
private theorem computableIn_qfSatBool (k : ℕ)
    (hcomp : ComputableIn O fun d : RelationApplicationData L ℕ ↦ decide d.relMap) :
    ComputableIn O (qfSatBool (L := L) (k := k)) := by
  have hsat : ComputableIn O fun p : L.Formula (Fin k) × (Fin k → ℕ) ↦
      satStack p.2 ((p.1 : L.BoundedFormula (Fin k) 0).listEncode) := by
    have harg : ComputableIn O fun p : L.Formula (Fin k) × (Fin k → ℕ) ↦
        (((p.2, (p.1 : L.BoundedFormula (Fin k) 0).listEncode) :
          (Fin k → ℕ) × List (FormulaSymbol L (Fin k))),
          ((p.1 : L.BoundedFormula (Fin k) 0).listEncode).length) :=
      (Primrec.pair
        (Primrec.pair Primrec.snd (primrec_formula_listEncode.comp Primrec.fst))
        (Primrec.list_length.comp
          (primrec_formula_listEncode.comp Primrec.fst))).to_comp.computableIn
    exact (ComputableIn.comp (computableIn₂_satStackAux O k hcomp) harg).of_eq fun p ↦
      satStackAux_length _
  exact (ComputableIn.option_getD
    (ComputableIn.option_map
      ((Primrec.list_head?.to_comp.computableIn).comp hsat)
      (((Primrec.snd.comp (Primrec.snd.comp
        Primrec.snd)).to_comp.computableIn).to₂))
    (ComputableIn.const false)).of_eq fun p ↦ rfl

end OracleAssembly

end QFSatisfaction

section QFContracts

/-- The roadmap PR 7 gate in diagram-ready total form: quantifier-freeness together
with satisfaction is a computable predicate on formulas with tuples, deciding `false`
off the quantifier-free fragment. -/
theorem qf_realize_computablePredIn (O : Set (ℕ →. ℕ))
    [IsComputableStructureIn O L] (k : ℕ) :
    ComputablePredIn O fun p : L.Formula (Fin k) × (Fin k → ℕ) ↦
      (p.1 : L.BoundedFormula (Fin k) 0).IsQF ∧ p.1.Realize p.2 := by
  obtain ⟨hdec, hcomp⟩ :=
    IsComputableStructureIn.relMap_computablePredIn (O := O) (L := L)
  letI := hdec
  have hwit : DecidablePred fun p : L.Formula (Fin k) × (Fin k → ℕ) ↦
      (p.1 : L.BoundedFormula (Fin k) 0).IsQF ∧ p.1.Realize p.2 := fun p ↦
    if hB : qfSatBool p = true
    then Decidable.isTrue ((qfSatBool_iff p).1 hB)
    else Decidable.isFalse fun h ↦ hB ((qfSatBool_iff p).2 h)
  refine ⟨hwit, ?_⟩
  refine (computableIn_qfSatBool O k hcomp).of_eq fun p ↦ ?_
  by_cases hB : qfSatBool p = true
  · rw [hB]
    exact (@decide_eq_true _ (hwit p) ((qfSatBool_iff p).1 hB)).symm
  · rw [Bool.not_eq_true] at hB
    rw [hB]
    refine (@decide_eq_false _ (hwit p) fun h ↦ ?_).symm
    rw [(qfSatBool_iff p).2 h] at hB
    simp at hB

/-- The uniform subtype form: satisfaction of quantifier-free formulas is a computable
predicate. -/
theorem qfFormula_realize_computablePredIn (O : Set (ℕ →. ℕ))
    [IsComputableStructureIn O L] (k : ℕ) :
    ComputablePredIn O fun p : QFFormula L (Fin k) × (Fin k → ℕ) ↦
      (p.1 : L.Formula (Fin k)).Realize p.2 :=
  ((qf_realize_computablePredIn O k).comp
    ((Primrec.subtype_val.to_comp.computableIn.comp ComputableIn.fst).pair
      ComputableIn.snd)).of_eq fun p ↦ and_iff_right p.1.2

/-- The pointwise corollary: satisfaction of a fixed quantifier-free formula is a
computable predicate on tuples. -/
theorem realize_computablePredIn_of_isQF (O : Set (ℕ →. ℕ))
    [IsComputableStructureIn O L] {k : ℕ} (φ : L.Formula (Fin k))
    (hφ : (φ : L.BoundedFormula (Fin k) 0).IsQF) :
    ComputablePredIn O fun v : Fin k → ℕ ↦ φ.Realize v :=
  (qfFormula_realize_computablePredIn O k).comp
    ((ComputableIn.const (⟨φ, hφ⟩ : QFFormula L (Fin k))).pair ComputableIn.id)

end QFContracts

end FirstOrder.Language
