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

end QFSatisfaction

end FirstOrder.Language
