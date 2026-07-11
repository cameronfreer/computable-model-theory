/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.FormulaOps
import Mathlib.Computability.RE
import Mathlib.ModelTheory.Complexity

/-!
# Decidability and computability of formula complexity

Boolean deciders for mathlib's `IsAtomic` and `IsQF` (which have no `Decidable`
instances upstream), their correctness (`isAtomicBool_iff`, `isQFBool_iff`), the
resulting `DecidablePred` instances, and the roadmap acceptance gates
`computablePred_isAtomic`/`computablePred_isQF` on packaged bounded formulas.

The computability witnesses read the deciders off the symbol list: atomicity is a test
on the head symbol, and quantifier-freeness is a single left-to-right scan for a
universal-quantifier marker with one symbol of lookbehind (the marker value `1` also
occurs as a relation's variable bound, always immediately after the relation symbol).
The scan's correctness (`foldl_qfScanStep_listEncode`) is proven by structural induction
uniformly in a continuation state.

The prenex/universal/existential predicates are deferred (roadmap PR 5's later half).
-/


open Encodable

namespace FirstOrder.Language.BoundedFormula

universe u v u'

variable {L : Language.{u, v}} {α : Type u'} {n : ℕ}

/-! ### Boolean deciders -/

/-- The Boolean atomicity decider. -/
def isAtomicBool : ∀ {n}, L.BoundedFormula α n → Bool
  | _, equal _ _ => true
  | _, rel _ _ => true
  | _, _ => false

/-- The Boolean decider decides `IsAtomic`. -/
theorem isAtomicBool_iff (φ : L.BoundedFormula α n) :
    isAtomicBool φ = true ↔ φ.IsAtomic := by
  constructor
  · intro h
    cases φ with
    | equal t₁ t₂ => exact IsAtomic.equal t₁ t₂
    | rel R ts => exact IsAtomic.rel R ts
    | falsum => simp [isAtomicBool] at h
    | imp φ₁ φ₂ => simp [isAtomicBool] at h
    | all φ => simp [isAtomicBool] at h
  · rintro (⟨t₁, t₂⟩ | ⟨R, ts⟩) <;> rfl

instance : DecidablePred (IsAtomic : L.BoundedFormula α n → Prop) := fun φ ↦
  decidable_of_iff _ (isAtomicBool_iff φ)

/-- The Boolean quantifier-freeness decider. -/
def isQFBool : ∀ {n}, L.BoundedFormula α n → Bool
  | _, falsum => true
  | _, equal _ _ => true
  | _, rel _ _ => true
  | _, imp φ₁ φ₂ => isQFBool φ₁ && isQFBool φ₂
  | _, all _ => false

/-- The Boolean decider decides `IsQF`. -/
theorem isQFBool_iff (φ : L.BoundedFormula α n) : isQFBool φ = true ↔ φ.IsQF := by
  induction φ with
  | falsum => exact iff_of_true rfl IsQF.falsum
  | equal t₁ t₂ => exact iff_of_true rfl (IsAtomic.equal t₁ t₂).isQF
  | rel R ts => exact iff_of_true rfl (IsAtomic.rel R ts).isQF
  | imp φ₁ φ₂ ih₁ ih₂ =>
    rw [show isQFBool (φ₁.imp φ₂) = (isQFBool φ₁ && isQFBool φ₂) from rfl,
      Bool.and_eq_true, ih₁, ih₂]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact h₁.imp h₂
    · intro h
      cases h with
      | of_isAtomic h => cases h
      | imp h₁ h₂ => exact ⟨h₁, h₂⟩
  | all φ ih =>
    refine iff_of_false (by simp [isQFBool]) fun h ↦ ?_
    cases h with
    | of_isAtomic h => cases h

instance : DecidablePred (IsQF : L.BoundedFormula α n → Prop) := fun φ ↦
  decidable_of_iff _ (isQFBool_iff φ)

/-! ### The symbol-list scan for quantifier-freeness -/

/-- Whether a symbol is a packaged relation symbol. -/
def isRelSymbol : FormulaSymbol L α → Bool
  | Sum.inr (Sum.inl _) => true
  | _ => false

/-- Whether a symbol is the universal-quantifier marker. -/
def isAllMarker : FormulaSymbol L α → Bool
  | Sum.inr (Sum.inr 1) => true
  | _ => false

/-- One step of the left-to-right quantifier scan. The state is the flag so far and
whether the previous symbol was a relation symbol (in which case the current symbol is
that relation's variable bound, not a quantifier marker). -/
def qfScanStep (st : Bool × Bool) (c : FormulaSymbol L α) : Bool × Bool :=
  (st.1 && !(isAllMarker c && !st.2), isRelSymbol c)

private theorem foldl_qfScanStep_inlList (l : List (FormulaSymbol L α))
    (hl : ∀ x ∈ l, x.isLeft) (ok : Bool) :
    l.foldl (qfScanStep (L := L) (α := α)) (ok, false) = (ok, false) := by
  induction l generalizing ok with
  | nil => rfl
  | cons a l ih =>
    rcases a with s | g
    · have hstep : qfScanStep (ok, false) (Sum.inl s) = (ok, false) := by
        simp [qfScanStep, isAllMarker, isRelSymbol]
      rw [List.foldl_cons, hstep]
      exact ih (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) ok
    · simpa using hl _ List.mem_cons_self

/-- The scan computes the quantifier-freeness decider on `listEncode`-images, uniformly
in a continuation state. -/
theorem foldl_qfScanStep_listEncode (φ : L.BoundedFormula α n) (ok : Bool) :
    φ.listEncode.foldl (qfScanStep (L := L) (α := α)) (ok, false) =
      (ok && isQFBool φ, false) := by
  induction φ generalizing ok with
  | falsum =>
    simp [listEncode, qfScanStep, isAllMarker, isRelSymbol, isQFBool]
  | equal t₁ t₂ =>
    simp [listEncode, qfScanStep, isAllMarker, isRelSymbol, isQFBool]
  | @rel nb ar R ts =>
    rw [listEncode]
    simp only [List.cons_append, List.nil_append]
    rw [List.foldl_cons, List.foldl_cons,
      show qfScanStep (ok, false) (Sum.inr (Sum.inl ⟨ar, R⟩)) = (ok, true) from by
        simp [qfScanStep, isAllMarker, isRelSymbol],
      show qfScanStep (ok, true) (Sum.inr (Sum.inr nb)) = (ok, false) from by
        simp [qfScanStep, isRelSymbol],
      foldl_qfScanStep_inlList _ (fun x hx ↦ by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
        rfl)]
    simp [isQFBool]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    rw [listEncode, List.cons_append, List.foldl_cons,
      show qfScanStep (ok, false) (Sum.inr (Sum.inr 0)) = (ok, false) from by
        simp [qfScanStep, isAllMarker, isRelSymbol],
      List.foldl_append, ih₁, ih₂,
      show isQFBool (φ₁.imp φ₂) = (isQFBool φ₁ && isQFBool φ₂) from rfl,
      Bool.and_assoc]
  | all φ ih =>
    rw [listEncode, List.foldl_cons,
      show qfScanStep (ok, false) (Sum.inr (Sum.inr 1)) = (false, false) from by
        simp [qfScanStep, isAllMarker, isRelSymbol],
      ih,
      show isQFBool φ.all = false from rfl]
    simp

/-- The quantifier-freeness decider as a symbol-list scan. -/
theorem isQFBool_eq_scan (φ : L.BoundedFormula α n) :
    isQFBool φ = (φ.listEncode.foldl (qfScanStep (L := L) (α := α)) (true, false)).1 := by
  rw [foldl_qfScanStep_listEncode, Bool.true_and]

/-- The atomicity decider reads off the head symbol. -/
def isAtomicSymbol : Option (FormulaSymbol L α) → Bool
  | some (Sum.inl _) => true
  | some (Sum.inr (Sum.inl _)) => true
  | _ => false

/-- The atomicity decider as a head-symbol test. -/
theorem isAtomicBool_eq_head (φ : L.BoundedFormula α n) :
    isAtomicBool φ = isAtomicSymbol φ.listEncode.head? := by
  cases φ <;> rfl

/-! ### Computability -/

section PrimrecComplexity

variable [Primcodable α] [L.EffectiveLanguage]

private theorem primrec_isRelSymbol : Primrec (isRelSymbol (L := L) (α := α)) := by
  have h : Primrec fun c : FormulaSymbol L α ↦
      Sum.casesOn (motive := fun _ ↦ Bool) c (fun _ ↦ false)
        fun g ↦ Sum.casesOn g (fun _ ↦ true) fun _ ↦ false :=
    Primrec.sumCasesOn Primrec.id ((Primrec.const false).to₂)
      ((Primrec.sumCasesOn Primrec.snd ((Primrec.const true).to₂)
        ((Primrec.const false).to₂)).to₂)
  exact h.of_eq fun c ↦ by rcases c with s | (r | k) <;> rfl

private theorem primrec_isAllMarker : Primrec (isAllMarker (L := L) (α := α)) := by
  have h : Primrec fun c : FormulaSymbol L α ↦
      Sum.casesOn (motive := fun _ ↦ Bool) c (fun _ ↦ false)
        fun g ↦ Sum.casesOn g (fun _ ↦ false)
          fun j ↦ Nat.casesOn j false fun j' ↦ Nat.casesOn j' true fun _ ↦ false :=
    Primrec.sumCasesOn Primrec.id ((Primrec.const false).to₂)
      ((Primrec.sumCasesOn Primrec.snd ((Primrec.const false).to₂)
        ((Primrec.nat_casesOn Primrec.snd (Primrec.const false)
          ((Primrec.nat_casesOn Primrec.snd (Primrec.const true)
            ((Primrec.const false).to₂)).to₂)).to₂)).to₂)
  exact h.of_eq fun c ↦ by rcases c with s | (r | (- | - | j)) <;> rfl

private theorem primrec₂_qfScanStep : Primrec₂ (qfScanStep (L := L) (α := α)) := by
  have h : Primrec fun p : (Bool × Bool) × FormulaSymbol L α ↦
      ((p.1.1 && !(isAllMarker p.2 && !p.1.2), isRelSymbol p.2) : Bool × Bool) :=
    Primrec.pair
      (Primrec.and.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.not.comp (Primrec.and.comp (primrec_isAllMarker.comp Primrec.snd)
          (Primrec.not.comp (Primrec.snd.comp Primrec.fst)))))
      (primrec_isRelSymbol.comp Primrec.snd)
  exact h.of_eq fun p ↦ rfl

/-- The quantifier-freeness decider is primitive recursive on packaged formulas. -/
theorem primrec_isQFBool :
    Primrec fun s : Σ n, L.BoundedFormula α n ↦ isQFBool s.2 := by
  have h : Primrec fun s : Σ n, L.BoundedFormula α n ↦
      (s.2.listEncode.foldl (qfScanStep (L := L) (α := α)) (true, false)).1 :=
    Primrec.fst.comp (Primrec.list_foldl primrec_sigmaBoundedFormula_listEncode
      (Primrec.const (true, false))
      ((primrec₂_qfScanStep.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂))
  exact h.of_eq fun s ↦ (isQFBool_eq_scan s.2).symm

private theorem primrec_isAtomicSymbol : Primrec (isAtomicSymbol (L := L) (α := α)) := by
  have h : Primrec fun o : Option (FormulaSymbol L α) ↦
      Option.casesOn (motive := fun _ ↦ Bool) o false fun c ↦
        Sum.casesOn c (fun _ ↦ true) fun g ↦ Sum.casesOn g (fun _ ↦ true) fun _ ↦ false :=
    Primrec.option_casesOn Primrec.id (Primrec.const false)
      ((Primrec.sumCasesOn Primrec.snd ((Primrec.const true).to₂)
        ((Primrec.sumCasesOn Primrec.snd ((Primrec.const true).to₂)
          ((Primrec.const false).to₂)).to₂)).to₂)
  exact h.of_eq fun o ↦ by rcases o with - | (s | (r | k)) <;> rfl

/-- The atomicity decider is primitive recursive on packaged formulas. -/
theorem primrec_isAtomicBool :
    Primrec fun s : Σ n, L.BoundedFormula α n ↦ isAtomicBool s.2 :=
  ((primrec_isAtomicSymbol (L := L) (α := α)).comp
    (Primrec.list_head?.comp primrec_sigmaBoundedFormula_listEncode)).of_eq
      fun s ↦ (isAtomicBool_eq_head s.2).symm

/-- The roadmap acceptance gate: atomicity of packaged bounded formulas is a computable
predicate. -/
theorem computablePred_isAtomic :
    ComputablePred fun s : Σ n, L.BoundedFormula α n ↦ s.2.IsAtomic :=
  ⟨fun _ ↦ inferInstance,
    (primrec_isAtomicBool.to_comp).of_eq fun s ↦
      Bool.eq_iff_iff.2 ((isAtomicBool_iff s.2).trans (decide_eq_true_iff).symm)⟩

/-- The roadmap acceptance gate: quantifier-freeness of packaged bounded formulas is a
computable predicate. -/
theorem computablePred_isQF :
    ComputablePred fun s : Σ n, L.BoundedFormula α n ↦ s.2.IsQF :=
  ⟨fun _ ↦ inferInstance,
    (primrec_isQFBool.to_comp).of_eq fun s ↦
      Bool.eq_iff_iff.2 ((isQFBool_iff s.2).trans (decide_eq_true_iff).symm)⟩

end PrimrecComplexity

end FirstOrder.Language.BoundedFormula
