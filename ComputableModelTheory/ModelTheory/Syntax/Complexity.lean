/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.ComputableOps
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

namespace FirstOrder.Language

variable {L : Language} {α : Type*}

/-- An atomic formula: a formula bundled with its atomicity. -/
abbrev AtomicFormula (L : Language) (α : Type*) :=
  { φ : L.Formula α // (φ : L.BoundedFormula α 0).IsAtomic }

/-- A quantifier-free formula: a formula bundled with its quantifier-freeness. -/
abbrev QFFormula (L : Language) (α : Type*) :=
  { φ : L.Formula α // (φ : L.BoundedFormula α 0).IsQF }

/-- Nondependent atomic-formula data: two terms to be equated, or a packaged relation
symbol with its argument-term list. -/
abbrev AtomicData (L : Language) (α : Type*) :=
  (L.Term α × L.Term α) ⊕ (L.RelationSymbol × List (L.Term α))

/-- The bound-`0` term carried by a term letter of the formula alphabet, relabelled to
the plain variable type. -/
def termOfSymbol? (c : FormulaSymbol L α) : Option (L.Term α) :=
  (c.getLeft?.bind (Term.sigmaFiberZero? L α)).map fun t ↦ t.relabel (Sum.elim id Fin.elim0)

@[simp]
theorem termOfSymbol?_inl (t : L.Term (α ⊕ Fin 0)) :
    termOfSymbol? (Sum.inl ⟨0, t⟩ : FormulaSymbol L α) =
      some (t.relabel (Sum.elim id Fin.elim0)) :=
  rfl

@[simp]
theorem termOfSymbol?_inr (g : (Σ n, L.Relations n) ⊕ ℕ) :
    termOfSymbol? (Sum.inr g : FormulaSymbol L α) = none :=
  rfl

/-- The atomic-formula data extractor: reads the head of the symbol list and collects
the equality's two terms or the relation's argument terms. Total, returning `none` off
the atomic cases. -/
def atomicData? (φ : L.Formula α) : Option (AtomicData L α) :=
  (φ : L.BoundedFormula α 0).listEncode.head?.bind fun c ↦
    match c with
    | Sum.inl _ =>
      (termOfSymbol? c).bind fun t₁ ↦
        ((φ : L.BoundedFormula α 0).listEncode[1]?.bind termOfSymbol?).map fun t₂ ↦
          Sum.inl (t₁, t₂)
    | Sum.inr (Sum.inl r) =>
      some (Sum.inr (r,
        ((φ : L.BoundedFormula α 0).listEncode.drop 2).filterMap termOfSymbol?))
    | Sum.inr (Sum.inr _) => none

theorem atomicData?_eq_some_of_equal (t₁ t₂ : L.Term (α ⊕ Fin 0)) :
    atomicData? (BoundedFormula.equal t₁ t₂ : L.Formula α) =
      some (Sum.inl (t₁.relabel (Sum.elim id Fin.elim0),
        t₂.relabel (Sum.elim id Fin.elim0))) := by
  rw [atomicData?]
  rfl

theorem atomicData?_eq_some_of_rel {n : ℕ} (R : L.Relations n)
    (ts : Fin n → L.Term (α ⊕ Fin 0)) :
    atomicData? (BoundedFormula.rel R ts : L.Formula α) =
      some (Sum.inr ((⟨n, R⟩ : L.RelationSymbol),
        (List.finRange n).map fun i ↦ (ts i).relabel (Sum.elim id Fin.elim0))) := by
  rw [atomicData?,
    show (BoundedFormula.rel R ts : L.BoundedFormula α 0).listEncode =
      Sum.inr (Sum.inl ⟨n, R⟩) :: Sum.inr (Sum.inr 0) ::
        (List.finRange n).map (fun i ↦ (Sum.inl ⟨0, ts i⟩ : FormulaSymbol L α)) from by
      rw [BoundedFormula.listEncode]
      simp]
  show some (Sum.inr (((⟨n, R⟩ : L.RelationSymbol), ((List.finRange n).map
    (fun i ↦ (Sum.inl ⟨0, ts i⟩ : FormulaSymbol L α))).filterMap termOfSymbol?)) :
      AtomicData L α) = _
  rw [List.filterMap_map,
    show (termOfSymbol? ∘ fun i : Fin n ↦ (Sum.inl ⟨0, ts i⟩ : FormulaSymbol L α)) =
      some ∘ fun i ↦ (ts i).relabel (Sum.elim id Fin.elim0) from funext fun i ↦ rfl,
    List.filterMap_eq_map]
  rfl

theorem atomicData?_isSome_iff (φ : L.Formula α) :
    (atomicData? φ).isSome ↔ (φ : L.BoundedFormula α 0).IsAtomic := by
  cases φ with
  | falsum =>
    exact iff_of_false (by simp [atomicData?, BoundedFormula.listEncode]) (by rintro ⟨⟩)
  | equal t₁ t₂ =>
    exact iff_of_true (by rw [atomicData?_eq_some_of_equal]; rfl)
      (BoundedFormula.IsAtomic.equal t₁ t₂)
  | rel R ts =>
    exact iff_of_true (by rw [atomicData?_eq_some_of_rel]; rfl) (BoundedFormula.IsAtomic.rel R ts)
  | imp φ₁ φ₂ =>
    refine iff_of_false (by simp [atomicData?, BoundedFormula.listEncode]) fun h ↦ ?_
    cases h
  | all φ =>
    refine iff_of_false (by simp [atomicData?, BoundedFormula.listEncode]) fun h ↦ ?_
    cases h

section ComputableExtract

variable [Primcodable α] [L.EffectiveLanguage]

/-- Packaging a formula at index `0` is primitive recursive: the codes agree. -/
theorem primrec_formula_toSigma :
    Primrec fun φ : L.Formula α ↦
      (⟨0, (φ : L.BoundedFormula α 0)⟩ : Σ n, L.BoundedFormula α n) :=
  Primrec.encode_iff.1 (Primrec.encode.of_eq fun _ ↦ rfl)

/-- The symbol list of a formula is primitive recursive. -/
theorem primrec_formula_listEncode :
    Primrec fun φ : L.Formula α ↦ (φ : L.BoundedFormula α 0).listEncode :=
  (BoundedFormula.primrec_sigmaBoundedFormula_listEncode.comp
    primrec_formula_toSigma).of_eq fun _ ↦ rfl

/-- Term extraction from a symbol is primitive recursive. -/
theorem primrec_termOfSymbol? : Primrec (termOfSymbol? (L := L) (α := α)) := by
  have hgl : Primrec fun c : FormulaSymbol L α ↦ c.getLeft? := by
    have h : Primrec fun c : FormulaSymbol L α ↦
        Sum.casesOn (motive := fun _ ↦ Option (Σ k, L.Term (α ⊕ Fin k))) c
          (fun s ↦ some s) fun _ ↦ none :=
      Primrec.sumCasesOn Primrec.id
        ((Primrec.option_some.comp Primrec.snd).to₂) ((Primrec.const none).to₂)
    exact h.of_eq fun c ↦ by rcases c with s | g <;> rfl
  have hrel : Primrec fun t : L.Term (α ⊕ Fin 0) ↦
      t.relabel (Sum.elim id Fin.elim0) := by
    have hg : Primrec (Sum.elim id Fin.elim0 : α ⊕ Fin 0 → α) := by
      have h : Primrec fun c : α ⊕ Fin 0 ↦
          Sum.casesOn (motive := fun _ ↦ α) c (fun a ↦ a) fun i ↦ i.elim0 :=
        Primrec.sumCasesOn Primrec.id (Primrec.snd.to₂)
          ((Primrec.of_isEmpty (fun p : (α ⊕ Fin 0) × Fin 0 ↦ (p.2.elim0 : α))).to₂)
      refine h.of_eq fun c ↦ ?_
      rcases c with a | i
      · rfl
      · exact i.elim0
    exact Term.primrec_relabel hg
  exact Primrec.option_map
    (Primrec.option_bind hgl ((Term.primrec_sigmaFiberZero? L α).comp Primrec.snd).to₂)
    ((hrel.comp Primrec.snd).to₂)

/-- The atomic-data extractor is primitive recursive. -/
theorem primrec_atomicData? : Primrec (atomicData? (L := L) (α := α)) := by
  have hle : Primrec fun φ : L.Formula α ↦ (φ : L.BoundedFormula α 0).listEncode :=
    primrec_formula_listEncode
  have hinl : Primrec₂ fun (x : L.Formula α × FormulaSymbol L α)
      (s : Σ k, L.Term (α ⊕ Fin k)) ↦
      (termOfSymbol? x.2).bind fun t₁ ↦
        ((x.1 : L.BoundedFormula α 0).listEncode[1]?.bind termOfSymbol?).map fun t₂ ↦
          (Sum.inl (t₁, t₂) : AtomicData L α) :=
    ((Primrec.option_bind
      ((primrec_termOfSymbol?.comp Primrec.snd).comp Primrec.fst)
      ((Primrec.option_map
        ((Primrec.option_bind
          (Primrec.list_getElem?.comp (hle.comp Primrec.fst) (Primrec.const 1))
          ((primrec_termOfSymbol?.comp Primrec.snd).to₂)).comp
            (Primrec.fst.comp Primrec.fst))
        ((Primrec.sumInl.comp
          ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂)).to₂)).to₂)
  have hinr : Primrec₂ fun (x : L.Formula α × FormulaSymbol L α)
      (g : (Σ n, L.Relations n) ⊕ ℕ) ↦
      (Sum.casesOn (motive := fun _ ↦ Option (AtomicData L α)) g
        (fun r ↦ some (Sum.inr (r,
          ((x.1 : L.BoundedFormula α 0).listEncode.drop 2).filterMap termOfSymbol?)))
        fun _ ↦ none) := by
    have hargs : Primrec fun y : (L.Formula α × FormulaSymbol L α) ×
        ((Σ n, L.Relations n) ⊕ ℕ) ↦
        ((y.1.1 : L.BoundedFormula α 0).listEncode.drop 2).filterMap termOfSymbol? :=
      Primrec.listFilterMap
        (Primrec.list_drop.comp (Primrec.const 2)
          (hle.comp (Primrec.fst.comp Primrec.fst)))
        ((primrec_termOfSymbol?.comp Primrec.snd).to₂)
    exact (Primrec.sumCasesOn Primrec.snd
      ((Primrec.option_some.comp (Primrec.sumInr.comp
        (Primrec.snd.pair (hargs.comp Primrec.fst)))).to₂)
      ((Primrec.const none).to₂)).to₂
  have hbody : Primrec₂ fun (φ : L.Formula α) (c : FormulaSymbol L α) ↦
      (match c with
      | Sum.inl _ =>
        (termOfSymbol? c).bind fun t₁ ↦
          ((φ : L.BoundedFormula α 0).listEncode[1]?.bind termOfSymbol?).map fun t₂ ↦
            Sum.inl (t₁, t₂)
      | Sum.inr (Sum.inl r) =>
        some (Sum.inr (r,
          ((φ : L.BoundedFormula α 0).listEncode.drop 2).filterMap termOfSymbol?))
      | Sum.inr (Sum.inr _) => none : Option (AtomicData L α)) := by
    have h := Primrec.sumCasesOn
      (Primrec.snd : Primrec fun x : L.Formula α × FormulaSymbol L α ↦ x.2)
      hinl hinr
    exact h.of_eq fun x ↦ by rcases x with ⟨φ, (s | (r | j))⟩ <;> rfl
  exact (Primrec.option_bind (Primrec.list_head?.comp hle) hbody).of_eq fun φ ↦ rfl

/-- The atomicity decider is primitive recursive on formulas. -/
theorem primrec_formula_isAtomicBool :
    Primrec fun φ : L.Formula α ↦ BoundedFormula.isAtomicBool (φ : L.BoundedFormula α 0) :=
  ((BoundedFormula.primrec_isAtomicSymbol.comp
    (Primrec.list_head?.comp primrec_formula_listEncode)).of_eq
    fun _ ↦ (BoundedFormula.isAtomicBool_eq_head _).symm)

/-- Atomicity of formulas is a primitive recursive predicate. -/
theorem primrecPred_formula_isAtomic :
    PrimrecPred fun φ : L.Formula α ↦ (φ : L.BoundedFormula α 0).IsAtomic := by
  refine Primrec.primrecPred ((primrec_formula_isAtomicBool (L := L)).of_eq fun φ ↦ ?_)
  exact Bool.eq_iff_iff.2 ((BoundedFormula.isAtomicBool_iff _).trans (decide_eq_true_iff).symm)

/-- Atomic formulas over a `Primcodable` variable type are primitively codable, as a
subtype of formulas. -/
instance : Primcodable { φ : L.Formula α // (φ : L.BoundedFormula α 0).IsAtomic } :=
  Primcodable.subtype primrecPred_formula_isAtomic

/-- The quantifier-freeness decider is primitive recursive on formulas. -/
theorem primrec_formula_isQFBool :
    Primrec fun φ : L.Formula α ↦ BoundedFormula.isQFBool (φ : L.BoundedFormula α 0) :=
  (BoundedFormula.primrec_isQFBool.comp primrec_formula_toSigma).of_eq fun _ ↦ rfl

/-- Quantifier-freeness of formulas is a primitive recursive predicate. -/
theorem primrecPred_formula_isQF :
    PrimrecPred fun φ : L.Formula α ↦ (φ : L.BoundedFormula α 0).IsQF := by
  refine Primrec.primrecPred ((primrec_formula_isQFBool (L := L)).of_eq fun φ ↦ ?_)
  exact Bool.eq_iff_iff.2
    ((BoundedFormula.isQFBool_iff _).trans (decide_eq_true_iff).symm)

/-- Quantifier-free formulas over a `Primcodable` variable type are primitively
codable, as a subtype of formulas. -/
instance : Primcodable { φ : L.Formula α // (φ : L.BoundedFormula α 0).IsQF } :=
  Primcodable.subtype primrecPred_formula_isQF

/-- The atomic-data extractor is computable. -/
theorem computable_atomicData? : Computable (atomicData? (L := L) (α := α)) :=
  primrec_atomicData?.to_comp

end ComputableExtract

end FirstOrder.Language
