/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.UniformTermEvaluation
import ComputableModelTheory.ModelTheory.Computable.AtomicEquiv

/-!
# Bounded-variable atomic data and its uniform realization

Typed atomic normal-form data over natural-number variables — `AtomicData L ℕ`, a term
equality or a relation symbol with a term list — is *valid at width `k`* when every
variable is below `k` and relation argument lists match arities. Validity is decided
by scanning symbol lists (`AtomicData.validAtBool`, primitive recursive uniformly in
the width). `ComputableAgeIn.realizeAtomicData` realizes such data at an age index
under a list environment through the uniform term evaluator, and is computable
uniformly in the index, the environment, and the data.

The central correctness gate `atomicEquivalent_iff_forall_validAtomicData`: two
width-`k` tuples are atomically equivalent exactly when every atomic data valid at `k`
has the same realization on both. Fin-variable terms enter the data by relabeling
along `Fin.val`; valid natural-variable terms return by `Term.restrictVar`.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {L : Language} [L.EffectiveLanguage]

namespace Term

omit [L.EffectiveLanguage] in
/-- A variable occurs in a term exactly when its letter occurs in the symbol list. -/
theorem mem_varFinset_iff_inl_mem_listEncode (t : L.Term ℕ) (v : ℕ) :
    v ∈ t.varFinset ↔ Sum.inl v ∈ t.listEncode := by
  induction t with
  | var a => simp [varFinset, listEncode]
  | func f ts ih =>
    simp only [varFinset, listEncode, Finset.mem_biUnion, Finset.mem_univ, true_and,
      List.mem_cons, reduceCtorEq, List.mem_flatMap, List.mem_finRange, false_or]
    exact exists_congr fun i ↦ ih i

/-- All variables of a term lie below the bound. -/
def VarsBelow (k : ℕ) (t : L.Term ℕ) : Prop :=
  ∀ v ∈ t.varFinset, v < k

/-- The symbol-list scan for bounded variables. -/
def varsBelowBool (k : ℕ) (t : L.Term ℕ) : Bool :=
  t.listEncode.all fun c ↦
    Sum.casesOn (motive := fun _ ↦ Bool) c (fun v ↦ decide (v < k)) fun _ ↦ true

omit [L.EffectiveLanguage] in
/-- The scan decides bounded variables. -/
theorem varsBelowBool_iff (k : ℕ) (t : L.Term ℕ) :
    varsBelowBool k t = true ↔ VarsBelow k t := by
  rw [varsBelowBool, List.all_eq_true]
  constructor
  · intro h v hv
    exact of_decide_eq_true
      (h (Sum.inl v) ((mem_varFinset_iff_inl_mem_listEncode t v).1 hv))
  · intro h c hc
    rcases c with v | g
    · exact decide_eq_true (h v ((mem_varFinset_iff_inl_mem_listEncode t v).2 hc))
    · rfl

omit [L.EffectiveLanguage] in
/-- Relabeling a `Fin`-variable term along `Fin.val` produces bounded-variable
data. -/
theorem varsBelow_relabel_val {k : ℕ} (t : L.Term (Fin k)) :
    VarsBelow k (t.relabel Fin.val) := by
  intro v hv
  induction t with
  | var a =>
    simp only [relabel, varFinset, Finset.mem_singleton] at hv
    exact hv ▸ a.isLt
  | func f ts ih =>
    simp only [relabel, varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
      at hv
    obtain ⟨i, hi⟩ := hv
    exact ih i hi

private theorem list_all_eq_foldr {β : Type*} (f : β → Bool) (l : List β) :
    l.all f = l.foldr (fun b r ↦ f b && r) true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.all_cons, ih]

/-- The bounded-variable scan is primitive recursive uniformly in the bound. -/
theorem primrec₂_varsBelowBool : Primrec₂ (varsBelowBool (L := L)) := by
  have h : Primrec fun p : ℕ × L.Term ℕ ↦
      p.2.listEncode.foldr
        (fun c r ↦
          (Sum.casesOn (motive := fun _ ↦ Bool) c (fun v ↦ decide (v < p.1))
            fun _ ↦ true) && r) true :=
    Primrec.list_foldr (Term.primrec_listEncode.comp Primrec.snd)
      (Primrec.const true)
      ((Primrec.and.comp
        (Primrec.sumCasesOn (Primrec.fst.comp Primrec.snd)
          (((Primrec.nat_lt.comp Primrec.snd
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).decide).to₂)
          ((Primrec.const true).to₂))
        (Primrec.snd.comp Primrec.snd)).to₂)
  exact h.of_eq fun p ↦ (list_all_eq_foldr _ _).symm

end Term

namespace AtomicData

/-- Validity of atomic data at a width: every variable is below the width, and
relation argument lists match arities. -/
def ValidAt (k : ℕ) : AtomicData L ℕ → Prop
  | Sum.inl q => Term.VarsBelow k q.1 ∧ Term.VarsBelow k q.2
  | Sum.inr q => q.2.length = q.1.arity ∧ ∀ t ∈ q.2, Term.VarsBelow k t

/-- The validity scan. -/
def validAtBool (k : ℕ) (d : AtomicData L ℕ) : Bool :=
  Sum.casesOn (motive := fun _ ↦ Bool) d
    (fun q ↦ Term.varsBelowBool k q.1 && Term.varsBelowBool k q.2)
    fun q ↦ decide (q.2.length = q.1.arity) && q.2.all (Term.varsBelowBool k)

omit [L.EffectiveLanguage] in
/-- The scan decides validity. -/
theorem validAtBool_iff (k : ℕ) (d : AtomicData L ℕ) :
    validAtBool k d = true ↔ ValidAt k d := by
  rcases d with q | q
  · show (_ && _) = true ↔ _ ∧ _
    rw [Bool.and_eq_true, Term.varsBelowBool_iff, Term.varsBelowBool_iff]
  · show (_ && _) = true ↔ _ ∧ _
    rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact and_congr_right fun _ ↦
      forall₂_congr fun t _ ↦ Term.varsBelowBool_iff k t

/-- The validity scan is primitive recursive uniformly in the width. -/
theorem primrec₂_validAtBool : Primrec₂ (validAtBool (L := L)) := by
  have hall : Primrec fun p : (ℕ × AtomicData L ℕ) ×
      (L.RelationSymbol × List (L.Term ℕ)) ↦
      p.2.2.all (Term.varsBelowBool p.1.1) := by
    have h : Primrec fun p : (ℕ × AtomicData L ℕ) ×
        (L.RelationSymbol × List (L.Term ℕ)) ↦
        p.2.2.foldr (fun t r ↦ Term.varsBelowBool p.1.1 t && r) true :=
      Primrec.list_foldr (Primrec.snd.comp Primrec.snd) (Primrec.const true)
        ((Primrec.and.comp
          (Term.primrec₂_varsBelowBool.comp
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)).to₂)
    exact h.of_eq fun p ↦ (Term.list_all_eq_foldr _ _).symm
  have h : Primrec fun p : ℕ × AtomicData L ℕ ↦
      Sum.casesOn (motive := fun _ ↦ Bool) p.2
        (fun q ↦ Term.varsBelowBool p.1 q.1 && Term.varsBelowBool p.1 q.2)
        fun q ↦ decide (q.2.length = q.1.arity) && q.2.all (Term.varsBelowBool p.1) :=
    Primrec.sumCasesOn Primrec.snd
      ((Primrec.and.comp
        (Term.primrec₂_varsBelowBool.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd))
        (Term.primrec₂_varsBelowBool.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd))).to₂)
      ((Primrec.and.comp
        ((Primrec.eq.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
          ((primrec_relationSymbol_arity (L := L)).comp
            (Primrec.fst.comp Primrec.snd))).decide)
        hall).to₂)
  exact h.of_eq fun p ↦ rfl

end AtomicData

namespace ComputableAgeIn

variable {O : Set (ℕ →. ℕ)} (K : ComputableAgeIn O L)

/-- Uniform realization of atomic data at an age index under a list environment:
equalities compare uniform term evaluations; relation data packages its evaluated
term list, arity-checked, into the age's uniform relation interpretation; malformed
relation data is false. -/
def realizeAtomicData (i : ℕ) (env : Tuple ℕ) : AtomicData L ℕ → Prop
  | Sum.inl q => K.termRealize ((i, env), q.1) = K.termRealize ((i, env), q.2)
  | Sum.inr q =>
    Option.casesOn (motive := fun _ ↦ Prop)
      (RelationApplicationData.ofSymbolArgs?
        (q.1, q.2.map fun t ↦ K.termRealize ((i, env), t)))
      False fun d ↦ @RelationApplicationData.relMap L ℕ (K.structureAt i) d

set_option maxHeartbeats 1000000 in
/-- Uniform atomic-data realization is computable in the oracle: one program over the
index, the environment, and the data. -/
theorem realizeAtomicData_computablePredIn :
    ComputablePredIn O fun p : (ℕ × Tuple ℕ) × AtomicData L ℕ ↦
      K.realizeAtomicData p.1.1 p.1.2 p.2 := by
  obtain ⟨hRdec, hRcomp⟩ := K.relMap_computablePredIn
  have hvals : ComputableIn O fun y : ((ℕ × Tuple ℕ) × AtomicData L ℕ) ×
      (L.RelationSymbol × List (L.Term ℕ)) ↦
      y.2.2.map fun t ↦ K.termRealize ((y.1.1.1, y.1.1.2), t) :=
    ComputableIn.list_map
      ((Primrec.snd.comp Primrec.snd).to_comp.computableIn)
      (((K.termRealize_computableIn).comp
        ((((Primrec.fst.comp (Primrec.fst.comp
            (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp (Primrec.fst.comp
            (Primrec.fst.comp Primrec.fst)))).to_comp.computableIn).pair
          ComputableIn.snd)).to₂)
  have hofs : ComputableIn O fun y : ((ℕ × Tuple ℕ) × AtomicData L ℕ) ×
      (L.RelationSymbol × List (L.Term ℕ)) ↦
      RelationApplicationData.ofSymbolArgs?
        (y.2.1, y.2.2.map fun t ↦ K.termRealize ((y.1.1.1, y.1.1.2), t)) :=
    (RelationApplicationData.primrec_ofSymbolArgs?.to_comp.computableIn).comp
      (((Primrec.fst.comp Primrec.snd).to_comp.computableIn).pair hvals)
  have hrel : ComputableIn O fun y : ((ℕ × Tuple ℕ) × AtomicData L ℕ) ×
      (L.RelationSymbol × List (L.Term ℕ)) ↦
      Option.casesOn (motive := fun _ ↦ Bool)
        (RelationApplicationData.ofSymbolArgs?
          (y.2.1, y.2.2.map fun t ↦ K.termRealize ((y.1.1.1, y.1.1.2), t)))
        false fun d ↦ decide ((fun p : ℕ × RelationApplicationData L ℕ ↦
          @RelationApplicationData.relMap L ℕ (K.structureAt p.1) p.2)
          (y.1.1.1, d)) :=
    ComputableIn.option_casesOn hofs (ComputableIn.const false)
      ((hRcomp.comp
        (((Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst))).to_comp.computableIn).pair
          ComputableIn.snd)).to₂)
  have heq : ComputableIn O fun y : ((ℕ × Tuple ℕ) × AtomicData L ℕ) ×
      (L.Term ℕ × L.Term ℕ) ↦
      decide (K.termRealize ((y.1.1.1, y.1.1.2), y.2.1) =
        K.termRealize ((y.1.1.1, y.1.1.2), y.2.2)) := by
    have hproj : ComputableIn O fun y : ((ℕ × Tuple ℕ) × AtomicData L ℕ) ×
        (L.Term ℕ × L.Term ℕ) ↦
        (((y.1.1.1, y.1.1.2), y.2.1), ((y.1.1.1, y.1.1.2), y.2.2)) :=
      ((((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.fst.comp Primrec.snd)).pair
        (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp Primrec.snd))).to_comp.computableIn
    have hcmp : ComputableIn O fun z : ((ℕ × Tuple ℕ) × L.Term ℕ) ×
        ((ℕ × Tuple ℕ) × L.Term ℕ) ↦
        decide (K.termRealize z.1 = K.termRealize z.2) :=
      (Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂.comp
        (K.termRealize_computableIn.comp ComputableIn.fst)
        (K.termRealize_computableIn.comp ComputableIn.snd)
    exact (hcmp.comp hproj).of_eq fun _ ↦ rfl
  refine ⟨fun p ↦ ?_, ?_⟩
  · rcases p with ⟨⟨i, env⟩, q | q⟩
    · exact instDecidableEqNat _ _
    · exact Option.rec
        (motive := fun o ↦ Decidable (Option.casesOn (motive := fun _ ↦ Prop) o
          False fun d ↦ @RelationApplicationData.relMap L ℕ (K.structureAt i) d))
        (inferInstanceAs (Decidable False)) (fun d ↦ hRdec (i, d))
        (RelationApplicationData.ofSymbolArgs?
          (q.1, q.2.map fun t ↦ K.termRealize ((i, env), t)))
  · have hB : ComputableIn O fun p : (ℕ × Tuple ℕ) × AtomicData L ℕ ↦
        Sum.casesOn (motive := fun _ ↦ Bool) p.2
          (fun q ↦ decide (K.termRealize ((p.1.1, p.1.2), q.1) =
            K.termRealize ((p.1.1, p.1.2), q.2)))
          fun q ↦
            Option.casesOn (motive := fun _ ↦ Bool)
              (RelationApplicationData.ofSymbolArgs?
                (q.1, q.2.map fun t ↦ K.termRealize ((p.1.1, p.1.2), t)))
              false fun d ↦ decide ((fun r : ℕ × RelationApplicationData L ℕ ↦
                @RelationApplicationData.relMap L ℕ (K.structureAt r.1) r.2)
                (p.1.1, d)) :=
      ComputableIn.sumCasesOn ComputableIn.snd heq.to₂ hrel.to₂
    have hbridge : ∀ (i : ℕ) (o : Option (RelationApplicationData L ℕ)),
        (Option.casesOn (motive := fun _ ↦ Bool) o false fun d ↦
          decide ((fun r : ℕ × RelationApplicationData L ℕ ↦
            @RelationApplicationData.relMap L ℕ (K.structureAt r.1) r.2) (i, d))) =
        @decide (Option.casesOn (motive := fun _ ↦ Prop) o False fun d ↦
            @RelationApplicationData.relMap L ℕ (K.structureAt i) d)
          (Option.rec (inferInstanceAs (Decidable False))
            (fun d ↦ hRdec (i, d)) o) := by
      rintro i (- | d)
      · exact (decide_eq_false fun h ↦ h).symm
      · exact decide_eq_decide.2 Iff.rfl
    refine hB.of_eq fun p ↦ ?_
    rcases p with ⟨⟨i, env⟩, q | q⟩
    · exact decide_eq_decide.2 Iff.rfl
    · exact hbridge i _

/-- Relabeled `Fin`-variable terms evaluate to ordinary realization at the cast
view. -/
theorem termRealize_relabel_view (i : ℕ) (env : Tuple ℕ) {k : ℕ}
    (hk : env.length = k) (t : L.Term (Fin k)) :
    K.termRealize ((i, env), t.relabel Fin.val) =
      @Term.realize L ℕ (K.structureAt i) _
        (fun x : Fin k ↦ env.view (Fin.cast hk.symm x)) t := by
  letI := K.structureAt i
  show (t.relabel Fin.val).realize (envFun env) = _
  rw [Term.realize_relabel]
  congr 1
  funext x
  show (env[(x : ℕ)]?).getD 0 = env.get (Fin.cast hk.symm x)
  rw [List.getElem?_eq_getElem (show (x : ℕ) < env.length by omega)]
  rfl

/-- Valid natural-variable terms evaluate to the realization of their
restriction. -/
theorem termRealize_eq_realize_restrictVar (i : ℕ) (env : Tuple ℕ) {k : ℕ}
    (hk : env.length = k) (t : L.Term ℕ) (hv : Term.VarsBelow k t) :
    K.termRealize ((i, env), t) =
      @Term.realize L ℕ (K.structureAt i) _
        (fun x : Fin k ↦ env.view (Fin.cast hk.symm x))
        (t.restrictVar fun x ↦ (⟨x.1, hv x.1 x.2⟩ : Fin k)) := by
  letI := K.structureAt i
  show t.realize (envFun env) = _
  refine (Term.realize_restrictVar (envFun env) fun v ↦ ?_).symm
  show env.get (Fin.cast hk.symm _) = (env[(v : ℕ)]?).getD 0
  rw [List.getElem?_eq_getElem (show (v : ℕ) < env.length by
    have := hv v.1 v.2
    omega)]
  rfl

/-- The central correctness gate: two width-`k` tuples are atomically equivalent
exactly when every atomic data valid at `k` has the same realization on both. -/
theorem atomicEquivalent_iff_forall_validAtomicData (i j : ℕ) (a b : Tuple ℕ)
    (hb : b.length = a.length) :
    (@AtomicEquivalent L ℕ ℕ (K.structureAt i) (K.structureAt j) _
      a.view fun x ↦ b.view (Fin.cast hb.symm x)) ↔
    ∀ d : AtomicData L ℕ, AtomicData.ValidAt a.length d →
      (K.realizeAtomicData i a d ↔ K.realizeAtomicData j b d) := by
  constructor
  · rintro ⟨hEq, hRel⟩ d hd
    rcases d with q | ⟨⟨n, R⟩, ts⟩
    · obtain ⟨hv₁, hv₂⟩ := hd
      show K.termRealize ((i, a), q.1) = K.termRealize ((i, a), q.2) ↔
        K.termRealize ((j, b), q.1) = K.termRealize ((j, b), q.2)
      rw [K.termRealize_eq_realize_restrictVar i a rfl q.1 hv₁,
        K.termRealize_eq_realize_restrictVar i a rfl q.2 hv₂,
        K.termRealize_eq_realize_restrictVar j b hb q.1 hv₁,
        K.termRealize_eq_realize_restrictVar j b hb q.2 hv₂]
      exact hEq _ _
    · obtain ⟨hlen, hall⟩ := hd
      show Option.casesOn (motive := fun _ ↦ Prop)
          (RelationApplicationData.ofSymbolArgs?
            ((⟨n, R⟩ : L.RelationSymbol),
              ts.map fun t ↦ K.termRealize ((i, a), t))) False _ ↔
        Option.casesOn (motive := fun _ ↦ Prop)
          (RelationApplicationData.ofSymbolArgs?
            ((⟨n, R⟩ : L.RelationSymbol),
              ts.map fun t ↦ K.termRealize ((j, b), t))) False _
      rw [RelationApplicationData.ofSymbolArgs?_of_length_eq _ (by
          simpa using hlen),
        RelationApplicationData.ofSymbolArgs?_of_length_eq _ (by
          simpa using hlen)]
      show @RelationApplicationData.relMap L ℕ (K.structureAt i)
          (RelationApplicationData.equivSubtype.symm _) ↔
        @RelationApplicationData.relMap L ℕ (K.structureAt j)
          (RelationApplicationData.equivSubtype.symm _)
      rw [@RelationApplicationData.relMap_equivSubtype_symm L ℕ (K.structureAt i) _ _,
        @RelationApplicationData.relMap_equivSubtype_symm L ℕ (K.structureAt j) _ _]
      have key := hRel R fun x : Fin n ↦
        (ts[(Fin.cast hlen.symm x : Fin ts.length)]).restrictVar
          fun v ↦ ⟨v.1, hall _ (ts.getElem_mem _) v.1 v.2⟩
      refine Iff.trans ?_ (Iff.trans key ?_)
      · refine Eq.to_iff (congrArg _ (funext fun x ↦ ?_))
        rw [List.get_eq_getElem, List.getElem_map]
        exact K.termRealize_eq_realize_restrictVar i a rfl _ _
      · refine Eq.to_iff (congrArg _ (funext fun x ↦ ?_))
        rw [List.get_eq_getElem, List.getElem_map]
        exact (K.termRealize_eq_realize_restrictVar j b hb _ _).symm
  · intro hall
    constructor
    · intro t₁ t₂
      have h : (K.termRealize ((i, a), t₁.relabel Fin.val) =
          K.termRealize ((i, a), t₂.relabel Fin.val)) ↔
          (K.termRealize ((j, b), t₁.relabel Fin.val) =
          K.termRealize ((j, b), t₂.relabel Fin.val)) :=
        hall (Sum.inl (t₁.relabel Fin.val, t₂.relabel Fin.val))
          ⟨Term.varsBelow_relabel_val t₁, Term.varsBelow_relabel_val t₂⟩
      rw [K.termRealize_relabel_view i a rfl t₁, K.termRealize_relabel_view i a rfl t₂,
        K.termRealize_relabel_view j b hb t₁, K.termRealize_relabel_view j b hb t₂]
        at h
      exact h
    · intro n R ts
      have h : (Option.casesOn (motive := fun _ ↦ Prop)
          (RelationApplicationData.ofSymbolArgs?
            ((⟨n, R⟩ : L.RelationSymbol),
              ((List.finRange n).map fun x ↦ (ts x).relabel Fin.val).map
                fun t ↦ K.termRealize ((i, a), t))) False fun d ↦
            @RelationApplicationData.relMap L ℕ (K.structureAt i) d) ↔
          (Option.casesOn (motive := fun _ ↦ Prop)
          (RelationApplicationData.ofSymbolArgs?
            ((⟨n, R⟩ : L.RelationSymbol),
              ((List.finRange n).map fun x ↦ (ts x).relabel Fin.val).map
                fun t ↦ K.termRealize ((j, b), t))) False fun d ↦
            @RelationApplicationData.relMap L ℕ (K.structureAt j) d) :=
        hall (Sum.inr (⟨n, R⟩,
            (List.finRange n).map fun x ↦ (ts x).relabel Fin.val))
          ⟨by simp [RelationSymbol.arity], by
            intro t ht
            obtain ⟨x, -, rfl⟩ := List.mem_map.1 ht
            exact Term.varsBelow_relabel_val (ts x)⟩
      rw [RelationApplicationData.ofSymbolArgs?_of_length_eq _ (by
          simp [RelationSymbol.arity]),
        RelationApplicationData.ofSymbolArgs?_of_length_eq _ (by
          simp [RelationSymbol.arity])] at h
      have h' : @RelationApplicationData.relMap L ℕ (K.structureAt i)
          (RelationApplicationData.equivSubtype.symm _) ↔
          @RelationApplicationData.relMap L ℕ (K.structureAt j)
            (RelationApplicationData.equivSubtype.symm _) := h
      rw [@RelationApplicationData.relMap_equivSubtype_symm L ℕ (K.structureAt i) _ _,
        @RelationApplicationData.relMap_equivSubtype_symm L ℕ (K.structureAt j) _ _]
        at h'
      refine Iff.trans ?_ (Iff.trans h' ?_)
      · refine Eq.to_iff (congrArg _ (funext fun x ↦ ?_))
        rw [List.get_eq_getElem, List.getElem_map, List.getElem_map,
          List.getElem_finRange]
        exact (K.termRealize_relabel_view i a rfl _).symm
      · refine Eq.to_iff (congrArg _ (funext fun x ↦ ?_))
        rw [List.get_eq_getElem, List.getElem_map, List.getElem_map,
          List.getElem_finRange]
        exact K.termRealize_relabel_view j b hb _

end ComputableAgeIn

end FirstOrder.Language
