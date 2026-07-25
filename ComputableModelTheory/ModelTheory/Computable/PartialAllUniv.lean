/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialAgeSemantics

/-!
# The all-carrier-`ℕ` recovery

`ComputableAgeIn` is the all-carrier-`ℕ` fragment of CHMM Definition 2.1, embedded into it by
`ComputableAgeIn.toPartialAge`. This file runs the other way on the sub-class where the
embedding's image lives: a Definition 2.1 family every one of whose carriers is all of `ℕ`
gives back a `ComputableAgeIn`.

This is a **recovery, not an inverse**, and the statements here are deliberately extensional:

* the recovered `structureAt` and `gens` *are* the originals, definitionally;
* the partial evaluators are totalized uniformly — on an all-`ℕ` carrier every argument tuple
  is on-domain, so `funEval`/`relEval` are everywhere defined and
  `RecursiveIn.computableIn_get` turns them into total computable interpretations;
* the round trip is asserted only up to **memberwise equivalence** and `SameClass`
  (`toComputableAge_memberEquiv`, `toComputableAge_sameClass`).

No equality is claimed between the original stored enumerator and evaluators and the ones the
round trip produces, and none holds: the recovered family enumerates by the identity and
evaluates by a totalized `get`, which need not be the stored witnesses even when they compute
the same structure. That is exactly why this is not a literal inverse.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace PartialAgeIn

variable (B : PartialAgeIn O L)

/-- A Definition 2.1 family whose carriers are all of `ℕ` — the sub-class on which the all-ℕ
fragment is recoverable. -/
def AllDomainsUniv : Prop :=
  ∀ i, B.domainAt i = Set.univ

variable {B}

theorem mem_domainAt_of_allDomainsUniv (h : B.AllDomainsUniv) (i x : ℕ) :
    x ∈ B.domainAt i :=
  (h i) ▸ Set.mem_univ x

/-- On an all-`ℕ` carrier every argument tuple is on-domain, so the partial function
evaluator is everywhere defined. -/
theorem funEval_dom (h : B.AllDomainsUniv) (p : ℕ × FunctionApplicationData L ℕ) :
    (B.funEval p.1 p.2).Dom :=
  (B.funEval_correct p.1 p.2 fun k ↦ mem_domainAt_of_allDomainsUniv h p.1 (p.2.args k)).fst

theorem relEval_dom (h : B.AllDomainsUniv) (p : ℕ × RelationApplicationData L ℕ) :
    (B.relEval p.1 p.2).Dom :=
  (B.relEval_correct p.1 p.2
    fun k ↦ mem_domainAt_of_allDomainsUniv h p.1 (p.2.args k)).choose_spec.1.fst

/-- The totalized function evaluator computes the interpretation. -/
theorem funEval_get (h : B.AllDomainsUniv) (p : ℕ × FunctionApplicationData L ℕ) :
    (B.funEval p.1 p.2).get (funEval_dom h p) =
      @FunctionApplicationData.funMap L ℕ (B.structureAt p.1) p.2 :=
  (Part.get_eq_of_mem
    (B.funEval_correct p.1 p.2 fun k ↦ mem_domainAt_of_allDomainsUniv h p.1 (p.2.args k))
    _).symm ▸ rfl

/-- The totalized relation decider decides the interpretation. -/
theorem relEval_get_iff (h : B.AllDomainsUniv) (p : ℕ × RelationApplicationData L ℕ) :
    ((B.relEval p.1 p.2).get (relEval_dom h p) = true) ↔
      @RelationApplicationData.relMap L ℕ (B.structureAt p.1) p.2 := by
  obtain ⟨b, hb, hiff⟩ :=
    B.relEval_correct p.1 p.2 fun k ↦ mem_domainAt_of_allDomainsUniv h p.1 (p.2.args k)
  rw [Part.get_eq_of_mem hb]
  exact hiff

/-- **The recovery.** A Definition 2.1 family with all carriers `ℕ` is a `ComputableAgeIn`,
with the same structure data and the same generators; the interpretations are the totalized
partial evaluators. -/
noncomputable def toComputableAge (h : B.AllDomainsUniv) : ComputableAgeIn O L where
  structureAt := B.structureAt
  gens := B.gens
  gens_computableIn := B.gens_computableIn
  funMap_computableIn :=
    (B.funEval_recursiveIn.computableIn_get (funEval_dom h)).of_eq (funEval_get h)
  relMap_computablePredIn := by
    have hdec : ∀ q : ℕ × RelationApplicationData L ℕ,
        Decidable (@RelationApplicationData.relMap L ℕ (B.structureAt q.1) q.2) :=
      fun q ↦ decidable_of_iff _ (relEval_get_iff h q)
    refine ⟨hdec, ?_⟩
    refine (B.relEval_recursiveIn.computableIn_get (relEval_dom h)).of_eq fun p ↦ ?_
    by_cases hp : @RelationApplicationData.relMap L ℕ (B.structureAt p.1) p.2
    · rw [@decide_eq_true _ (hdec p) hp]
      exact (relEval_get_iff h p).2 hp
    · rw [@decide_eq_false _ (hdec p) hp, ← Bool.not_eq_true]
      exact fun hc ↦ hp ((relEval_get_iff h p).1 hc)
  generates := fun i ↦
    (@Tuple.generates_iff L ℕ (B.structureAt i) (B.gens i)).2 fun x ↦
      ((B.generates i x).1 ⟨_, (mem_domainAt_of_allDomainsUniv h i x).choose_spec⟩).imp
        fun _ hT ↦ hT.symm

@[simp]
theorem toComputableAge_structureAt (h : B.AllDomainsUniv) (i : ℕ) :
    (B.toComputableAge h).structureAt i = B.structureAt i :=
  rfl

@[simp]
theorem toComputableAge_gens (h : B.AllDomainsUniv) (i : ℕ) :
    (B.toComputableAge h).gens i = B.gens i :=
  rfl

/-! ### The round trip, up to memberwise equivalence

Nothing below asserts an equality of stored data. The recovered family re-enumerates by the
identity and re-evaluates by a totalized `get`; only the *members* are claimed to match. -/

/-- Each member of the round trip is first-order equivalent to the original member, by the
identity on values: same structure data, and both carriers are all of `ℕ`. -/
noncomputable def toComputableAge_memberEquiv (h : B.AllDomainsUniv) (i : ℕ) :
    ((B.toComputableAge h).toPartialAge.memberAt i).domain ≃[L] (B.memberAt i).domain :=
  PartialCePresentationIn.eqDomainEquiv rfl
    (by rw [PartialAgeIn.memberAt_domain, PartialAgeIn.memberAt_domain,
      (B.toComputableAge h).toPartialAge_domainAt, h i])

/-- The round trip represents the same isomorphism classes. -/
theorem toComputableAge_sameClass (h : B.AllDomainsUniv) :
    (B.toComputableAge h).toPartialAge.SameClass B :=
  ⟨fun i ↦ ⟨i, ⟨toComputableAge_memberEquiv h i⟩⟩,
    fun j ↦ ⟨j, ⟨(toComputableAge_memberEquiv h j).symm⟩⟩⟩

end PartialAgeIn

end FirstOrder.Language
