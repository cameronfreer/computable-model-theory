/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ChainPresentation
import ComputableModelTheory.ModelTheory.Computable.CeStructureChainAudit
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for coded chain presentations

Named acceptance tests for the certified coded presentation, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it via
`scripts/run-audit-modules.sh`.

Abstract gates: the coded presentation's domain is exactly the canonical codes and is
computably decidable; coded function values are canonical again (closure) and decode
to raw limit values (normalized-output semantics); the coded relation is the raw
limit relation on canonical codes; off-canonical inputs receive junk by the guarded
`dite`, never a fabricated value; and the inclusion into the c.e. level preserves the
domain.

Concrete gates run on the two non-inclusion shift chains with their trivial
certificates and constant-stage uniform evaluators: the coded successor of the
canonical code of `(0, 5)` decodes `limEquiv` to `(0, 6)`, and the coded path-graph
adjacency holds on the canonical codes of the mixed-stage adjacent pair.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

section AbstractGates

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (D : CeStructureChainIn O L)
variable (cert : D.toDomainChain.DecidableStagesCertificate)

/-- Gate: the coded presentation's domain is exactly the canonical codes, and it is
computably decidable. -/
theorem test_codedPresentation_domain (U : D.UniformEvaluatorsIn) :
    (D.codedPresentation cert U).domain = {c | CeStructureChainIn.IsCanonicalCode D cert c} ∧
      ComputablePredIn O fun c ↦ c ∈ (D.codedPresentation cert U).domain :=
  ⟨D.codedPresentation_domain cert U,
    (D.codedPresentation cert U).domain_computablePredIn⟩

/-- Gate: coded function values on canonical arguments are canonical (closure) and
decode to raw limit values of the decoded arguments (normalized-output semantics);
the coded relation is the raw limit relation. -/
theorem test_coded_semantics {n : ℕ} (f : L.Functions n) (R : L.Relations n)
    (v : Fin n → ℕ) (h : ∀ k, CeStructureChainIn.IsCanonicalCode D cert (v k)) :
    CeStructureChainIn.IsCanonicalCode D cert (D.codedFunMap cert f v) ∧
      D.LimFunGraph f (fun k ↦ Nat.unpair (v k))
        (Nat.unpair (D.codedFunMap cert f v)) ∧
      (D.codedRelMap cert R v ↔ D.LimRelHolds R fun k ↦ Nat.unpair (v k)) :=
  ⟨D.codedFunMap_isCanonical cert f v h, D.codedFunMap_limFunGraph cert f v h,
    D.codedRelMap_iff cert R v h⟩

/-- Gate: off the canonical domain, the coded function returns junk by the guard and
the coded relation fails — no fabricated values. -/
theorem test_coded_junk {n : ℕ} (f : L.Functions n) (R : L.Relations n)
    (v : Fin n → ℕ) (h : ¬∀ k, CeStructureChainIn.IsCanonicalCode D cert (v k)) :
    D.codedFunMap cert f v = 0 ∧ ¬D.codedRelMap cert R v := by
  constructor
  · rw [CeStructureChainIn.codedFunMap, dif_neg h]
  · exact fun hc ↦ h hc.1

/-- Gate: the inclusion of the coded presentation into the c.e. level preserves the
domain. -/
theorem test_coded_ce_inclusion (U : D.UniformEvaluatorsIn) :
    (D.codedPresentation cert U).toCePresentation.domain
      = {c | CeStructureChainIn.IsCanonicalCode D cert c} :=
  ((D.codedPresentation cert U).toCePresentation_domain).trans
    (D.codedPresentation_domain cert U)

/-- Gate: normalized stage embeddings are injective on stage domains, commute with
transport, and exhaust the coded carrier (the union of stages). -/
theorem test_stageIntoCoded_carrier {i j x x₂ y c : ℕ} (hij : i ≤ j)
    (hx : x ∈ (D.stageAt i).domain) (hx₂ : x₂ ∈ (D.stageAt i).domain)
    (hy : y ∈ D.transportTo i j x)
    (heq : D.stageIntoCoded cert i x = D.stageIntoCoded cert i x₂)
    (hc : CeStructureChainIn.IsCanonicalCode D cert c) :
    x = x₂ ∧ D.stageIntoCoded cert i x = D.stageIntoCoded cert j y ∧
      ∃ i' x', x' ∈ (D.stageAt i').domain ∧ c = D.stageIntoCoded cert i' x' :=
  ⟨D.stageIntoCoded_injective cert hx hx₂ heq,
    D.stageIntoCoded_transport cert hij hx hy,
    D.stageIntoCoded_surjective cert hc⟩

/-- Gate: normalized stage embeddings are homomorphisms for functions and embeddings
for relations into the coded structure. -/
theorem test_stageIntoCoded_structure {i n : ℕ} (f : L.Functions n)
    (R : L.Relations n) (v : Fin n → ℕ) (hv : ∀ k, v k ∈ (D.stageAt i).domain) :
    (D.codedFunMap cert f (fun k ↦ D.stageIntoCoded cert i (v k))
        = D.stageIntoCoded cert i (@Structure.funMap L ℕ (D.stageAt i).str n f v)) ∧
      (D.codedRelMap cert R (fun k ↦ D.stageIntoCoded cert i (v k))
        ↔ @Structure.RelMap L ℕ (D.stageAt i).str n R v) :=
  ⟨D.stageIntoCoded_funMap cert f v hv, D.stageIntoCoded_relMap cert R v hv⟩

/-- Gate: the initial-segment conversion exists, only through the c.e. inclusion and
the rank machinery — a nonuniform corollary, never uniform data. -/
theorem test_coded_initialSegment (U : D.UniformEvaluatorsIn) :
    ∃ Q : ComputableInitialSegmentPresentationIn O L,
      Q.str = (D.codedPresentation cert U).toCePresentation.rankStr ∧
        Q.domain = Set.range (D.codedPresentation cert U).toCePresentation.posRank :=
  D.exists_initialSegment_coded cert U

end AbstractGates

section ConcreteGates

variable (O : Set (ℕ →. ℕ))

/-- Constant-stage uniform evaluators for the successor shift chain. -/
theorem succShiftUniform : (succShiftChain O).UniformEvaluatorsIn where
  funEval_uniform :=
    ((succShiftChain O).stageAt 0).funEval_recursiveIn.comp ComputableIn.snd
  relEval_uniform :=
    ((succShiftChain O).stageAt 0).relEval_recursiveIn.comp ComputableIn.snd

/-- Constant-stage uniform evaluators for the path-graph shift chain. -/
theorem pathShiftUniform : (pathShiftChain O).UniformEvaluatorsIn where
  funEval_uniform :=
    ((pathShiftChain O).stageAt 0).funEval_recursiveIn.comp ComputableIn.snd
  relEval_uniform :=
    ((pathShiftChain O).stageAt 0).relEval_recursiveIn.comp ComputableIn.snd

/-- The trivial decidable-stages certificate of the path-graph shift chain. -/
def pathShiftCert : (pathShiftChain O).toDomainChain.DecidableStagesCertificate where
  memB _ _ := true
  memB_computableIn := ComputableIn.const true
  memB_iff := fun _ x ↦ ⟨fun _ ↦ ⟨x, rfl⟩, fun _ ↦ rfl⟩

/-- The canonical code of a valid pair. -/
noncomputable def canonCodeOf {C : CeDomainChainIn O}
    (cert : C.DecidableStagesCertificate) (p : ℕ × ℕ) : ℕ :=
  Nat.pair (CeDomainChainIn.normalize cert p).1 (CeDomainChainIn.normalize cert p).2

private theorem canonCodeOf_isCanonical (p : ℕ × ℕ)
    (hp : (succShiftChain O).toDomainChain.limMem p) :
    CeStructureChainIn.IsCanonicalCode (succShiftChain O) (succShiftCert O)
      (canonCodeOf O (succShiftCert O) p) :=
  (succShiftChain O).isCanonicalCode_pair (succShiftCert O)
    ((succShiftChain O).isCanonicalPair_normalize (succShiftCert O) hp)

private theorem canonCodeOf_unpair_equiv (p : ℕ × ℕ)
    (hp : (succShiftChain O).toDomainChain.limMem p) :
    (succShiftChain O).toDomainChain.limEquiv p
      (Nat.unpair (canonCodeOf O (succShiftCert O) p)) := by
  rw [canonCodeOf, Nat.unpair_pair]
  exact (CeDomainChainIn.normalize_spec (succShiftCert O) hp).2

/-- Concrete gate: the coded successor of the canonical code of `(0, 5)` decodes
`limEquiv` to `(0, 6)` — the normalized output denotes the right limit element. -/
theorem test_succShift_coded_funMap :
    (succShiftChain O).toDomainChain.limEquiv
      (Nat.unpair ((succShiftChain O).codedFunMap (succShiftCert O)
        SuccFunctions.succ (fun _ : Fin 1 ↦ canonCodeOf O (succShiftCert O) (0, 5))))
      (0, 6) := by
  set c := canonCodeOf O (succShiftCert O) (0, 5) with hc
  have hval : (succShiftChain O).toDomainChain.limMem ((0 : ℕ), (5 : ℕ)) := ⟨5, rfl⟩
  have hcanon : ∀ k : Fin 1, CeStructureChainIn.IsCanonicalCode (succShiftChain O)
      (succShiftCert O) ((fun _ : Fin 1 ↦ c) k) :=
    fun _ ↦ canonCodeOf_isCanonical O (0, 5) hval
  have hgraph := (succShiftChain O).codedFunMap_limFunGraph (succShiftCert O)
    SuccFunctions.succ (fun _ : Fin 1 ↦ c) hcanon
  -- The base graph at the raw representative: `S(5) = 6` at stage 0.
  have hbase : (succShiftChain O).LimFunGraph SuccFunctions.succ
      (fun _ : Fin 1 ↦ ((0 : ℕ), (5 : ℕ))) (0, 6) := by
    refine ⟨0, fun _ ↦ 5, fun _ ↦ le_refl 0, ?_, ?_⟩
    · intro k
      rw [CeStructureChainIn.transportTo, CeDomainChainIn.transportTo_self]
      exact Part.mem_some _
    · exact (succShiftChain O).toDomainChain.limEquiv_refl _
  -- Transfer the base graph to the canonical-code tuple, then compare outputs.
  have hbase' : (succShiftChain O).LimFunGraph SuccFunctions.succ
      (fun _ : Fin 1 ↦ Nat.unpair c) (0, 6) :=
    (succShiftChain O).limFunGraph_of_limEquiv SuccFunctions.succ
      (fun _ ↦ hval) (fun k ↦ ((hcanon k).limMem))
      (fun _ ↦ canonCodeOf_unpair_equiv O (0, 5) hval)
      ⟨6, rfl⟩ ⟨6, rfl⟩ ((succShiftChain O).toDomainChain.limEquiv_refl _) hbase
  have hvalout : (succShiftChain O).toDomainChain.limMem
      (Nat.unpair ((succShiftChain O).codedFunMap (succShiftCert O)
        SuccFunctions.succ (fun _ : Fin 1 ↦ c))) :=
    ((succShiftChain O).codedFunMap_isCanonical (succShiftCert O)
      SuccFunctions.succ (fun _ : Fin 1 ↦ c) hcanon).limMem
  exact (succShiftChain O).limFunGraph_functional SuccFunctions.succ
    (fun k ↦ (hcanon k).limMem) hgraph hbase' hvalout ⟨6, rfl⟩

/-- Concrete gate: the coded path-graph adjacency holds on the canonical codes of the
mixed-stage adjacent pair `(0, 3)` and `(1, 5)`. -/
theorem test_pathShift_coded_relMap :
    (pathShiftChain O).codedRelMap (pathShiftCert O)
      (.adj : Language.graph.Relations 2)
      ![Nat.pair (CeDomainChainIn.normalize (pathShiftCert O) (0, 3)).1
          (CeDomainChainIn.normalize (pathShiftCert O) (0, 3)).2,
        Nat.pair (CeDomainChainIn.normalize (pathShiftCert O) (1, 5)).1
          (CeDomainChainIn.normalize (pathShiftCert O) (1, 5)).2] := by
  have hval₀ : (pathShiftChain O).toDomainChain.limMem ((0 : ℕ), (3 : ℕ)) := ⟨3, rfl⟩
  have hval₁ : (pathShiftChain O).toDomainChain.limMem ((1 : ℕ), (5 : ℕ)) := ⟨5, rfl⟩
  have hcanon : ∀ k : Fin 2, CeStructureChainIn.IsCanonicalCode (pathShiftChain O)
      (pathShiftCert O)
      ((![Nat.pair (CeDomainChainIn.normalize (pathShiftCert O) (0, 3)).1
          (CeDomainChainIn.normalize (pathShiftCert O) (0, 3)).2,
        Nat.pair (CeDomainChainIn.normalize (pathShiftCert O) (1, 5)).1
          (CeDomainChainIn.normalize (pathShiftCert O) (1, 5)).2] : Fin 2 → ℕ) k) :=
    fun k ↦ match k with
    | ⟨0, _⟩ => (pathShiftChain O).isCanonicalCode_pair (pathShiftCert O)
        ((pathShiftChain O).isCanonicalPair_normalize (pathShiftCert O) hval₀)
    | ⟨1, _⟩ => (pathShiftChain O).isCanonicalCode_pair (pathShiftCert O)
        ((pathShiftChain O).isCanonicalPair_normalize (pathShiftCert O) hval₁)
  refine ⟨hcanon, ?_⟩
  refine ((pathShiftChain O).limRelHolds_iff_of_limEquiv
    (.adj : Language.graph.Relations 2)
    (v := ![(0, 3), (1, 5)]) (fun k ↦ match k with
      | ⟨0, _⟩ => hval₀
      | ⟨1, _⟩ => hval₁)
    (fun k ↦ (hcanon k).limMem)
    (fun k ↦ match k with
      | ⟨0, _⟩ => by
          show (pathShiftChain O).toDomainChain.limEquiv (0, 3)
            (Nat.unpair (Nat.pair
              (CeDomainChainIn.normalize (pathShiftCert O) (0, 3)).1
              (CeDomainChainIn.normalize (pathShiftCert O) (0, 3)).2))
          rw [Nat.unpair_pair]
          exact (CeDomainChainIn.normalize_spec (pathShiftCert O) hval₀).2
      | ⟨1, _⟩ => by
          show (pathShiftChain O).toDomainChain.limEquiv (1, 5)
            (Nat.unpair (Nat.pair
              (CeDomainChainIn.normalize (pathShiftCert O) (1, 5)).1
              (CeDomainChainIn.normalize (pathShiftCert O) (1, 5)).2))
          rw [Nat.unpair_pair]
          exact (CeDomainChainIn.normalize_spec (pathShiftCert O) hval₁).2)).1
    (test_pathShift_relHolds O)

/-- Concrete gate: transport identifies normalized stage images across stages — `3`
at stage 0 and `5` at stage 2 share their canonical code in the path-graph chain. -/
theorem test_pathShift_stageIntoCoded_collapse :
    (pathShiftChain O).stageIntoCoded (pathShiftCert O) 0 3
      = (pathShiftChain O).stageIntoCoded (pathShiftCert O) 2 5 :=
  (pathShiftChain O).stageIntoCoded_transport (pathShiftCert O) (by omega)
    ⟨3, rfl⟩ (by
      show (5 : ℕ) ∈ (pathShiftChain O).transportTo 0 2 3
      exact (pathShiftChain O).toDomainChain.transportTo_trans (by omega) (by omega)
        ((pathShiftChain O).toDomainChain.step_mem_transportTo_succ (Part.mem_some _))
        ((pathShiftChain O).toDomainChain.step_mem_transportTo_succ
          (Part.mem_some _)))

end ConcreteGates

end FirstOrder.Language

open FirstOrder.Language

#assert_standard_axioms test_codedPresentation_domain
#assert_standard_axioms test_coded_semantics
#assert_standard_axioms test_coded_junk
#assert_standard_axioms test_coded_ce_inclusion
#assert_standard_axioms succShiftUniform
#assert_standard_axioms pathShiftUniform
#assert_standard_axioms test_succShift_coded_funMap
#assert_standard_axioms test_pathShift_coded_relMap
#assert_standard_axioms test_stageIntoCoded_carrier
#assert_standard_axioms test_stageIntoCoded_structure
#assert_standard_axioms test_pathShift_stageIntoCoded_collapse
#assert_standard_axioms test_coded_initialSegment
