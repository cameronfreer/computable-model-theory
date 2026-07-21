/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureLimit
import ComputableModelTheory.ModelTheory.Computable.CeStructureChainAudit
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for the semantic direct limit

Named acceptance tests for the quotient descent, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it via
`scripts/run-audit-modules.sh`.

Abstract gates: the computation laws of the limit structure on representatives, the
graph characterization of function values, and the stage-injection package —
injectivity on stage domains, step and transport compatibility, commutation with
function interpretations, exact transfer of relations, and the limit being the union
of its stages.

Concrete gates reuse the two non-inclusion shift chains of the chain audit: in the
path-graph chain, mixed-stage representatives are identified across stages by
transport and their limit adjacency descends to the quotient structure; in the
successor chain, the limit successor of a stage-2 image is a stage-0 image.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

section AbstractGates

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (D : CeStructureChainIn O L)

/-- Gate: the computation laws of the limit structure on representatives, and the
graph characterization of function values. -/
theorem test_limitStructure_computation {n : ℕ} (f : L.Functions n)
    (R : L.Relations n) (v : Fin n → D.Rep) (out : D.Rep) :
    (@Structure.funMap L D.Limit D.limitStructure n f (fun k ↦ ⟦v k⟧)
        = ⟦D.limFunRep f v⟧) ∧
      (@Structure.RelMap L D.Limit D.limitStructure n R (fun k ↦ ⟦v k⟧)
        ↔ D.LimRelHolds R (fun k ↦ (v k).1)) ∧
      (@Structure.funMap L D.Limit D.limitStructure n f (fun k ↦ ⟦v k⟧) = ⟦out⟧ ↔
        D.LimFunGraph f (fun k ↦ (v k).1) out.1) :=
  ⟨D.limitStructure_funMap_eq f v, D.limitStructure_relMap_iff R v,
    D.limitStructure_funMap_eq_iff f v out⟩

/-- Gate: stage injections are injective on stage domains and compatible with steps
and transport. -/
theorem test_stageIntoLimit_compat {i j x y x₂ : ℕ} (hij : i ≤ j)
    (hx : x ∈ (D.stageAt i).domain) (hx₂ : x₂ ∈ (D.stageAt i).domain)
    (hy : y ∈ (D.stageAt j).domain) (htrans : y ∈ D.transportTo i j x)
    (heq : D.stageIntoLimit i x hx = D.stageIntoLimit i x₂ hx₂) :
    x = x₂ ∧ D.stageIntoLimit i x hx = D.stageIntoLimit j y hy :=
  ⟨D.stageIntoLimit_injective hx hx₂ heq,
    D.stageIntoLimit_transport hij hx hy htrans⟩

/-- Gate: stage injections are homomorphisms for functions and embeddings for
relations, and every limit element is a stage image. -/
theorem test_stageIntoLimit_structure {i n : ℕ} (f : L.Functions n)
    (R : L.Relations n) (v : Fin n → ℕ) (hv : ∀ k, v k ∈ (D.stageAt i).domain)
    (q : D.Limit) :
    (@Structure.funMap L D.Limit D.limitStructure n f
          (fun k ↦ D.stageIntoLimit i (v k) (hv k))
        = D.stageIntoLimit i (@Structure.funMap L ℕ (D.stageAt i).str n f v)
            ((D.stageAt i).domain_closed n f v hv)) ∧
      (@Structure.RelMap L D.Limit D.limitStructure n R
          (fun k ↦ D.stageIntoLimit i (v k) (hv k))
        ↔ @Structure.RelMap L ℕ (D.stageAt i).str n R v) ∧
      ∃ (j z : ℕ) (hz : z ∈ (D.stageAt j).domain), q = D.stageIntoLimit j z hz :=
  ⟨D.stageIntoLimit_funMap f v hv, D.stageIntoLimit_relMap R v hv,
    D.exists_stageIntoLimit q⟩

end AbstractGates

section ConcreteGates

variable (O : Set (ℕ →. ℕ))

/-- Concrete gate: transport identifies representatives across stages in the quotient
— `3` at stage 0 and `5` at stage 2 are the same limit element of the path-graph
shift chain. -/
theorem test_pathShift_stage_collapse :
    (pathShiftChain O).stageIntoLimit 0 3 ⟨3, rfl⟩
      = (pathShiftChain O).stageIntoLimit 2 5 ⟨5, rfl⟩ :=
  (pathShiftChain O).stageIntoLimit_transport (by omega) ⟨3, rfl⟩ ⟨5, rfl⟩
    (by
      show (5 : ℕ) ∈ (pathShiftChain O).transportTo 0 2 3
      exact (pathShiftChain O).toDomainChain.transportTo_trans (by omega) (by omega)
        ((pathShiftChain O).toDomainChain.step_mem_transportTo_succ (Part.mem_some _))
        ((pathShiftChain O).toDomainChain.step_mem_transportTo_succ
          (Part.mem_some _)))

/-- Concrete gate: the limit adjacency of the mixed-stage representatives descends to
the quotient structure. -/
theorem test_pathShift_limit_adjacent :
    @Structure.RelMap Language.graph ((pathShiftChain O).Limit)
      (pathShiftChain O).limitStructure 2 (.adj : Language.graph.Relations 2)
      (fun k ↦ (pathShiftChain O).stageIntoLimit
        ((![(0, 3), (1, 5)] : Fin 2 → ℕ × ℕ) k).1
        ((![(0, 3), (1, 5)] : Fin 2 → ℕ × ℕ) k).2
        (match k with
          | ⟨0, _⟩ => ⟨3, rfl⟩
          | ⟨1, _⟩ => ⟨5, rfl⟩)) :=
  ((pathShiftChain O).limitStructure_relMap_iff (.adj : Language.graph.Relations 2)
    (fun k ↦ ⟨(![(0, 3), (1, 5)] : Fin 2 → ℕ × ℕ) k,
      match k with
        | ⟨0, _⟩ => ⟨3, rfl⟩
        | ⟨1, _⟩ => ⟨5, rfl⟩⟩)).2 (test_pathShift_relHolds O)

/-- Concrete gate: the limit successor of the stage-2 image of `7` is the stage-0
image of `6` — the quotient descent of the cross-stage function gate. -/
theorem test_succShift_limit_funMap :
    @Structure.funMap succLang ((succShiftChain O).Limit)
      (succShiftChain O).limitStructure 1 SuccFunctions.succ
      (fun _ ↦ (succShiftChain O).stageIntoLimit 2 7 ⟨7, rfl⟩)
      = (succShiftChain O).stageIntoLimit 0 6 ⟨6, rfl⟩ :=
  ((succShiftChain O).limitStructure_funMap_eq_iff SuccFunctions.succ
    (fun _ ↦ ⟨(2, 7), ⟨7, rfl⟩⟩) ⟨(0, 6), ⟨6, rfl⟩⟩).2
    (test_succShift_funGraph_cross O)

end ConcreteGates

end FirstOrder.Language

open FirstOrder.Language

#assert_standard_axioms test_limitStructure_computation
#assert_standard_axioms test_stageIntoLimit_compat
#assert_standard_axioms test_stageIntoLimit_structure
#assert_standard_axioms test_pathShift_stage_collapse
#assert_standard_axioms test_pathShift_limit_adjacent
#assert_standard_axioms test_succShift_limit_funMap
