/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureChain
import ComputableModelTheory.ModelTheory.Computable.ChainShiftExample
import ComputableModelTheory.ModelTheory.Computable.SuccExample
import ComputableModelTheory.ModelTheory.Computable.GraphExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for c.e. structure chains

Named acceptance tests for the structure half of effective direct limits, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it via
`scripts/run-audit-modules.sh`.

Abstract gates: transport preserves functions and preserves-and-reflects relations
on-domain; the limit function graph is total and functional up to `limEquiv` on valid
tuples; both limit operations are invariant under pointwise `limEquiv`; and the limit
relation is determined by any single admissible realization.

Concrete gates run on two shift chains whose steps `x ↦ x + 1` are genuinely not
inclusions:

* the **successor shift chain** (constant `succStructure` stages) exercises a function
  applied to a representative from a *later* stage than its output representative, and
  — under the trivial decidable-stages certificate — a function output computed at
  stage 2 that requires normalization to be identified with its stage-0 representative;
* the **path-graph shift chain** (constant `pathGraphStructure` stages) checks a
  relation on representatives *from different stages* after moving both to a strictly
  later common stage, refutes a non-adjacent pair, and transfers a verdict along
  pointwise `limEquiv`.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

section AbstractGates

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (D : CeStructureChainIn O L)

/-- Gate: transport along the derived chain preserves function interpretations and
preserves-and-reflects relation interpretations on-domain. -/
theorem test_transport_structure {i j : ℕ} (hij : i ≤ j) {n : ℕ} (f : L.Functions n)
    (R : L.Relations n) {v w : Fin n → ℕ} (hv : ∀ k, v k ∈ (D.stageAt i).domain)
    (hw : ∀ k, w k ∈ D.transportTo i j (v k)) :
    @Structure.funMap L ℕ (D.stageAt j).str n f w
        ∈ D.transportTo i j (@Structure.funMap L ℕ (D.stageAt i).str n f v) ∧
      (@Structure.RelMap L ℕ (D.stageAt j).str n R w ↔
        @Structure.RelMap L ℕ (D.stageAt i).str n R v) :=
  ⟨D.transport_funMap hij f hv hw, D.transport_relMap hij R hv hw⟩

/-- Gate: on valid tuples the limit function graph is total (with valid output) and
functional up to `limEquiv`. -/
theorem test_limFunGraph_total_functional {n : ℕ} (f : L.Functions n)
    {v : Fin n → ℕ × ℕ} (hv : D.TupleMem v) {out₁ out₂ : ℕ × ℕ}
    (h₁ : D.LimFunGraph f v out₁) (h₂ : D.LimFunGraph f v out₂)
    (hout₁ : D.toDomainChain.limMem out₁) (hout₂ : D.toDomainChain.limMem out₂) :
    (∃ out, D.LimFunGraph f v out ∧ D.toDomainChain.limMem out) ∧
      D.toDomainChain.limEquiv out₁ out₂ :=
  ⟨D.limFunGraph_total f hv, D.limFunGraph_functional f hv h₁ h₂ hout₁ hout₂⟩

/-- Gate: the limit relation is determined by any single admissible realization. -/
theorem test_limRelHolds_realization {n : ℕ} (R : L.Relations n) {v : Fin n → ℕ × ℕ}
    (hv : D.TupleMem v) {m : ℕ} {src : Fin n → ℕ} (hm : ∀ k, (v k).1 ≤ m)
    (hsrc : ∀ k, src k ∈ D.transportTo (v k).1 m (v k).2) :
    D.LimRelHolds R v ↔ @Structure.RelMap L ℕ (D.stageAt m).str n R src :=
  D.limRelHolds_iff_realization R hv hm hsrc

/-- Gate: both limit operations are invariant under pointwise `limEquiv` on valid
representatives (with `limEquiv` outputs for the function graph). -/
theorem test_lim_invariance {n : ℕ} (f : L.Functions n) (R : L.Relations n)
    {v v' : Fin n → ℕ × ℕ} {out out' : ℕ × ℕ}
    (hv : D.TupleMem v) (hv' : D.TupleMem v')
    (heq : ∀ k, D.toDomainChain.limEquiv (v k) (v' k))
    (hout : D.toDomainChain.limMem out) (hout' : D.toDomainChain.limMem out')
    (houteq : D.toDomainChain.limEquiv out out') :
    (D.LimRelHolds R v ↔ D.LimRelHolds R v') ∧
      (D.LimFunGraph f v out ↔ D.LimFunGraph f v' out') :=
  ⟨D.limRelHolds_iff_of_limEquiv R hv hv' heq,
    D.limFunGraph_iff_of_limEquiv f hv hv' heq hout hout' houteq⟩

end AbstractGates


end FirstOrder.Language

open FirstOrder.Language

#assert_standard_axioms test_transport_structure
#assert_standard_axioms test_limFunGraph_total_functional
#assert_standard_axioms test_limRelHolds_realization
#assert_standard_axioms test_lim_invariance
#assert_standard_axioms test_succShift_funGraph_cross
#assert_standard_axioms test_succShift_output_normalization
#assert_standard_axioms test_pathShift_relHolds
#assert_standard_axioms test_pathShift_not_relHolds
#assert_standard_axioms test_pathShift_invariance
