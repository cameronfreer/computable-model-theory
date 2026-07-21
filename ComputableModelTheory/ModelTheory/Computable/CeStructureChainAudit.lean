/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureChain
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

section SuccShift

variable (O : Set (ℕ →. ℕ))

/-- The successor shift chain: every stage is the (all-ℕ) successor presentation, and
each step is `x ↦ x + 1` — a genuine non-inclusion embedding, since
`S(x + 1) = S(x) + 1`. -/
noncomputable def succShiftChain : CeStructureChainIn O succLang where
  stageAt _ := ComputableStructureIn.toCePresentation
    { inst := succStructure, isComputable := succ_isComputable }
  enum_uniform := ComputableIn.snd
  step _ x := Part.some (x + 1)
  step_recursiveIn :=
    ((Primrec.succ.to_comp.computableIn (O := O)).comp ComputableIn.snd :
      ComputableIn O fun p : ℕ × ℕ ↦ p.2 + 1)
  step_mem := fun _ x _ ↦ ⟨x + 1, Part.mem_some _, ⟨x + 1, rfl⟩⟩
  step_injOn := fun _ x₁ x₂ y _ _ h₁ h₂ ↦ by
    have e₁ := Part.mem_some_iff.1 h₁
    have e₂ := Part.mem_some_iff.1 h₂
    omega
  step_funMap := fun i n f v w hv hw ↦ by
    match n, f, v, w, hw with
    | 1, .succ, v, w, hw =>
      have h0 : w 0 = v 0 + 1 := Part.mem_some_iff.1 (hw 0)
      exact Part.mem_some_iff.2 (by change w 0 + 1 = v 0 + 1 + 1; omega)
    | 0, f, _, _, _ => exact isEmptyElim f
    | n + 2, f, _, _, _ => exact isEmptyElim f
  step_relMap := fun _ _ R _ _ _ _ ↦ isEmptyElim R

/-- One transport step along a shift chain, phrased for reuse in the gates below. -/
private theorem succShift_transport_succ (i x : ℕ) :
    (x + 1) ∈ (succShiftChain O).transportTo i (i + 1) x :=
  (succShiftChain O).toDomainChain.step_mem_transportTo_succ (Part.mem_some _)

/-- Concrete gate: the limit successor applied to the representative `(2, 7)` — a
stage-2 representative — yields the stage-0 representative `(0, 6)`: the input and
output representatives live at different stages. -/
theorem test_succShift_funGraph_cross :
    (succShiftChain O).LimFunGraph SuccFunctions.succ (fun _ : Fin 1 ↦ (2, 7)) (0, 6) := by
  refine ⟨2, fun _ ↦ 7, fun _ ↦ le_refl 2, ?_, ?_⟩
  · intro k
    rw [CeStructureChainIn.transportTo, CeDomainChainIn.transportTo_self]
    exact Part.mem_some _
  · -- The stage-2 value `(2, 8)` is `limEquiv` to `(0, 6)`: transport `6` up twice.
    refine ⟨8, ?_, ?_⟩
    · show (8 : ℕ) ∈ (succShiftChain O).transportTo 2 (max 2 0) 8
      rw [show max 2 0 = 2 from rfl, CeStructureChainIn.transportTo,
        CeDomainChainIn.transportTo_self]
      exact Part.mem_some _
    · show (8 : ℕ) ∈ (succShiftChain O).transportTo 0 (max 2 0) 6
      exact (succShiftChain O).toDomainChain.transportTo_trans (by omega) (by omega)
        (succShift_transport_succ O 0 6) (succShift_transport_succ O 1 7)

/-- The (trivial) decidable-stages certificate of the successor shift chain. -/
def succShiftCert : (succShiftChain O).toDomainChain.DecidableStagesCertificate where
  memB _ _ := true
  memB_computableIn := ComputableIn.const true
  memB_iff := fun _ x ↦ ⟨fun _ ↦ ⟨x, rfl⟩, fun _ ↦ rfl⟩

/-- Concrete gate: the function output `(2, 8)` computed at stage 2 **requires
normalization** to be identified with the early representative `(0, 6)` — under the
certificate the two normalize to the same canonical representative. -/
theorem test_succShift_output_normalization :
    CeDomainChainIn.normalize (succShiftCert O) (2, 8)
      = CeDomainChainIn.normalize (succShiftCert O) (0, 6) := by
  refine (CeDomainChainIn.normalize_eq_iff (succShiftCert O) ⟨8, rfl⟩ ⟨6, rfl⟩).2 ?_
  refine ⟨8, ?_, ?_⟩
  · show (8 : ℕ) ∈ (succShiftChain O).transportTo 2 (max 2 0) 8
    rw [show max 2 0 = 2 from rfl, CeStructureChainIn.transportTo,
      CeDomainChainIn.transportTo_self]
    exact Part.mem_some _
  · show (8 : ℕ) ∈ (succShiftChain O).transportTo 0 (max 2 0) 6
    exact (succShiftChain O).toDomainChain.transportTo_trans (by omega) (by omega)
      (succShift_transport_succ O 0 6) (succShift_transport_succ O 1 7)

end SuccShift

section PathShift

variable (O : Set (ℕ →. ℕ))

/-- The shift step preserves and reflects path-graph adjacency. -/
private theorem pathShift_relMap {n : ℕ} (R : Language.graph.Relations n)
    (v w : Fin n → ℕ) (hw : ∀ k, w k = v k + 1) :
    @Structure.RelMap Language.graph ℕ pathGraphStructure n R w ↔
      @Structure.RelMap Language.graph ℕ pathGraphStructure n R v :=
  match n, R, v, w, hw with
  | 2, .adj, v, w, hw => by
    have h0 := hw 0
    have h1 := hw 1
    change (w 0 + 1 = w 1 ∨ w 1 + 1 = w 0) ↔ (v 0 + 1 = v 1 ∨ v 1 + 1 = v 0)
    omega
  | 0, R, _, _, _ => isEmptyElim R
  | 1, R, _, _, _ => isEmptyElim R
  | _ + 3, R, _, _, _ => isEmptyElim R

/-- The path-graph shift chain: every stage is the (all-ℕ) path-graph presentation,
and each step is `x ↦ x + 1` — a genuine non-inclusion embedding, since adjacency is
shift-invariant. -/
noncomputable def pathShiftChain : CeStructureChainIn O Language.graph where
  stageAt _ := ComputableStructureIn.toCePresentation
    { inst := pathGraphStructure, isComputable := pathGraph_isComputable }
  enum_uniform := ComputableIn.snd
  step _ x := Part.some (x + 1)
  step_recursiveIn :=
    ((Primrec.succ.to_comp.computableIn (O := O)).comp ComputableIn.snd :
      ComputableIn O fun p : ℕ × ℕ ↦ p.2 + 1)
  step_mem := fun _ x _ ↦ ⟨x + 1, Part.mem_some _, ⟨x + 1, rfl⟩⟩
  step_injOn := fun _ x₁ x₂ y _ _ h₁ h₂ ↦ by
    have e₁ := Part.mem_some_iff.1 h₁
    have e₂ := Part.mem_some_iff.1 h₂
    omega
  step_funMap := fun _ _ f _ _ _ _ ↦ isEmptyElim f
  step_relMap := fun i n R v w hv hw ↦
    pathShift_relMap R v w fun k ↦ Part.mem_some_iff.1 (hw k)

private theorem pathShift_transport_succ (i x : ℕ) :
    (x + 1) ∈ (pathShiftChain O).transportTo i (i + 1) x :=
  (pathShiftChain O).toDomainChain.step_mem_transportTo_succ (Part.mem_some _)

/-- The representative tuple mixing stages: `3` presented at stage 0 and `5` presented
at stage 1. -/
private def mixedPair : Fin 2 → ℕ × ℕ := ![(0, 3), (1, 5)]

private theorem mixedPair_tupleMem : (pathShiftChain O).TupleMem (mixedPair) := fun k ↦
  match k with
  | ⟨0, _⟩ => ⟨3, rfl⟩
  | ⟨1, _⟩ => ⟨5, rfl⟩

/-- Both mixed-stage representatives transported to the strictly later common stage 2:
`3` climbs two steps to `5`, and `5` climbs one step to `6`. -/
private theorem mixedPair_transport (k : Fin 2) :
    (![5, 6] : Fin 2 → ℕ) k
      ∈ (pathShiftChain O).transportTo ((mixedPair) k).1 2 ((mixedPair) k).2 :=
  match k with
  | ⟨0, _⟩ => by
      show (5 : ℕ) ∈ (pathShiftChain O).transportTo 0 2 3
      exact (pathShiftChain O).toDomainChain.transportTo_trans (by omega) (by omega)
        (pathShift_transport_succ O 0 3) (pathShift_transport_succ O 1 4)
  | ⟨1, _⟩ => by
      show (6 : ℕ) ∈ (pathShiftChain O).transportTo 1 2 5
      exact pathShift_transport_succ O 1 5

private theorem mixedPair_stages (k : Fin 2) : ((mixedPair) k).1 ≤ 2 :=
  match k with
  | ⟨0, _⟩ => Nat.zero_le 2
  | ⟨1, _⟩ => Nat.le_succ 1

/-- Concrete gate: the limit adjacency of representatives **from different stages**
(`3` at stage 0, `5` at stage 1), checked after moving both to the strictly later
common stage 2, where they realize as the consecutive pair `5, 6`. -/
theorem test_pathShift_relHolds :
    (pathShiftChain O).LimRelHolds (.adj : Language.graph.Relations 2) (mixedPair) :=
  ⟨2, ![5, 6], mixedPair_stages, mixedPair_transport O, Or.inl rfl⟩

/-- Concrete negative gate: `3` at stage 0 and `6` at stage 1 are not limit-adjacent —
refuted through the single-realization characterization at the common stage 2. -/
theorem test_pathShift_not_relHolds :
    ¬(pathShiftChain O).LimRelHolds (.adj : Language.graph.Relations 2)
      ![(0, 3), (1, 6)] := by
  have htuple : (pathShiftChain O).TupleMem ![(0, 3), (1, 6)] := fun k ↦
    match k with
    | ⟨0, _⟩ => ⟨3, rfl⟩
    | ⟨1, _⟩ => ⟨6, rfl⟩
  have hsrc : ∀ k : Fin 2, (![5, 7] : Fin 2 → ℕ) k
      ∈ (pathShiftChain O).transportTo ((![(0, 3), (1, 6)] : Fin 2 → ℕ × ℕ) k).1 2
        ((![(0, 3), (1, 6)] : Fin 2 → ℕ × ℕ) k).2 := fun k ↦
    match k with
    | ⟨0, _⟩ => by
        show (5 : ℕ) ∈ (pathShiftChain O).transportTo 0 2 3
        exact (pathShiftChain O).toDomainChain.transportTo_trans (by omega) (by omega)
          (pathShift_transport_succ O 0 3) (pathShift_transport_succ O 1 4)
    | ⟨1, _⟩ => by
        show (7 : ℕ) ∈ (pathShiftChain O).transportTo 1 2 6
        exact pathShift_transport_succ O 1 6
  have hm : ∀ k : Fin 2, ((![(0, 3), (1, 6)] : Fin 2 → ℕ × ℕ) k).1 ≤ 2 := fun k ↦
    match k with
    | ⟨0, _⟩ => Nat.zero_le 2
    | ⟨1, _⟩ => Nat.le_succ 1
  rw [(pathShiftChain O).limRelHolds_iff_realization
    (.adj : Language.graph.Relations 2) htuple hm hsrc]
  exact fun h ↦ (by decide : ¬((5 : ℕ) + 1 = 7 ∨ 7 + 1 = 5)) h

/-- Concrete gate: the limit-adjacency verdict transfers along pointwise `limEquiv` —
`(2, 5)` re-presents `3` at stage 2 and `(0, 4)` re-presents `5`'s limit element at
stage 0, and the transported tuple is still adjacent. -/
theorem test_pathShift_invariance :
    (pathShiftChain O).LimRelHolds (.adj : Language.graph.Relations 2)
      ![(2, 5), (0, 4)] := by
  have htuple' : (pathShiftChain O).TupleMem ![(2, 5), (0, 4)] := fun k ↦
    match k with
    | ⟨0, _⟩ => ⟨5, rfl⟩
    | ⟨1, _⟩ => ⟨4, rfl⟩
  have heq : ∀ k : Fin 2, (pathShiftChain O).toDomainChain.limEquiv
      ((mixedPair) k) ((![(2, 5), (0, 4)] : Fin 2 → ℕ × ℕ) k) := fun k ↦
    match k with
    | ⟨0, _⟩ => ⟨5,
        by
          show (5 : ℕ) ∈ (pathShiftChain O).transportTo 0 (max 0 2) 3
          exact (pathShiftChain O).toDomainChain.transportTo_trans (by omega)
            (by omega) (pathShift_transport_succ O 0 3)
            (pathShift_transport_succ O 1 4),
        by
          show (5 : ℕ) ∈ (pathShiftChain O).transportTo 2 (max 0 2) 5
          rw [show max 0 2 = 2 from rfl, CeStructureChainIn.transportTo,
            CeDomainChainIn.transportTo_self]
          exact Part.mem_some _⟩
    | ⟨1, _⟩ => ⟨5,
        by
          show (5 : ℕ) ∈ (pathShiftChain O).transportTo 1 (max 1 0) 5
          rw [show max 1 0 = 1 from rfl, CeStructureChainIn.transportTo,
            CeDomainChainIn.transportTo_self]
          exact Part.mem_some _,
        by
          show (5 : ℕ) ∈ (pathShiftChain O).transportTo 0 (max 1 0) 4
          exact pathShift_transport_succ O 0 4⟩
  exact ((pathShiftChain O).limRelHolds_iff_of_limEquiv
    (.adj : Language.graph.Relations 2) (mixedPair_tupleMem O) htuple' heq).1
    (test_pathShift_relHolds O)

end PathShift

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
