/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureChain
import ComputableModelTheory.ModelTheory.Computable.SuccExample
import ComputableModelTheory.ModelTheory.Computable.GraphExample

/-!
# Shift-chain examples

Two c.e. structure chains whose steps `x ↦ x + 1` are genuinely **not** inclusions, together
with their concrete semantic facts. Sitting in the import spine rather than in an audit module
is deliberate: several audit modules consume these fixtures, and an audit module's `.olean` is
never built, so an audit that imports another audit cannot be checked.

* The **successor shift chain** (constant `succStructure` stages) exercises a function applied
  to a representative from a *later* stage than its output representative, and — under the
  trivial decidable-stages certificate — a function output computed at stage 2 that requires
  normalization to be identified with its stage-0 representative.
* The **path-graph shift chain** (constant `pathGraphStructure` stages) checks a relation on
  representatives *from different stages* after moving both to a strictly later common stage,
  refutes a non-adjacent pair, and transfers a verdict along pointwise `limEquiv`.

The axiom-policy gates for these facts live in `CeStructureChainAudit`, which asserts them on
the declarations imported from here.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

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
