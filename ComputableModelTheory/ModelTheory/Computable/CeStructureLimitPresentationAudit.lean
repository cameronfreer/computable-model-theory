/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureLimitPresentation
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the Level-1 extensional limit presentation

The row that records the design is `test_funMap_always_accepted`: **every** function application
returns an accepted code, including applications to codes that name nothing. That is why no
defensive guard belongs in the structure, and why the carrier hypotheses in the three presentation
laws do no computational work. Without this row, a later reader could reasonably add a guard and
find that everything still compiles.

`test_limitPresentation_domain` pins the carrier as exactly the accepted codes — no membership test
in the enumeration and no fallback value, since canonicalization's range *is* the accepted set.

The last two rows are the semantic interface. Everything above this file should reach the limit
through them, leaving `Part.get` and the evaluator internals below the boundary.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace CeStructureChainIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (D : CeStructureChainIn O L)

/-- **Every function application returns an accepted code**, unconditionally. -/
theorem test_funMap_always_accepted {n : ℕ} (f : L.Functions n) (v : Fin n → ℕ) :
    D.toDomainChain.Accepted (@Structure.funMap L ℕ D.limitStr n f v) :=
  D.accepted_limitStr_funMap f v

/-- **The carrier is exactly the accepted codes** — enumerated with no test and no fallback. -/
theorem test_limitPresentation_domain (U : D.UniformEvaluatorsIn) :
    (D.limitPresentation U).domain = {n | D.toDomainChain.Accepted n} ∧
      (D.limitPresentation U).enum = D.toDomainChain.canonicalRaw :=
  ⟨D.limitPresentation_domain U, rfl⟩

/-- The presentation carries the limit structure. -/
theorem test_limitPresentation_str (U : D.UniformEvaluatorsIn) :
    (D.limitPresentation U).str = D.limitStr :=
  rfl

/-! ### The semantic interface -/

/-- Function values are the limit's, on the arguments' classes. -/
theorem test_funMap_limFunGraph {n : ℕ} (f : L.Functions n) (v : Fin n → ℕ) :
    D.LimFunGraph f (fun k ↦ D.toDomainChain.rawRep (v k))
      (D.toDomainChain.rawRep (@Structure.funMap L ℕ D.limitStr n f v)) :=
  D.limitStr_funMap_limFunGraph f v

/-- Relations are the limit's. -/
theorem test_relMap_iff_limRelHolds {n : ℕ} (R : L.Relations n) (v : Fin n → ℕ) :
    @Structure.RelMap L ℕ D.limitStr n R v ↔
      D.LimRelHolds R fun k ↦ D.toDomainChain.rawRep (v k) :=
  D.limitStr_relMap_iff_limRelHolds R v

/-! ### The stage maps at code level -/

/-- The stage map lands in the carrier, and is **injective on its stage** — which is what will make
it an embedding rather than merely a well-defined map. -/
theorem test_stageCode_accepted_and_injOn {i x y : ℕ} (hx : x ∈ (D.stageAt i).domain)
    (hy : y ∈ (D.stageAt i).domain) :
    D.toDomainChain.Accepted (D.stageCode hx) ∧
      (D.stageCode hx = D.stageCode hy → x = y) :=
  ⟨D.accepted_stageCode hx, D.stageCode_injOn hx hy⟩

/-- **Relations transfer both ways** between a stage and the limit. -/
theorem test_stageCode_relMap_iff {i n : ℕ} (R : L.Relations n) (v : Fin n → ℕ)
    (hv : ∀ k, v k ∈ (D.stageAt i).domain) :
    @Structure.RelMap L ℕ D.limitStr n R (fun k ↦ D.stageCode (hv k)) ↔
      @Structure.RelMap L ℕ (D.stageAt i).str n R v :=
  D.stageCode_relMap_iff R v hv

/-- **Functions transfer.** Proved through functionality of the limit graph plus accepted codes
being equivalent only when equal — no inverse equivalence is constructed. -/
theorem test_stageCode_funMap {i n : ℕ} (f : L.Functions n) (v : Fin n → ℕ)
    (hv : ∀ k, v k ∈ (D.stageAt i).domain) :
    D.stageCode ((D.stageAt i).domain_closed n f v hv) =
      @Structure.funMap L ℕ D.limitStr n f (fun k ↦ D.stageCode (hv k)) :=
  D.stageCode_funMap f v hv

/-! ### The bundled stage embeddings -/

/-- **The computational bridge.** The bundled embedding's value is a value of the uniformly partial
recursive stage map. Without this row the package would carry a semantic embedding and a computable
map with nothing relating them. -/
theorem test_stageEmbedding_apply_mem (U : D.UniformEvaluatorsIn) (i : ℕ)
    (x : (D.stageAt i).domain) :
    ((D.stageEmbedding U i x : (D.limitPresentation U).domain) : ℕ) ∈
      D.toDomainChain.stageIntoPart i x.1 :=
  D.stageEmbedding_apply_mem U i x

/-- **Coherence with the chain steps**, inherited from the search rather than re-derived: the two
stage maps are equal as `Part`s, so the bundled equality is `Part.mem_unique`. -/
theorem test_stageEmbedding_step (U : D.UniformEvaluatorsIn) {i x : ℕ}
    (hx : x ∈ (D.stageAt i).domain) :
    ∃ y ∈ D.toDomainChain.step i x, ∃ hy : y ∈ (D.stageAt (i + 1)).domain,
      D.stageEmbedding U i ⟨x, hx⟩ = D.stageEmbedding U (i + 1) ⟨y, hy⟩ :=
  D.stageEmbedding_step U hx

/-- **Coverage.** Every carrier element is a stage image, so the limit is the union of the stage
embeddings' ranges. -/
theorem test_exists_stageEmbedding_eq (U : D.UniformEvaluatorsIn)
    (c : (D.limitPresentation U).domain) :
    ∃ (i : ℕ) (x : ℕ) (hx : x ∈ (D.stageAt i).domain),
      D.stageEmbedding U i ⟨x, hx⟩ = c :=
  D.exists_stageEmbedding_eq U c

/-! ### Lemma 2.9 -/

/-- **Coherence at an arbitrary realized step**, not merely at a chosen one — what transport and
iteration consumers need, so that none of them repeats the single-valuedness argument. -/
theorem test_stageEmbedding_step_of_mem (U : D.UniformEvaluatorsIn) {i x y : ℕ}
    (hx : x ∈ (D.stageAt i).domain) (hy : y ∈ D.toDomainChain.step i x) :
    ∃ hy' : y ∈ (D.stageAt (i + 1)).domain,
      D.stageEmbedding U i ⟨x, hx⟩ = D.stageEmbedding U (i + 1) ⟨y, hy'⟩ :=
  D.stageEmbedding_step_of_mem U hx hy

/-- **CHMM Lemma 2.9 at Level 1**: a computable chain has an effective direct limit with uniformly
computable stage embeddings, and **no certificate** is required. -/
theorem test_lemma_2_9 (U : D.UniformEvaluatorsIn) : Nonempty D.LimitIn :=
  D.exists_limit U

/-- The package carries **both** sides of the map, tied together. A consumer can use the limit
without knowing how canonicalization is implemented. -/
theorem test_limit_ties_program_to_embedding (U : D.UniformEvaluatorsIn) (i : ℕ)
    (x : (D.stageAt i).domain) :
    (((D.toLimit U).stageEmbedding i x : ((D.toLimit U).presentation).domain) : ℕ) ∈
      (D.toLimit U).stageMap i x.1 :=
  (D.toLimit U).stageEmbedding_apply_mem i x

end CeStructureChainIn

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_funMap_always_accepted
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_limitPresentation_domain
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_limitPresentation_str
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_funMap_limFunGraph
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_relMap_iff_limRelHolds
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_stageCode_accepted_and_injOn
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_stageCode_relMap_iff
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_stageCode_funMap
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_stageEmbedding_apply_mem
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_stageEmbedding_step
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_exists_stageEmbedding_eq
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_stageEmbedding_step_of_mem
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_lemma_2_9
#assert_standard_axioms FirstOrder.Language.CeStructureChainIn.test_limit_ties_program_to_embedding
