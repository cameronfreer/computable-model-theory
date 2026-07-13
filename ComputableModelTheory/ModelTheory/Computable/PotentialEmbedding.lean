/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ComputableAge
import ComputableModelTheory.ModelTheory.Computable.AtomicEquiv

/-!
# Potential embeddings

Potential embedding data is pure code data — a domain index, a codomain index, and a
range tuple — with all proof obligations kept outside the type, so it is `Primcodable`
independently of any age. Well-formedness fixes the range tuple's width to the domain
generators'; actualness (`IsEmbedding`) is well-formedness together with atomic
equivalence of the domain generators and the range tuple, with the source structure at
`domIdx` and the target structure at `codIdx`. Malformed data is never actual.

The identity potential embedding at an index takes the indexed generator tuple as its
range and is actual. An actual potential embedding realizes: atomic equivalence yields
a generator-preserving equivalence of tuple closures (`toClosureEquiv`); the source
closure is the whole structure by its generator proof; and the target tuple closure
includes into the target presentation, giving a bundled embedding (`toEmbedding`)
carrying each generator to the corresponding range entry. Actualness is exactly the
existence of an embedding extending the tuple assignment
(`isEmbedding_iff_exists_embedding_extending_tuple`).
-/

open Encodable FirstOrder Language Language.BoundedFormula

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- Potential embedding data: a domain index, a codomain index, and a range tuple.
Pure code data with no proof obligations. -/
structure PotentialEmbeddingData where
  /-- The index of the domain object. -/
  domIdx : ℕ
  /-- The index of the codomain object. -/
  codIdx : ℕ
  /-- The intended images of the domain generators. -/
  rangeTuple : Tuple ℕ

/-- The code-level packaging of potential embedding data. -/
private def peEquiv : PotentialEmbeddingData ≃ ℕ × ℕ × List ℕ where
  toFun F := (F.domIdx, F.codIdx, F.rangeTuple)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable PotentialEmbeddingData :=
  Primcodable.ofEquiv _ peEquiv

theorem PotentialEmbeddingData.primrec_domIdx :
    Primrec PotentialEmbeddingData.domIdx :=
  (Primrec.fst.comp (Primrec.of_equiv (e := peEquiv))).of_eq fun _ ↦ rfl

theorem PotentialEmbeddingData.primrec_codIdx :
    Primrec PotentialEmbeddingData.codIdx :=
  ((Primrec.fst.comp Primrec.snd).comp
    (Primrec.of_equiv (e := peEquiv))).of_eq fun _ ↦ rfl

theorem PotentialEmbeddingData.primrec_rangeTuple :
    Primrec PotentialEmbeddingData.rangeTuple :=
  ((Primrec.snd.comp Primrec.snd).comp
    (Primrec.of_equiv (e := peEquiv))).of_eq fun _ ↦ rfl

theorem PotentialEmbeddingData.domIdx_computable :
    ComputableIn O PotentialEmbeddingData.domIdx :=
  PotentialEmbeddingData.primrec_domIdx.to_comp.computableIn

theorem PotentialEmbeddingData.codIdx_computable :
    ComputableIn O PotentialEmbeddingData.codIdx :=
  PotentialEmbeddingData.primrec_codIdx.to_comp.computableIn

theorem PotentialEmbeddingData.rangeTuple_computable :
    ComputableIn O PotentialEmbeddingData.rangeTuple :=
  PotentialEmbeddingData.primrec_rangeTuple.to_comp.computableIn

/-- The named triple → data factory (`peEquiv.symm`), used definitionally in `compData` so the
composed code triple reads literally as `(F.domIdx, G.codIdx, …)`. Naming the head does not on
its own make a `PotentialEmbeddingData`-valued composition go through: the insufficiently pinned
construction diverged at `whnf` on the `ofEquiv peEquiv` encoding. `compData_computableIn` instead
crosses `ofTriple` through `ComputableIn.encode_iff` (ℕ-valued output), the reliable route. -/
def PotentialEmbeddingData.ofTriple (p : ℕ × ℕ × Tuple ℕ) : PotentialEmbeddingData :=
  peEquiv.symm p

@[simp]
theorem PotentialEmbeddingData.ofTriple_domIdx (p : ℕ × ℕ × Tuple ℕ) :
    (PotentialEmbeddingData.ofTriple p).domIdx = p.1 :=
  rfl

@[simp]
theorem PotentialEmbeddingData.ofTriple_codIdx (p : ℕ × ℕ × Tuple ℕ) :
    (PotentialEmbeddingData.ofTriple p).codIdx = p.2.1 :=
  rfl

@[simp]
theorem PotentialEmbeddingData.ofTriple_rangeTuple (p : ℕ × ℕ × Tuple ℕ) :
    (PotentialEmbeddingData.ofTriple p).rangeTuple = p.2.2 :=
  rfl

theorem PotentialEmbeddingData.primrec_ofTriple :
    Primrec PotentialEmbeddingData.ofTriple :=
  Primrec.of_equiv_symm

theorem PotentialEmbeddingData.ofTriple_computableIn :
    ComputableIn O PotentialEmbeddingData.ofTriple :=
  PotentialEmbeddingData.primrec_ofTriple.to_comp.computableIn

namespace PotentialEmbeddingData

/-- Well-formedness relative to an age: the range tuple has the width of the domain
generators. -/
def WellFormed (F : PotentialEmbeddingData) (K : ComputableAgeIn O L) : Prop :=
  F.rangeTuple.length = (K.gens F.domIdx).length

/-- The target fixed-width view of the range tuple of well-formed data. -/
def targetView {K : ComputableAgeIn O L} (F : PotentialEmbeddingData)
    (h : F.WellFormed K) : Fin (K.gens F.domIdx).length → ℕ :=
  fun i ↦ F.rangeTuple.view (Fin.cast h.symm i)

/-- The target view does not depend on the chosen well-formedness proof. -/
theorem targetView_irrel {K : ComputableAgeIn O L} (F : PotentialEmbeddingData)
    (h h' : F.WellFormed K) : F.targetView h = F.targetView h' :=
  rfl

/-- Actualness: well-formed, and the domain generators are atomically equivalent to
the range tuple, with the source structure at `domIdx` and the target structure at
`codIdx`. -/
def IsEmbedding (F : PotentialEmbeddingData) (K : ComputableAgeIn O L) : Prop :=
  ∃ h : F.WellFormed K,
    @AtomicEquivalent L ℕ ℕ (K.structureAt F.domIdx) (K.structureAt F.codIdx) _
      (K.gens F.domIdx).view (F.targetView h)

/-- Malformed data is never actual. -/
theorem not_isEmbedding_of_not_wellFormed {K : ComputableAgeIn O L}
    {F : PotentialEmbeddingData} (hn : ¬F.WellFormed K) : ¬F.IsEmbedding K :=
  fun ⟨h, _⟩ ↦ hn h

/-- The identity potential embedding at an index: the indexed generator tuple is its
own range. -/
def id (K : ComputableAgeIn O L) (i : ℕ) : PotentialEmbeddingData :=
  ⟨i, i, K.gens i⟩

@[simp]
theorem id_domIdx (K : ComputableAgeIn O L) (i : ℕ) : (id K i).domIdx = i :=
  rfl

@[simp]
theorem id_codIdx (K : ComputableAgeIn O L) (i : ℕ) : (id K i).codIdx = i :=
  rfl

@[simp]
theorem id_rangeTuple (K : ComputableAgeIn O L) (i : ℕ) :
    (id K i).rangeTuple = K.gens i :=
  rfl

/-- The identity potential embedding is actual. -/
theorem id_isEmbedding (K : ComputableAgeIn O L) (i : ℕ) :
    (id K i).IsEmbedding K :=
  ⟨rfl, ⟨fun _ _ ↦ Iff.rfl, fun _ _ ↦ Iff.rfl⟩⟩

end PotentialEmbeddingData

/-- The closure of a fixed-width tuple in the structure at an index of an age. -/
def ComputableAgeIn.rangeClosure (K : ComputableAgeIn O L) (i : ℕ) {k : ℕ}
    (v : Fin k → ℕ) : @Substructure L ℕ (K.structureAt i) :=
  letI := K.structureAt i
  Substructure.closure L (Set.range v)

/-- The induced structure on a tuple closure, keyed on `rangeClosure` so that it is
found without an ambient structure on the carrier. -/
instance instStructureRangeClosure (K : ComputableAgeIn O L) (i : ℕ) {k : ℕ}
    (v : Fin k → ℕ) : L.Structure ↥(K.rangeClosure i v) :=
  letI := K.structureAt i
  Substructure.inducedStructure

/-- The generator-tuple closure at an index is everything. -/
theorem ComputableAgeIn.rangeClosure_gens_eq_top (K : ComputableAgeIn O L) (i : ℕ) :
    K.rangeClosure i (K.gens i).view = ⊤ := by
  letI := K.structureAt i
  show Substructure.closure L (Set.range (K.gens i).view) = ⊤
  rw [← Tuple.closure_eq]
  exact K.generates i

/-- The presentation at an index, as a structure, is its generator-tuple closure. -/
def ComputableAgeIn.topToClosure (K : ComputableAgeIn O L) (i : ℕ) :
    (K.presentationAt i).toBundled ≃[L] ↥(K.rangeClosure i (K.gens i).view) where
  toEquiv :=
    { toFun := fun x ↦ ⟨x,
        (K.rangeClosure_gens_eq_top i).symm ▸ Substructure.mem_top x⟩
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  map_fun' := fun _ _ ↦ rfl
  map_rel' := fun _ _ ↦ Iff.rfl

namespace PotentialEmbeddingData

variable {K : ComputableAgeIn O L} {F : PotentialEmbeddingData}

/-- The generator-preserving equivalence of tuple closures obtained from atomic
equivalence. -/
noncomputable def toClosureEquiv (h : F.WellFormed K)
    (hAE : @AtomicEquivalent L ℕ ℕ (K.structureAt F.domIdx)
      (K.structureAt F.codIdx) _ (K.gens F.domIdx).view (F.targetView h)) :
    ↥(K.rangeClosure F.domIdx (K.gens F.domIdx).view) ≃[L]
      ↥(K.rangeClosure F.codIdx (F.targetView h)) :=
  ((@atomicEquivalent_iff_exists_closure_equiv L ℕ ℕ
    (K.structureAt F.domIdx) (K.structureAt F.codIdx) _ _ _).1 hAE).choose

/-- The closure equivalence carries each generator to its range entry. -/
theorem toClosureEquiv_gens (h : F.WellFormed K)
    (hAE : @AtomicEquivalent L ℕ ℕ (K.structureAt F.domIdx)
      (K.structureAt F.codIdx) _ (K.gens F.domIdx).view (F.targetView h))
    (i : Fin (K.gens F.domIdx).length) :
    toClosureEquiv h hAE
        ⟨(K.gens F.domIdx).view i,
          @Substructure.subset_closure L ℕ (K.structureAt F.domIdx) _ _ ⟨i, rfl⟩⟩ =
      ⟨F.targetView h i,
        @Substructure.subset_closure L ℕ (K.structureAt F.codIdx) _ _ ⟨i, rfl⟩⟩ :=
  ((@atomicEquivalent_iff_exists_closure_equiv L ℕ ℕ
    (K.structureAt F.domIdx) (K.structureAt F.codIdx) _ _ _).1 hAE).choose_spec i

/-- The realized embedding of an actual potential embedding: the source presentation
is its generator closure, carried by the closure equivalence into the target tuple
closure, which includes into the target presentation. The bundled carriers wear the
stored structures, passed explicitly. -/
noncomputable def toEmbedding (h : F.WellFormed K)
    (hAE : @AtomicEquivalent L ℕ ℕ (K.structureAt F.domIdx)
      (K.structureAt F.codIdx) _ (K.gens F.domIdx).view (F.targetView h)) :
    @Language.Embedding L ↥(K.presentationAt F.domIdx).toBundled
      ↥(K.presentationAt F.codIdx).toBundled
      (K.structureAt F.domIdx) (K.structureAt F.codIdx) :=
  @Language.Embedding.comp L ↥(K.presentationAt F.domIdx).toBundled
    ↥(K.rangeClosure F.codIdx (F.targetView h))
    (K.structureAt F.domIdx) (instStructureRangeClosure K F.codIdx _)
    ↥(K.presentationAt F.codIdx).toBundled (K.structureAt F.codIdx)
    (@Substructure.subtype L ℕ (K.structureAt F.codIdx)
      (K.rangeClosure F.codIdx (F.targetView h)))
    (@Language.Embedding.comp L ↥(K.presentationAt F.domIdx).toBundled
      ↥(K.rangeClosure F.domIdx (K.gens F.domIdx).view)
      (K.structureAt F.domIdx) (instStructureRangeClosure K F.domIdx _)
      ↥(K.rangeClosure F.codIdx (F.targetView h))
      (instStructureRangeClosure K F.codIdx _)
      (toClosureEquiv h hAE).toEmbedding
      (K.topToClosure F.domIdx).toEmbedding)

/-- The realized embedding carries each generator to its range entry. -/
theorem toEmbedding_apply_gens (h : F.WellFormed K)
    (hAE : @AtomicEquivalent L ℕ ℕ (K.structureAt F.domIdx)
      (K.structureAt F.codIdx) _ (K.gens F.domIdx).view (F.targetView h))
    (i : Fin (K.gens F.domIdx).length) :
    toEmbedding h hAE ((K.gens F.domIdx).view i) = F.targetView h i := by
  have hx : toEmbedding h hAE ((K.gens F.domIdx).view i) =
      (↑(toClosureEquiv h hAE
        ⟨(K.gens F.domIdx).view i,
          @Substructure.subset_closure L ℕ (K.structureAt F.domIdx) _ _ ⟨i, rfl⟩⟩) :
        ℕ) := by
    simp only [toEmbedding, Embedding.comp_apply]
    rfl
  rw [hx, toClosureEquiv_gens h hAE i]

/-- An embedding extending the tuple assignment witnesses actualness. -/
theorem isEmbedding_of_embedding_extending_tuple (h : F.WellFormed K)
    (g : @Language.Embedding L ↥(K.presentationAt F.domIdx).toBundled
      ↥(K.presentationAt F.codIdx).toBundled
      (K.structureAt F.domIdx) (K.structureAt F.codIdx))
    (hg : ∀ i, g ((K.gens F.domIdx).view i) = F.targetView h i) :
    F.IsEmbedding K := by
  have hcomp : F.targetView h = ⇑g ∘ (K.gens F.domIdx).view :=
    funext fun i ↦ (hg i).symm
  have hreal : ∀ t : L.Term (Fin (K.gens F.domIdx).length),
      @Term.realize L ℕ (K.structureAt F.codIdx) _ (F.targetView h) t =
        g (@Term.realize L ℕ (K.structureAt F.domIdx) _
          ((K.gens F.domIdx).view) t) := fun t ↦ by
    rw [hcomp]
    exact HomClass.realize_term g
  refine ⟨h, ?_, ?_⟩
  · intro t₁ t₂
    constructor
    · intro he
      rw [hreal t₁, hreal t₂, he]
    · intro he
      rw [hreal t₁, hreal t₂] at he
      exact g.injective he
  · intro n R ts
    have hmr := g.map_rel' R fun i ↦
      @Term.realize L ℕ (K.structureAt F.domIdx) _ ((K.gens F.domIdx).view) (ts i)
    rw [show g.toFun = ⇑g from rfl,
      show (⇑g ∘ fun i ↦ @Term.realize L ℕ (K.structureAt F.domIdx) _
          ((K.gens F.domIdx).view) (ts i)) =
        fun i ↦ @Term.realize L ℕ (K.structureAt F.codIdx) _
          (F.targetView h) (ts i) from
        funext fun i ↦ (hreal (ts i)).symm] at hmr
    exact hmr.symm

/-- Actualness is exactly the existence of an embedding extending the tuple
assignment. -/
theorem isEmbedding_iff_exists_embedding_extending_tuple :
    F.IsEmbedding K ↔
      ∃ (h : F.WellFormed K)
        (g : @Language.Embedding L ↥(K.presentationAt F.domIdx).toBundled
          ↥(K.presentationAt F.codIdx).toBundled
          (K.structureAt F.domIdx) (K.structureAt F.codIdx)),
        ∀ i, g ((K.gens F.domIdx).view i) = F.targetView h i := by
  constructor
  · rintro ⟨h, hAE⟩
    exact ⟨h, toEmbedding h hAE, toEmbedding_apply_gens h hAE⟩
  · rintro ⟨h, g, hg⟩
    exact isEmbedding_of_embedding_extending_tuple h g hg

end PotentialEmbeddingData

end FirstOrder.Language
