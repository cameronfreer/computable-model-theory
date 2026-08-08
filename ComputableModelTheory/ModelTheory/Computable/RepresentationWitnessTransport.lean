/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.RepresentationConjugation
import ComputableModelTheory.ModelTheory.Computable.PartialCJEP
import ComputableModelTheory.ModelTheory.Computable.PartialTheorem28

/-!
# Transporting witness interfaces along a representation isomorphism

Which of the effective witness properties are invariant under `RepresentationIsoIn` is decided by
one question: does the property's contract mention **recorded generators of the family being
asserted about**, in a position the transport cannot control?

`PartialCJEPIn` does not, and transports. Its selector is total, its soundness clause is a pair of
realization statements at the selector's own output tuples, and those output tuples are exactly
what a transport produces. Every clause is therefore reachable, and this file supplies the
transport in the only direction that needs proving — the other follows by `symm`.

## Why CHP does not transport

`MappedPartialCHPIn` asks, for a carrier-valid query `s`, for an index `c` with
`(B.gens c).length = s.length` and an embedding carrying `B.gens c` coordinatewise onto **`s`**.
The query is *input*. A transport, by contrast, produces a datum whose range tuple is the image of
the selected member's generators, and the source family's witness controls only `A.gens` — nothing
relates those to `B.gens (forward.indexMap c)`, not even in length.

The failure is not subtle. Over a one-constant language with the singleton structure `{5}`, let `A`
record member `i` with `List.replicate i 5` and let `B` record every member with `[5]`. Both
present the same class, and constant index maps make them representation-isomorphic with identity
structure maps. `A` has CHP — select the member whose generator length matches the query — while
`B` fails it outright at the valid query `s = []`, since every candidate has exactly one recorded
generator and the length equation is unsatisfiable.

So CHP transport is not stated here. If it is needed later it should carry an explicit cover
condition, `∀ i, r.sourceGensImage i = B.gens (r.indexMap i)` — genuine generator-respecting
equality, not equality of lengths — and bidirectional invariance would need it on both covers.
That hypothesis is strictly stronger than `RepresentationIsoIn` and belongs outside it: CHMM
Definition 2.3 deliberately does not contain it.

`PartialCAPIn` is unsupported for the separate reasons recorded in `RepresentationConjugation`.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- Read a `PartialRealizesAt` back into the coordinate form the witness interfaces state, at an
index and tuple given by *equations* rather than definitionally.

The interfaces name `(sel …).apexIdx` and `(sel …).leftImage` literally, and a transported
selector's output is a `Part.get` — reducible to neither. Taking the two as equational
hypotheses lets them be substituted away inside this lemma, where they are variables. -/
theorem partialRealizesAt_coords {B : PartialAgeIn O L} {G : PotentialEmbeddingData} {i q q' : ℕ}
    {t : Tuple ℕ} {g : (B.memberAt i).domain ↪[L] (B.memberAt q).domain}
    (hg : B.PartialRealizesAt G i q g) (hq : q' = q) (ht : t = G.rangeTuple) :
    ∃ hlen : (B.gens i).length = t.length,
      ∃ F : (B.memberAt i).domain ↪[L] (B.memberAt q').domain,
        ∀ k : Fin (B.gens i).length,
          ((F ⟨(B.gens i).get k, B.gens_mem_domainAt k⟩ : (B.memberAt q').domain) : ℕ) =
            t.get (Fin.cast hlen k) :=
  hq ▸ ht ▸ ⟨hg.2.2.choose, g, hg.2.2.choose_spec⟩

namespace RepresentationIsoIn

variable {A B : PartialAgeIn O L} (r : RepresentationIsoIn E A B)

/-! ### One leg

A leg of a joint-embedding datum is potential embedding data out of the pulled-back query member,
so `transportOutOf` applies with both index equations holding on the nose. -/

/-- Transport one leg into the queried member `e`: the source family's leg runs out of
`backward.indexMap e`, and the result runs out of `e` itself. -/
noncomputable def transportLeg (e p : ℕ) (t : Tuple ℕ) : Part PotentialEmbeddingData :=
  r.transportOutOf e p (PotentialEmbeddingData.ofTriple (r.backward.indexMap e, p, t))

theorem transportLeg_dom {e p : ℕ} {t : Tuple ℕ}
    (h : A.PartialIsEmbedding
      (PotentialEmbeddingData.ofTriple (r.backward.indexMap e, p, t))) :
    (r.transportLeg e p t).Dom :=
  r.transportOutOf_dom h rfl rfl

theorem transportLeg_realizesAt {e p : ℕ} {t : Tuple ℕ}
    {f : (A.memberAt (r.backward.indexMap e)).domain ↪[L] (A.memberAt p).domain}
    (hf : A.PartialRealizes
      (PotentialEmbeddingData.ofTriple (r.backward.indexMap e, p, t)) f)
    {G : PotentialEmbeddingData} (hG : G ∈ r.transportLeg e p t) :
    B.PartialRealizesAt G e (r.forward.indexMap p)
      (PartialCeIsoIn.conjugate (r.backward.isoAt e).symm (r.forward.isoAt p) f) :=
  r.transportOutOf_realizesAt ⟨rfl, rfl, hf⟩ hG

/-! ### The whole datum

Both legs share the source apex, so both land at `forward.indexMap` of it — the transported datum
is a genuine joint embedding, not two unrelated embeddings. -/

/-- Transport a joint-embedding datum answering the queried pair `(i, j)`, given the source
family's answer `J` at the pulled-back pair. -/
noncomputable def transportJoint (i j : ℕ) (J : PartialJointEmbeddingData) :
    Part PartialJointEmbeddingData :=
  (r.transportLeg i J.apexIdx J.leftImage).bind fun GL ↦
    (r.transportLeg j J.apexIdx J.rightImage).map fun GR ↦
      PartialJointEmbeddingData.ofTriple
        (r.forward.indexMap J.apexIdx, GL.rangeTuple, GR.rangeTuple)

theorem mem_transportJoint_iff {i j : ℕ} {J K : PartialJointEmbeddingData} :
    K ∈ r.transportJoint i j J ↔
      ∃ GL ∈ r.transportLeg i J.apexIdx J.leftImage,
        ∃ GR ∈ r.transportLeg j J.apexIdx J.rightImage,
          K = PartialJointEmbeddingData.ofTriple
            (r.forward.indexMap J.apexIdx, GL.rangeTuple, GR.rangeTuple) := by
  rw [transportJoint]
  constructor
  · intro h
    obtain ⟨GL, hGL, h'⟩ := Part.mem_bind_iff.1 h
    obtain ⟨GR, hGR, rfl⟩ := (Part.mem_map_iff _).1 h'
    exact ⟨GL, hGL, GR, hGR, rfl⟩
  · rintro ⟨GL, hGL, GR, hGR, rfl⟩
    exact Part.mem_bind_iff.2 ⟨GL, hGL, (Part.mem_map_iff _).2 ⟨GR, hGR, rfl⟩⟩

theorem transportJoint_dom {i j : ℕ} {J : PartialJointEmbeddingData}
    (hL : A.PartialIsEmbedding
      (PotentialEmbeddingData.ofTriple (r.backward.indexMap i, J.apexIdx, J.leftImage)))
    (hR : A.PartialIsEmbedding
      (PotentialEmbeddingData.ofTriple (r.backward.indexMap j, J.apexIdx, J.rightImage))) :
    (r.transportJoint i j J).Dom := by
  obtain ⟨GL, hGL⟩ := Part.dom_iff_mem.1 (r.transportLeg_dom hL)
  obtain ⟨GR, hGR⟩ := Part.dom_iff_mem.1 (r.transportLeg_dom hR)
  exact Part.dom_iff_mem.2 ⟨_, r.mem_transportJoint_iff.2 ⟨GL, hGL, GR, hGR, rfl⟩⟩

/-! ### Computability

Uniform in the query pair and the datum, drawing on `transportOutOf_uniform_recursiveIn`. The
packaging steps go through pinned adapters, as everywhere the `ofEquiv`-encoded data types are
built inside a larger expression. -/

private def legTriple (r : RepresentationIsoIn E A B) (z : (ℕ × ℕ) × Tuple ℕ) :
    ℕ × ℕ × Tuple ℕ :=
  (r.backward.indexMap z.1.1, z.1.2, z.2)

private theorem legData_computableIn :
    ComputableIn E fun z : (ℕ × ℕ) × Tuple ℕ ↦
      PotentialEmbeddingData.ofTriple (r.backward.indexMap z.1.1, z.1.2, z.2) :=
  ComputableIn.comp (O := E) (α := (ℕ × ℕ) × Tuple ℕ) (β := ℕ × ℕ × Tuple ℕ)
    (σ := PotentialEmbeddingData)
    (f := PotentialEmbeddingData.ofTriple) (g := r.legTriple)
    PotentialEmbeddingData.ofTriple_computableIn
    ((((r.backward.indexMap_computableIn.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
      ((ComputableIn.snd.comp ComputableIn.fst).pair ComputableIn.snd))).of_eq fun _ ↦ rfl)

theorem transportLeg_recursiveIn (hOE : O ⊆ E) :
    RecursiveIn E fun z : (ℕ × ℕ) × Tuple ℕ ↦ r.transportLeg z.1.1 z.1.2 z.2 :=
  RecursiveIn.comp (O := E) (α := (ℕ × ℕ) × Tuple ℕ)
    (β := (ℕ × ℕ) × PotentialEmbeddingData) (σ := PotentialEmbeddingData)
    (f := fun q : (ℕ × ℕ) × PotentialEmbeddingData ↦ r.transportOutOf q.1.1 q.1.2 q.2)
    (g := fun z : (ℕ × ℕ) × Tuple ℕ ↦
      (z.1, PotentialEmbeddingData.ofTriple (r.backward.indexMap z.1.1, z.1.2, z.2)))
    (r.transportOutOf_uniform_recursiveIn hOE)
    (ComputableIn.fst.pair r.legData_computableIn)

private def jointTriple (r : RepresentationIsoIn E A B)
    (v : (((ℕ × ℕ) × PartialJointEmbeddingData) × PotentialEmbeddingData) ×
      PotentialEmbeddingData) : ℕ × Tuple ℕ × Tuple ℕ :=
  (r.forward.indexMap v.1.1.2.apexIdx, v.1.2.rangeTuple, v.2.rangeTuple)

private theorem jointPack_computableIn :
    ComputableIn E fun v : (((ℕ × ℕ) × PartialJointEmbeddingData) × PotentialEmbeddingData) ×
        PotentialEmbeddingData ↦
      PartialJointEmbeddingData.ofTriple
        (r.forward.indexMap v.1.1.2.apexIdx, v.1.2.rangeTuple, v.2.rangeTuple) :=
  ComputableIn.comp (O := E)
    (α := (((ℕ × ℕ) × PartialJointEmbeddingData) × PotentialEmbeddingData) ×
      PotentialEmbeddingData)
    (β := ℕ × Tuple ℕ × Tuple ℕ) (σ := PartialJointEmbeddingData)
    (f := PartialJointEmbeddingData.ofTriple) (g := r.jointTriple)
    PartialJointEmbeddingData.primrec_ofTriple.to_comp.computableIn
    ((((r.forward.indexMap_computableIn.comp
          (PartialJointEmbeddingData.primrec_apexIdx.to_comp.computableIn.comp
            (ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)))).pair
        ((PotentialEmbeddingData.rangeTuple_computable.comp
            (ComputableIn.snd.comp ComputableIn.fst)).pair
          (PotentialEmbeddingData.rangeTuple_computable.comp ComputableIn.snd)))).of_eq
      fun _ ↦ rfl)

theorem transportJoint_recursiveIn (hOE : O ⊆ E) :
    RecursiveIn E fun z : (ℕ × ℕ) × PartialJointEmbeddingData ↦
      r.transportJoint z.1.1 z.1.2 z.2 := by
  have hleg := r.transportLeg_recursiveIn hOE
  have hL : RecursiveIn E fun z : (ℕ × ℕ) × PartialJointEmbeddingData ↦
      r.transportLeg z.1.1 z.2.apexIdx z.2.leftImage :=
    RecursiveIn.comp (O := E) (α := (ℕ × ℕ) × PartialJointEmbeddingData)
      (β := (ℕ × ℕ) × Tuple ℕ) (σ := PotentialEmbeddingData)
      (f := fun w : (ℕ × ℕ) × Tuple ℕ ↦ r.transportLeg w.1.1 w.1.2 w.2)
      (g := fun z : (ℕ × ℕ) × PartialJointEmbeddingData ↦
        ((z.1.1, z.2.apexIdx), z.2.leftImage))
      hleg
      (((ComputableIn.fst.comp ComputableIn.fst).pair
          (PartialJointEmbeddingData.primrec_apexIdx.to_comp.computableIn.comp
            ComputableIn.snd)).pair
        (PartialJointEmbeddingData.primrec_leftImage.to_comp.computableIn.comp
          ComputableIn.snd))
  have hR : RecursiveIn E fun w : ((ℕ × ℕ) × PartialJointEmbeddingData) ×
      PotentialEmbeddingData ↦
      r.transportLeg w.1.1.2 w.1.2.apexIdx w.1.2.rightImage :=
    RecursiveIn.comp (O := E)
      (α := ((ℕ × ℕ) × PartialJointEmbeddingData) × PotentialEmbeddingData)
      (β := (ℕ × ℕ) × Tuple ℕ) (σ := PotentialEmbeddingData)
      (f := fun w : (ℕ × ℕ) × Tuple ℕ ↦ r.transportLeg w.1.1 w.1.2 w.2)
      (g := fun w : ((ℕ × ℕ) × PartialJointEmbeddingData) × PotentialEmbeddingData ↦
        ((w.1.1.2, w.1.2.apexIdx), w.1.2.rightImage))
      hleg
      ((((ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst)).pair
          (PartialJointEmbeddingData.primrec_apexIdx.to_comp.computableIn.comp
            (ComputableIn.snd.comp ComputableIn.fst))).pair
        (PartialJointEmbeddingData.primrec_rightImage.to_comp.computableIn.comp
          (ComputableIn.snd.comp ComputableIn.fst))))
  -- shaped as `bind (fun GL ↦ map)`, matching `transportJoint`; the `(bind).map` association
  -- is a different term and forces `whnf` to chase the whole pipeline
  exact RecursiveIn.bind hL (RecursiveIn.map hR r.jointPack_computableIn.to₂).to₂

end RepresentationIsoIn

/-! ### The transport theorem

Stated in one direction; the other is this applied to `r.symm`, since symmetry of a
representation isomorphism is just the swap of its two covers. -/

namespace PartialAgeIn

/-- **The computable joint embedding property transports along a representation isomorphism.**

Every clause is reachable because CJEP never measures the target family's recorded generators
against anything the transport does not produce: its output tuples *are* the transported images.
Contrast `MappedPartialCHPIn`, whose contract pins the range tuple to a query supplied from
outside — see the module header. -/
theorem PartialCJEPIn.transport {A B : PartialAgeIn O L} (r : RepresentationIsoIn E A B)
    (hOE : O ⊆ E) (h : A.PartialCJEPIn E) : B.PartialCJEPIn E := by
  obtain ⟨selA, hselA, hspecA⟩ := h
  have hLeft : ∀ i j : ℕ, A.PartialIsEmbedding (PotentialEmbeddingData.ofTriple
      (r.backward.indexMap i,
        (selA (r.backward.indexMap i) (r.backward.indexMap j)).apexIdx,
        (selA (r.backward.indexMap i) (r.backward.indexMap j)).leftImage)) := by
    intro i j
    obtain ⟨⟨hlen, Fi, hFi⟩, -⟩ := hspecA (r.backward.indexMap i) (r.backward.indexMap j)
    exact ⟨Fi, hlen, hFi⟩
  have hRight : ∀ i j : ℕ, A.PartialIsEmbedding (PotentialEmbeddingData.ofTriple
      (r.backward.indexMap j,
        (selA (r.backward.indexMap i) (r.backward.indexMap j)).apexIdx,
        (selA (r.backward.indexMap i) (r.backward.indexMap j)).rightImage)) := by
    intro i j
    obtain ⟨-, ⟨hlen, Fj, hFj⟩⟩ := hspecA (r.backward.indexMap i) (r.backward.indexMap j)
    exact ⟨Fj, hlen, hFj⟩
  have hdom : ∀ i j : ℕ,
      (r.transportJoint i j (selA (r.backward.indexMap i) (r.backward.indexMap j))).Dom :=
    fun i j ↦ r.transportJoint_dom (hLeft i j) (hRight i j)
  refine ⟨fun i j ↦
    (r.transportJoint i j (selA (r.backward.indexMap i) (r.backward.indexMap j))).get
      (hdom i j), ?_, ?_⟩
  · have hpull : ComputableIn E fun p : ℕ × ℕ ↦
        selA (r.backward.indexMap p.1) (r.backward.indexMap p.2) :=
      hselA.comp ((r.backward.indexMap_computableIn.comp ComputableIn.fst).pair
        (r.backward.indexMap_computableIn.comp ComputableIn.snd))
    have hpart : RecursiveIn E fun p : ℕ × ℕ ↦
        r.transportJoint p.1 p.2 (selA (r.backward.indexMap p.1) (r.backward.indexMap p.2)) :=
      RecursiveIn.comp (O := E) (α := ℕ × ℕ)
        (β := (ℕ × ℕ) × PartialJointEmbeddingData) (σ := PartialJointEmbeddingData)
        (f := fun z : (ℕ × ℕ) × PartialJointEmbeddingData ↦ r.transportJoint z.1.1 z.1.2 z.2)
        (g := fun p : ℕ × ℕ ↦
          (p, selA (r.backward.indexMap p.1) (r.backward.indexMap p.2)))
        (r.transportJoint_recursiveIn hOE) (ComputableIn.id.pair hpull)
    exact hpart.computableIn_get _
  · intro i j
    dsimp only
    obtain ⟨GL, hGL, GR, hGR, hK⟩ :=
      r.mem_transportJoint_iff.1 (Part.get_mem (hdom i j))
    obtain ⟨⟨hlenL, Fi, hFi⟩, ⟨hlenR, Fj, hFj⟩⟩ :=
      hspecA (r.backward.indexMap i) (r.backward.indexMap j)
    exact ⟨partialRealizesAt_coords
        (r.transportLeg_realizesAt (f := Fi) ⟨hlenL, hFi⟩ hGL) (by rw [hK]; rfl) (by rw [hK]; rfl),
      partialRealizesAt_coords
        (r.transportLeg_realizesAt (f := Fj) ⟨hlenR, hFj⟩ hGR) (by rw [hK]; rfl) (by rw [hK]; rfl)⟩

/-- **Both directions.** The reverse is the same theorem at `r.symm`. -/
theorem PartialCJEPIn.transport_iff {A B : PartialAgeIn O L} (r : RepresentationIsoIn E A B)
    (hOE : O ⊆ E) : A.PartialCJEPIn E ↔ B.PartialCJEPIn E :=
  ⟨PartialCJEPIn.transport r hOE, PartialCJEPIn.transport r.symm hOE⟩

end PartialAgeIn

end FirstOrder.Language
