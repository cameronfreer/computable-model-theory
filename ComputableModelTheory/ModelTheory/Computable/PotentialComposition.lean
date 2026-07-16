/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CanonicalTransport

/-!
# Composition of potential embedding data

`compData K G F` composes potential embedding data by transporting `F`'s range tuple along
`G`: the domain index comes from `F`, the codomain index from `G`, and the range tuple is
`F`'s transported entry-by-entry through `G` (`transportValue`). It is total code data —
defined on all inputs — with the semantic laws (actualness, realized-embedding composition,
identity, associativity) supplied separately with their hypotheses.

Computability (`compData_computableIn`) is packaged over
`PotentialEmbeddingData × PotentialEmbeddingData`. The components and the transported tuple are
built with `ComputableIn.comp`/`pair`/`list_map`, each with its implicit *type* params
(`α`/`β`/`γ`/`σ`) **and** *function* params (`f`/`g`) pinned: result-type ascription alone does
not steer elaboration past the `PotentialEmbeddingData` encoding, and the earlier
insufficiently-pinned construction diverged at `isDefEq`/`whnf`. Pinned `PotentialEmbeddingData`
intermediates (the leaf projections and the reindexing that feeds `transportValue`) are fine;
only the *crossing* of the `ofTriple` constructor is done ℕ-valued, through
`ComputableIn.encode_iff` (`encode (ofTriple t) = encode t`, since `peEquiv`'s `right_inv` is
`rfl`). That encoded route is the reliable implementation for crossing an `ofEquiv`-encoded
constructor: it sidesteps building a `PotentialEmbeddingData`-valued composition rather than
relying on one elaborating. `transportValue` is consumed only through its computability contract
(and kept locally irreducible), so `termCodeFor` stays opaque.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace ComputableAgeIn

variable (K : ComputableAgeIn O L)

-- `transportValue` is opaque within this file so composing `transportValue_computableIn`
-- (for the mapped range tuple) compares by congruence rather than reducing the term code
-- path. (Cf. `termCodeFor` in `CanonicalTransport`.)
attribute [local irreducible] ComputableAgeIn.transportValue

/-- Total composition of potential embedding data: transport the range tuple of `F` along
`G`. The domain index is `F`'s, the codomain index is `G`'s. Defined on all data; semantic
correctness carries its own hypotheses. Assembled through the named `ofTriple` factory so the
composed code triple reads literally as `(F.domIdx, G.codIdx, …)`; `compData_computableIn`
crosses that factory via `encode_iff` (see the module docstring). -/
noncomputable def compData (G F : PotentialEmbeddingData) : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple
    (F.domIdx, G.codIdx, F.rangeTuple.map (K.transportValue G))

@[simp]
theorem compData_domIdx (G F : PotentialEmbeddingData) :
    (K.compData G F).domIdx = F.domIdx :=
  rfl

@[simp]
theorem compData_codIdx (G F : PotentialEmbeddingData) :
    (K.compData G F).codIdx = G.codIdx :=
  rfl

@[simp]
theorem compData_rangeTuple (G F : PotentialEmbeddingData) :
    (K.compData G F).rangeTuple = F.rangeTuple.map (K.transportValue G) :=
  rfl

/-- Composition is computable in the oracle, uniformly in both potential embeddings.
Elaborates within the default heartbeat budget; see the module docstring for why every
combinator's type and function parameters are pinned and why the final step uses `encode_iff`. -/
theorem compData_computableIn :
    ComputableIn O fun p : PotentialEmbeddingData × PotentialEmbeddingData ↦
      K.compData p.1 p.2 := by
  -- Gate 1: the three ℕ / `Tuple ℕ` components. Every combinator's implicit type params
  -- (`α`/`β`/`σ`) *and* function params (`f`/`g`) are pinned; result-type ascription alone
  -- does not steer elaboration past the `PotentialEmbeddingData` encoding.
  have hdom : ComputableIn O fun p : PotentialEmbeddingData × PotentialEmbeddingData ↦
      p.2.domIdx :=
    ComputableIn.comp
      (α := PotentialEmbeddingData × PotentialEmbeddingData)
      (β := PotentialEmbeddingData) (σ := ℕ)
      (f := PotentialEmbeddingData.domIdx) (g := Prod.snd)
      PotentialEmbeddingData.domIdx_computable ComputableIn.snd
  have hcod : ComputableIn O fun p : PotentialEmbeddingData × PotentialEmbeddingData ↦
      p.1.codIdx :=
    ComputableIn.comp
      (α := PotentialEmbeddingData × PotentialEmbeddingData)
      (β := PotentialEmbeddingData) (σ := ℕ)
      (f := PotentialEmbeddingData.codIdx) (g := Prod.fst)
      PotentialEmbeddingData.codIdx_computable ComputableIn.fst
  have hrange : ComputableIn O fun p : PotentialEmbeddingData × PotentialEmbeddingData ↦
      p.2.rangeTuple :=
    ComputableIn.comp
      (α := PotentialEmbeddingData × PotentialEmbeddingData)
      (β := PotentialEmbeddingData) (σ := Tuple ℕ)
      (f := PotentialEmbeddingData.rangeTuple) (g := Prod.snd)
      PotentialEmbeddingData.rangeTuple_computable ComputableIn.snd
  -- Gate 2: the transported range tuple. `hval` reindexes `transportValue_computableIn`
  -- (opaque via `transportValue`'s local irreducibility) to the mapped binary function;
  -- `list_map` then maps it, again with every type/function param pinned.
  have hval : ComputableIn O
      fun q : (PotentialEmbeddingData × PotentialEmbeddingData) × ℕ ↦
        K.transportValue q.1.1 q.2 :=
    ComputableIn.comp
      (α := (PotentialEmbeddingData × PotentialEmbeddingData) × ℕ)
      (β := PotentialEmbeddingData × ℕ) (σ := ℕ)
      (f := fun r : PotentialEmbeddingData × ℕ ↦ K.transportValue r.1 r.2)
      (g := fun q : (PotentialEmbeddingData × PotentialEmbeddingData) × ℕ ↦ (q.1.1, q.2))
      K.transportValue_computableIn
      (ComputableIn.pair
        (α := (PotentialEmbeddingData × PotentialEmbeddingData) × ℕ)
        (β := PotentialEmbeddingData) (γ := ℕ)
        (f := fun q ↦ q.1.1) (g := fun q ↦ q.2)
        (ComputableIn.comp
          (α := (PotentialEmbeddingData × PotentialEmbeddingData) × ℕ)
          (β := PotentialEmbeddingData × PotentialEmbeddingData)
          (σ := PotentialEmbeddingData)
          (f := Prod.fst) (g := Prod.fst) ComputableIn.fst ComputableIn.fst)
        ComputableIn.snd)
  have hmap : ComputableIn O fun p : PotentialEmbeddingData × PotentialEmbeddingData ↦
      p.2.rangeTuple.map (K.transportValue p.1) :=
    ComputableIn.list_map
      (α := PotentialEmbeddingData × PotentialEmbeddingData) (β := ℕ) (σ := ℕ)
      (f := fun p ↦ p.2.rangeTuple)
      (g := fun p x ↦ K.transportValue p.1 x)
      hrange hval
  -- Gate 3: assemble the triple, then cross `ofTriple` through `encode_iff`. The output stays
  -- ℕ-valued, so no `PotentialEmbeddingData`-valued composition is ever formed — `encode
  -- (ofTriple t) = encode t` definitionally (`peEquiv`'s `right_inv` is `rfl`), so the closing
  -- `of_eq` is a plain `rfl` over the code triple, never touching the encoded data head.
  have htriple : ComputableIn O fun p : PotentialEmbeddingData × PotentialEmbeddingData ↦
      (p.2.domIdx, p.1.codIdx, p.2.rangeTuple.map (K.transportValue p.1)) :=
    ComputableIn.pair
      (α := PotentialEmbeddingData × PotentialEmbeddingData)
      (β := ℕ) (γ := ℕ × Tuple ℕ)
      (f := fun p ↦ p.2.domIdx)
      (g := fun p ↦ (p.1.codIdx, p.2.rangeTuple.map (K.transportValue p.1)))
      hdom
      (ComputableIn.pair
        (α := PotentialEmbeddingData × PotentialEmbeddingData)
        (β := ℕ) (γ := Tuple ℕ)
        (f := fun p ↦ p.1.codIdx)
        (g := fun p ↦ p.2.rangeTuple.map (K.transportValue p.1))
        hcod hmap)
  have henc : ComputableIn O fun p : PotentialEmbeddingData × PotentialEmbeddingData ↦
      encode (K.compData p.1 p.2) :=
    (ComputableIn.comp
      (α := PotentialEmbeddingData × PotentialEmbeddingData)
      (β := ℕ × ℕ × Tuple ℕ) (σ := ℕ)
      (f := fun t ↦ encode t)
      (g := fun p ↦ (p.2.domIdx, p.1.codIdx, p.2.rangeTuple.map (K.transportValue p.1)))
      ComputableIn.encode htriple).of_eq fun p ↦ rfl
  exact ComputableIn.encode_iff.mp henc

/-- Composition preserves well-formedness, needing only `F`'s: the domain index and the mapped
range tuple's length both come from `F` (`G` only reindexes each entry). -/
theorem compData_wellFormed {G F : PotentialEmbeddingData} (hF : F.WellFormed K) :
    (K.compData G F).WellFormed K := by
  simp only [PotentialEmbeddingData.WellFormed, compData_rangeTuple, compData_domIdx,
    List.length_map]
  exact hF

/-- Left identity: composing with the identity on `F`'s codomain returns `F` unchanged, on the
nose. `transportValue` of the identity is the identity (`transportValue_id`), so the mapped
range tuple is `F`'s own. -/
theorem compData_id_left (F : PotentialEmbeddingData) :
    K.compData (PotentialEmbeddingData.id K F.codIdx) F = F := by
  have hfun : K.transportValue (PotentialEmbeddingData.id K F.codIdx) = id :=
    funext fun x ↦ K.transportValue_id F.codIdx x
  change PotentialEmbeddingData.ofTriple
      (F.domIdx, F.codIdx,
        F.rangeTuple.map (K.transportValue (PotentialEmbeddingData.id K F.codIdx))) = F
  rw [hfun, List.map_id]
  rfl

/-- Under actualness, any tuple `v` and its `transportValue G`-image are atomically equivalent
(source and target structures at `G`'s domain and codomain indices). The ℕ-value of
`transportValue G` is the realized embedding of the actual `G` (`toEmbedding`), a homomorphism:
it reflects term equalities (injective) and preserves relation atoms. The bundled presentation
carriers of `toEmbedding` stay confined to this proof, so the statement is over `ℕ`. -/
theorem transportValue_atomicEquivalent {G : PotentialEmbeddingData} (hGwf : G.WellFormed K)
    (hGAE : @AtomicEquivalent L ℕ ℕ (K.structureAt G.domIdx) (K.structureAt G.codIdx) _
      (K.gens G.domIdx).view (G.targetView hGwf)) {k : ℕ} (v : Fin k → ℕ) :
    @AtomicEquivalent L ℕ ℕ (K.structureAt G.domIdx) (K.structureAt G.codIdx) _
      v (fun i ↦ K.transportValue G (v i)) := by
  have himg : (fun i ↦ K.transportValue G (v i)) = ⇑(G.toEmbedding hGwf hGAE) ∘ v :=
    funext fun i ↦ K.transportValue_eq_toEmbedding hGwf hGAE (v i)
  have hreal : ∀ t : L.Term (Fin k),
      @Term.realize L ℕ (K.structureAt G.codIdx) _ (fun i ↦ K.transportValue G (v i)) t
        = G.toEmbedding hGwf hGAE (@Term.realize L ℕ (K.structureAt G.domIdx) _ v t) := by
    intro t
    rw [himg]
    exact HomClass.realize_term (G.toEmbedding hGwf hGAE)
  refine ⟨fun t₁ t₂ ↦ ?_, fun R ts ↦ ?_⟩
  · rw [hreal t₁, hreal t₂]
    exact (G.toEmbedding hGwf hGAE).injective.eq_iff.symm
  · rw [show (fun i ↦ @Term.realize L ℕ (K.structureAt G.codIdx) _
        (fun j ↦ K.transportValue G (v j)) (ts i))
        = ⇑(G.toEmbedding hGwf hGAE)
          ∘ fun i ↦ @Term.realize L ℕ (K.structureAt G.domIdx) _ v (ts i) from
        funext fun i ↦ hreal (ts i)]
    exact ((G.toEmbedding hGwf hGAE).map_rel' R _).symm

/-- Composition of actual data along a matching middle index is actual. Chaining atomic
equivalences (`trans`) over the shared middle tuple `F.targetView`: `F`'s generators are
equivalent to it (`hFAE`, re-indexed to the middle structure by `hFG`), and it is equivalent to
its `transportValue G`-image (`transportValue_atomicEquivalent`) — which is `(compData G F)`'s
target view. Both steps stay over `ℕ`, so no bundled embedding is composed. -/
theorem compData_isEmbedding {G F : PotentialEmbeddingData} (hFG : F.codIdx = G.domIdx)
    (hF : F.IsEmbedding K) (hG : G.IsEmbedding K) :
    (K.compData G F).IsEmbedding K := by
  obtain ⟨hFwf, hFAE⟩ := hF
  obtain ⟨hGwf, hGAE⟩ := hG
  refine ⟨K.compData_wellFormed hFwf, ?_⟩
  rw [hFG] at hFAE
  have AE2 := K.transportValue_atomicEquivalent hGwf hGAE (F.targetView hFwf)
  have htuple : (fun i ↦ K.transportValue G (F.targetView hFwf i))
      = (K.compData G F).targetView (K.compData_wellFormed hFwf) := by
    funext i
    simp only [PotentialEmbeddingData.targetView, compData_rangeTuple, Tuple.view_eq_get,
      List.get_eq_getElem, List.getElem_map, Fin.val_cast]
  -- `structureAt` values are not instances, so pass all three to `trans` explicitly.
  have hchain := @AtomicEquivalent.trans L ℕ ℕ ℕ (K.structureAt F.domIdx)
    (K.structureAt G.domIdx) (K.structureAt G.codIdx) _ _ _ _ hFAE AE2
  rw [htuple] at hchain
  exact hchain

/-- Homomorphism property of transport on actual data: transport commutes with term
realization (source structure at `G.domIdx`, target at `G.codIdx`), since the ℕ-value of
`transportValue G` is the realized embedding `toEmbedding`. -/
theorem transportValue_realize {G : PotentialEmbeddingData} (hGwf : G.WellFormed K)
    (hGAE : @AtomicEquivalent L ℕ ℕ (K.structureAt G.domIdx) (K.structureAt G.codIdx) _
      (K.gens G.domIdx).view (G.targetView hGwf)) {k : ℕ} (v : Fin k → ℕ)
    (t : L.Term (Fin k)) :
    K.transportValue G (@Term.realize L ℕ (K.structureAt G.domIdx) _ v t)
      = @Term.realize L ℕ (K.structureAt G.codIdx) _ (fun i ↦ K.transportValue G (v i)) t := by
  rw [show (fun i ↦ K.transportValue G (v i)) = ⇑(G.toEmbedding hGwf hGAE) ∘ v from
      funext fun i ↦ K.transportValue_eq_toEmbedding hGwf hGAE (v i),
    K.transportValue_eq_toEmbedding hGwf hGAE
      (@Term.realize L ℕ (K.structureAt G.domIdx) _ v t)]
  exact (HomClass.realize_term (G.toEmbedding hGwf hGAE)).symm

/-- Transport carries each domain generator to the corresponding target-view entry. -/
theorem transportValue_gens {G : PotentialEmbeddingData} (hGwf : G.WellFormed K)
    (hGAE : @AtomicEquivalent L ℕ ℕ (K.structureAt G.domIdx) (K.structureAt G.codIdx) _
      (K.gens G.domIdx).view (G.targetView hGwf)) (i : Fin (K.gens G.domIdx).length) :
    K.transportValue G ((K.gens G.domIdx).view i) = G.targetView hGwf i := by
  rw [K.transportValue_eq_toEmbedding hGwf hGAE]
  exact G.toEmbedding_apply_gens hGwf hGAE i

/-- Right identity: composing with the identity on `G`'s domain returns `G`, given `G` actual.
Transport carries each generator to its range entry (`transportValue_gens`), so the mapped
generator tuple is `G`'s range tuple. -/
theorem compData_id_right {G : PotentialEmbeddingData} (hG : G.IsEmbedding K) :
    K.compData G (PotentialEmbeddingData.id K G.domIdx) = G := by
  obtain ⟨hGwf, hGAE⟩ := hG
  have hmap : (K.gens G.domIdx).map (K.transportValue G) = G.rangeTuple := by
    apply List.ext_getElem
    · rw [List.length_map]; exact hGwf.symm
    · intro n h1 h2
      rw [List.getElem_map]
      have hg := K.transportValue_gens hGwf hGAE ⟨n, by rwa [List.length_map] at h1⟩
      simpa [Tuple.view_eq_get, List.get_eq_getElem, PotentialEmbeddingData.targetView,
        Fin.val_cast] using hg
  change PotentialEmbeddingData.ofTriple
      (G.domIdx, G.codIdx, (K.gens G.domIdx).map (K.transportValue G)) = G
  rw [hmap]
  rfl

/-- Functoriality of transport: transporting along a composite equals composing the transports,
on actual data with matching middle index (`G.codIdx = H.domIdx`). Both sides realize the
representing term of `x` over `G`'s generators, each generator carried through `G` then `H`. -/
theorem transportValue_compData {G H : PotentialEmbeddingData} (hGH : G.codIdx = H.domIdx)
    (hG : G.IsEmbedding K) (hH : H.IsEmbedding K) (x : ℕ) :
    K.transportValue (K.compData H G) x = K.transportValue H (K.transportValue G x) := by
  obtain ⟨hGwf, hGAE⟩ := hG
  obtain ⟨hHwf, hHAE⟩ := hH
  obtain ⟨hcwf, hcAE⟩ := K.compData_isEmbedding hGH ⟨hGwf, hGAE⟩ ⟨hHwf, hHAE⟩
  -- Write `x` as a term value over `G`'s generators (`G` generates its structure).
  obtain ⟨t, ht⟩ := (@Tuple.generates_iff L ℕ (K.structureAt G.domIdx) (K.gens G.domIdx)).1
    (K.generates G.domIdx) x
  subst ht
  -- Generator base case: transport through the composite = transport through `G` then `H`.
  have hpt : ∀ i : Fin (K.gens G.domIdx).length,
      K.transportValue (K.compData H G) ((K.gens G.domIdx).view i)
        = K.transportValue H (K.transportValue G ((K.gens G.domIdx).view i)) := by
    intro i
    have hgc : K.transportValue (K.compData H G) ((K.gens G.domIdx).view i)
        = (K.compData H G).targetView hcwf i := K.transportValue_gens hcwf hcAE i
    rw [hgc, K.transportValue_gens hGwf hGAE i]
    simp only [PotentialEmbeddingData.targetView, compData_rangeTuple, Tuple.view_eq_get,
      List.get_eq_getElem, List.getElem_map, Fin.val_cast]
  -- The transport/realize equations, each ascribed to the `G`/`H`-flavored structures so the
  -- `(compData).domIdx ≡ G.domIdx`, `(compData).codIdx ≡ H.codIdx` defeqs are discharged here
  -- (rewriting alone would not match them syntactically).
  have e1 : K.transportValue (K.compData H G)
        (@Term.realize L ℕ (K.structureAt G.domIdx) _ (K.gens G.domIdx).view t)
      = @Term.realize L ℕ (K.structureAt H.codIdx) _
          (fun i ↦ K.transportValue (K.compData H G) ((K.gens G.domIdx).view i)) t :=
    K.transportValue_realize hcwf hcAE (K.gens G.domIdx).view t
  have e2 : K.transportValue G
        (@Term.realize L ℕ (K.structureAt G.domIdx) _ (K.gens G.domIdx).view t)
      = @Term.realize L ℕ (K.structureAt G.codIdx) _
          (fun i ↦ K.transportValue G ((K.gens G.domIdx).view i)) t :=
    K.transportValue_realize hGwf hGAE (K.gens G.domIdx).view t
  have e3 : @Term.realize L ℕ (K.structureAt G.codIdx) _
        (fun i ↦ K.transportValue G ((K.gens G.domIdx).view i)) t
      = @Term.realize L ℕ (K.structureAt H.domIdx) _
        (fun i ↦ K.transportValue G ((K.gens G.domIdx).view i)) t := by rw [hGH]
  have e4 : K.transportValue H
        (@Term.realize L ℕ (K.structureAt H.domIdx) _
          (fun i ↦ K.transportValue G ((K.gens G.domIdx).view i)) t)
      = @Term.realize L ℕ (K.structureAt H.codIdx) _
          (fun i ↦ K.transportValue H (K.transportValue G ((K.gens G.domIdx).view i))) t :=
    K.transportValue_realize hHwf hHAE (fun i ↦ K.transportValue G ((K.gens G.domIdx).view i)) t
  rw [e1, e2, e3, e4]
  simp only [hpt]

/-- The realized embedding of a composite is the composition of the realized embeddings (as
functions on ℕ), on actual data with matching middle index. A restatement of
`transportValue_compData` through `transportValue_eq_toEmbedding`. -/
theorem toEmbedding_compData {F G : PotentialEmbeddingData} (hFG : F.codIdx = G.domIdx)
    (hFwf : F.WellFormed K)
    (hFAE : @AtomicEquivalent L ℕ ℕ (K.structureAt F.domIdx) (K.structureAt F.codIdx) _
      (K.gens F.domIdx).view (F.targetView hFwf))
    (hGwf : G.WellFormed K)
    (hGAE : @AtomicEquivalent L ℕ ℕ (K.structureAt G.domIdx) (K.structureAt G.codIdx) _
      (K.gens G.domIdx).view (G.targetView hGwf))
    (hcwf : (K.compData G F).WellFormed K)
    (hcAE : @AtomicEquivalent L ℕ ℕ (K.structureAt (K.compData G F).domIdx)
      (K.structureAt (K.compData G F).codIdx) _ (K.gens (K.compData G F).domIdx).view
      ((K.compData G F).targetView hcwf)) (x : ℕ) :
    (K.compData G F).toEmbedding hcwf hcAE x
      = G.toEmbedding hGwf hGAE (F.toEmbedding hFwf hFAE x) := by
  rw [← K.transportValue_eq_toEmbedding hcwf hcAE,
    ← K.transportValue_eq_toEmbedding hFwf hFAE,
    ← K.transportValue_eq_toEmbedding hGwf hGAE]
  exact K.transportValue_compData hFG ⟨hFwf, hFAE⟩ ⟨hGwf, hGAE⟩ x

/-- Associativity of composition, as an equality of code data, on actual `G`, `H` with matching
middle index `G.codIdx = H.domIdx`. `F` is arbitrary: both sides transport `F`'s range tuple
by `transportValue H ∘ transportValue G`, which `transportValue_compData` identifies with
`transportValue (compData H G)`. -/
theorem compData_assoc {F G H : PotentialEmbeddingData} (hGH : G.codIdx = H.domIdx)
    (hG : G.IsEmbedding K) (hH : H.IsEmbedding K) :
    K.compData H (K.compData G F) = K.compData (K.compData H G) F := by
  have hfun : K.transportValue (K.compData H G) = K.transportValue H ∘ K.transportValue G :=
    funext fun e ↦ K.transportValue_compData hGH hG hH e
  change PotentialEmbeddingData.ofTriple
      (F.domIdx, H.codIdx,
        (F.rangeTuple.map (K.transportValue G)).map (K.transportValue H)) = _
  rw [List.map_map, ← hfun]
  rfl

/-- The checked (source-faithful) totalization of composition: the composite on actual `G`,
otherwise a fallback carrying `G`'s range at `F`'s domain and `G`'s codomain. Not claimed
computable here; later it is computable relative to an oracle deciding `IsEmbedding`. -/
noncomputable def checkedComp (G F : PotentialEmbeddingData) : PotentialEmbeddingData :=
  open Classical in
  if G.IsEmbedding K then K.compData G F
  else ⟨F.domIdx, G.codIdx, G.rangeTuple⟩

end ComputableAgeIn

end FirstOrder.Language
