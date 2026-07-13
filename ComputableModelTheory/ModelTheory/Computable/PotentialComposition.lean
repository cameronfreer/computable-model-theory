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
`PotentialEmbeddingData × PotentialEmbeddingData` and stays `ℕ`/`Tuple ℕ`-valued throughout.
The components and the transported tuple are built with `ComputableIn.comp`/`pair`/`list_map`,
each with its implicit *type* params (`α`/`β`/`σ`) **and** *function* params (`f`/`g`) pinned:
result-type ascription alone does not steer elaboration past the `PotentialEmbeddingData`
encoding. The closing `ofTriple` step crosses through `ComputableIn.encode_iff`, keeping the
output ℕ-valued so no `PotentialEmbeddingData`-valued composition — whose `isDefEq` whnf-diverges
on the `ofEquiv peEquiv` encoding — is ever formed. `transportValue` is consumed only through
its computability contract (and kept locally irreducible), so `termCodeFor` stays opaque.
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
correctness carries its own hypotheses. Built through the named `ofTriple` factory so its
computability proof compares by that head rather than an anonymous constructor. -/
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

end ComputableAgeIn

end FirstOrder.Language
