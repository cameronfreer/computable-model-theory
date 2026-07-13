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

Computability is packaged over `PotentialEmbeddingData × PotentialEmbeddingData` and stays
`ℕ`/`List ℕ`-valued: the transported tuple is built with `ComputableIn.list_map` over
`transportValue_computableIn`, and the result is assembled by `mk_computableIn`.
`transportValue` is consumed only through its computability contract, so `termCodeFor`
stays opaque.
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

/-- Composition is computable in the oracle, uniformly in both potential embeddings. -/
theorem compData_computableIn :
    ComputableIn O fun p : PotentialEmbeddingData × PotentialEmbeddingData ↦
      K.compData p.1 p.2 := by
  -- BLOCKED (WIP) — left as `sorry` to keep the branch building: even the individual `have`s
  -- below whnf-time-out (>2M, deterministic), not only the closing bridge, so none of the real
  -- structure elaborates.
  --
  -- Intended structure:
  --   have hdom := PotentialEmbeddingData.domIdx_computable.comp ComputableIn.snd
  --   have hcod := PotentialEmbeddingData.codIdx_computable.comp ComputableIn.fst
  --   have hmap := ComputableIn.list_map
  --     (PotentialEmbeddingData.rangeTuple_computable.comp ComputableIn.snd)
  --     (K.transportValue_computableIn.comp
  --       ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd))
  --   have htriple := hdom.pair (hcod.pair hmap)          -- ℕ × ℕ × List ℕ, encoding-free
  --   exact PotentialEmbeddingData.ofTriple_computableIn.comp htriple |>.of_eq fun _ ↦ rfl
  --
  -- The blow-up is `isDefEq` whnf-ing the `PotentialEmbeddingData` (`ofEquiv peEquiv`) encoding
  -- inside `ComputableIn`'s `RecursiveIn` content when a `PotentialEmbeddingData`-valued
  -- `ComputableIn` is matched. Attempts that all time out: `.of_eq fun _ ↦ rfl`; `simpa only
  -- [compData] using …` (inline and via an explicit `hmk`); the generic `mk_computableIn₃`;
  -- the named `ofTriple` head. `local irreducible transportValue` and budgets to 2M do not
  -- help. Needs a bridge (or a `Primcodable`-level lemma) that avoids `isDefEq` on the encoded
  -- `ComputableIn` head. See feature request cameronfreer/lean4-skills#150.
  sorry

end ComputableAgeIn

end FirstOrder.Language
