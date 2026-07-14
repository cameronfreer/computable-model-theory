/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CanonicalTransport
import ComputableModelTheory.ModelTheory.Computable.ComputableAge
import ComputableModelTheory.ModelTheory.Computable.EffectiveWitnesses
import ComputableModelTheory.ModelTheory.Computable.EmbeddingInformation
import ComputableModelTheory.ModelTheory.Computable.IndexedProperties
import ComputableModelTheory.ModelTheory.Computable.PotentialComposition
import ComputableModelTheory.ModelTheory.Computable.PotentialEmbedding
import ComputableModelTheory.ModelTheory.Computable.PotentialSpan
import ComputableModelTheory.ModelTheory.Computable.UniformAtomic
import ComputableModelTheory.ModelTheory.Computable.UniformTermEvaluation
import Mathlib.ModelTheory.FinitelyGenerated
import Mathlib.ModelTheory.Fraisse

/-!
# Computable ages

Umbrella module for the age layer: uniform computable ages with their represented
classical classes, potential embeddings with their realization theory, uniform term
and atomic-data evaluation, semantic embedding information with its r.e. complement,
canonical least-term transport of values along potential embedding data, composition of
potential embedding data, potential spans with amalgamation diagrams, the indexed
HP/JEP/AP properties with joint embedding data, and the effective HP/JEP/AP witness
interfaces. Witness extraction is to come.
-/
