/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.Complexity
import ComputableModelTheory.ModelTheory.Syntax.ComputableOps
import ComputableModelTheory.ModelTheory.Syntax.EffectiveLanguage
import ComputableModelTheory.ModelTheory.Syntax.FormulaOps
import ComputableModelTheory.ModelTheory.Syntax.FormulaSigma
import ComputableModelTheory.ModelTheory.Syntax.NatStack
import ComputableModelTheory.ModelTheory.Syntax.Primcodable
import ComputableModelTheory.ModelTheory.Syntax.TermSigma
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Encoding
import Mathlib.ModelTheory.Syntax

/-!
# First-order syntax computability

Umbrella module for the syntax layer: effective-language conventions on top of mathlib's
`FirstOrder.Language`, `Primcodable` instances for terms (including uniformly over all
`Fin` variable bounds) and for bounded formulas, formulas, and sentences, computability
of term operations and of the sigma-level formula constructors, and decidability and
computability of the `IsAtomic`/`IsQF` complexity predicates; formula
relabelling/substitution and the prenex operations are still to come.
-/
