/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.EffectiveLanguage
import ComputableModelTheory.ModelTheory.Syntax.Primcodable
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Encoding
import Mathlib.ModelTheory.Syntax

/-!
# First-order syntax computability

Umbrella module for the syntax layer: effective-language conventions on top of mathlib's
`FirstOrder.Language`, `Primcodable` instances for terms, `Encodable` instances for
formulas (their `Primcodable` upgrade is pending), and computability of syntactic
operations to come.
-/
