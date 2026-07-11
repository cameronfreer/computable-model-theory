/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.RecursiveIn
import Mathlib.Computability.Partrec
import Mathlib.Computability.RE

/-!
# Relative computable and r.e. predicates

This file defines `ComputablePredIn` and `REPredIn`, the oracle-relative analogues of
mathlib's `ComputablePred` and `REPred`, together with their closure lemmas (Boolean
operations, finite quantifiers, and the computable-to-r.e. bridge). Oracles are sets
`O : Set (ℕ →. ℕ)`, matching mathlib's `RecursiveIn`/`ComputableIn` layer.
-/
