/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.CeDomainChain
import ComputableModelTheory.Computability.Encoding
import ComputableModelTheory.Computability.Jump
import ComputableModelTheory.Computability.ListComputable
import ComputableModelTheory.Computability.OraclePred
import ComputableModelTheory.Computability.RecursiveIn
import ComputableModelTheory.Computability.Reduction

/-!
# Computability substrate

Umbrella module for the relative-computability layer: typed `RecursiveIn`/`ComputableIn`
combinators, oracle-relative predicates, lightweight reductions, and the minimal oracle
jump calculus (the `ComputesJumpOf` interface with its r.e.-to-decidable bridges and the
displayed `0′`).
-/
