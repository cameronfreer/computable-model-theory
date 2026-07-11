/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.OraclePred

/-!
# Lightweight reductions and oracle transport

This file provides just enough reducibility API to state that a predicate or function
is computable from a given oracle (for example, embedding information), without
formalizing Turing degrees as quotients.
-/
