/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.RecursiveIn

/-!
# Typed combinators for relative computability

This file supplements `Mathlib.Computability.RecursiveIn` with typed combinators for
`RecursiveIn` and `ComputableIn` (composition, pairing, conditionals, and μ-search),
built by descending to the `Nat.RecursiveIn` constructors through `Primcodable`
encodings. These are upstream candidates for mathlib.
-/
