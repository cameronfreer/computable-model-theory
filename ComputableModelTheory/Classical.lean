/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.CountablePrime
import ComputableModelTheory.ModelTheory.ExtensionRichDirectLimit
import ComputableModelTheory.ModelTheory.ExtensionRichFamily
import ComputableModelTheory.ModelTheory.OrbitIsolation
import ComputableModelTheory.ModelTheory.RepresentativeAge

/-!
# The classical layer

A narrow entry point for the classical, Mathlib-only model theory of this library, so that a
downstream project can import it in one line without the effective layers:

* `ExtensionRichFamily`: extension-rich families of substructures, a classical Fraïssé criterion;
* `RepresentativeAge`: representative classes, their Fraïssé properties, and tuple factorization;
* `ExtensionRichDirectLimit`: extension-rich direct limits and Fraïssé sequences;
* `OrbitIsolation`: semantic type isolation and atomicity from orbit formulas;
* `CountablePrime`: countable atomic structures embed elementarily into every model.

Everything here is in the namespace `FirstOrder.Language` and imports only Mathlib; the audit
`ClassicalAudit` checks that boundary and the axioms of every declaration.

**Name clash.** `FirstOrder.Language.IsAtomic` (atomicity of a structure over a theory) shares its
last component with Mathlib's order-theoretic `IsAtomic` and with the syntactic
`FirstOrder.Language.BoundedFormula.IsAtomic`. Outside the namespace, write `Language.IsAtomic`
(after `open FirstOrder`) or the full name; a bare `IsAtomic` after `open FirstOrder.Language` is
resolved only by overloading against the order-theoretic class.
-/
