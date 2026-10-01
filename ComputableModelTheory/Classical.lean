/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.CountablePrime
import ComputableModelTheory.ModelTheory.ExtensionRichDirectLimit
import ComputableModelTheory.ModelTheory.ExtensionRichFamily
import ComputableModelTheory.ModelTheory.FraisseExistence
import ComputableModelTheory.ModelTheory.NamedParameters
import ComputableModelTheory.ModelTheory.OrbitIsolation
import ComputableModelTheory.ModelTheory.RepresentativeAge
import ComputableModelTheory.ModelTheory.RootedExtension

/-!
# The classical layer

A narrow entry point for the classical, Mathlib-only model theory of this library, so that a
downstream project can import it in one line without the effective layers:

* `ExtensionRichFamily`: extension-rich families of substructures, a classical Fraïssé criterion;
* `RepresentativeAge`: representative classes, their Fraïssé properties, and tuple factorization;
* `ExtensionRichDirectLimit`: extension-rich direct limits and Fraïssé sequences;
* `RootedExtension`: rooted universality and uniqueness, adapters over Mathlib's back-and-forth;
* `FraisseExistence`: classical Fraïssé existence, including
  `IsFraisse K → ∃ M, IsFraisseLimit K M`;
* `OrbitIsolation`: semantic type isolation and atomicity from orbit formulas;
* `CountablePrime`: countable atomic structures embed elementarily into every model;
* `NamedParameters`: isolation and primeness over named finite parameters (`L[[Fin k]]`).

Everything here is in the namespace `FirstOrder.Language` and imports only Mathlib. This module is
import-only: it defines nothing. The audit `ClassicalAudit` checks that, the import boundary, and
the axioms of every declaration of the eight modules.

**Name clash.** `FirstOrder.Language.IsAtomic` (atomicity of a structure over a theory) shares its
last component with Mathlib's order-theoretic `IsAtomic` and with the syntactic
`FirstOrder.Language.BoundedFormula.IsAtomic`. Outside the namespace, write `Language.IsAtomic`
(after `open FirstOrder`) or the full name; a bare `IsAtomic` after `open FirstOrder.Language` is
resolved only by overloading against the order-theoretic class.
-/
