/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.OraclePred
import ComputableModelTheory.ModelTheory.Computable.AtomicEquiv
import ComputableModelTheory.ModelTheory.Computable.AtomicEquivComputability
import ComputableModelTheory.ModelTheory.Computable.AtomicSatisfaction
import ComputableModelTheory.ModelTheory.Computable.Diagram
import ComputableModelTheory.ModelTheory.Computable.GeneratedPresentation
import ComputableModelTheory.ModelTheory.Computable.GraphExample
import ComputableModelTheory.ModelTheory.Computable.QFSatisfaction
import ComputableModelTheory.ModelTheory.Computable.Structure
import ComputableModelTheory.ModelTheory.Computable.SuccExample
import ComputableModelTheory.ModelTheory.Computable.TermClosure
import ComputableModelTheory.ModelTheory.Computable.TermEvaluation
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Semantics

/-!
# Computable structures

Umbrella module for the computable-structure layer: ω-presented computable structures,
computable term evaluation, atomic and quantifier-free satisfaction, the signed
atomic and quantifier-free diagram predicates at fixed width, generated computable
presentations, atomic equivalence of tuples with its generator-preserving
closure-equivalence characterization, effective term enumeration over tuple closures,
and the r.e. failure of atomic equivalence between presentations.
-/
