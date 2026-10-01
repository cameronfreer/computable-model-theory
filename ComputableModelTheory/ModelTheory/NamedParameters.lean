/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.CountablePrime

/-! # Isolation and primeness over named finite parameters

A client of `OrbitIsolation` and `CountablePrime` through Mathlib's constants expansion: a tuple
`c : Fin k → M` of parameters is named by the constants of `L[[Fin k]]`, and the existing theorems
apply unchanged in the expanded language.

* `Named M c` is `M` with its `L`-structure and the constants of `L[[Fin k]]` interpreted by `c`.
* Automorphisms of the expansion are exactly the `L`-automorphisms fixing `c` pointwise
  (`namedEquiv`, `unnamedEquiv`).
* **Orbit formulas over the parameters** are `L`-formulas `ψ : L.Formula (Fin k ⊕ Fin n)`, read at
  `Sum.elim c b`, defining the orbit of a tuple under the automorphisms fixing `c`. Such formulas
  for every tuple make the expansion atomic over its own complete theory
  (`isAtomic_named_of_orbit_formulas`). They are hypotheses: ultrahomogeneity alone need not supply
  finitary orbit formulas, even in the original language, and a reduct adds a further obligation.
* **Primeness over the parameters**: for a countable source, any target `N` with a parameter tuple
  `d` whose expansion `Named N d` models the *expanded* complete theory receives an `L`-elementary
  embedding sending `c` to `d` (`exists_elementaryEmbedding_named`). An embedding of the root as an
  `L`-structure does not substitute for that hypothesis.

Nothing is assumed about the substructure the parameters generate, which may be infinite; orbit
formulas are first-order definitions over the parameters, not terms in them.
-/

universe u v w w'

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {k : ℕ}

/-- `M` with the constants of `L[[Fin k]]` interpreted by the parameter tuple `c`. -/
@[nolint unusedArguments]
def Named (M : Type w) (_c : Fin k → M) : Type w :=
  M

namespace Named

variable (c : Fin k → M)

instance : L.Structure (Named M c) :=
  inferInstanceAs (L.Structure M)

instance : (constantsOn (Fin k)).Structure (Named M c) :=
  constantsOn.structure c

instance [Countable M] : Countable (Named M c) :=
  inferInstanceAs (Countable M)

instance [Nonempty M] : Nonempty (Named M c) :=
  inferInstanceAs (Nonempty M)

/-- The `i`-th constant names `c i`. -/
theorem con_eq (i : Fin k) : ((L.con i : L[[Fin k]].Constants) : Named M c) = c i :=
  rfl

end Named

/-! ### Automorphisms of the expansion -/

/-- An `L`-automorphism fixing the parameters is an automorphism of the expansion. -/
def namedEquiv {c : Fin k → M} (e : M ≃[L] M) (he : ∀ i, e (c i) = c i) :
    Named M c ≃[L[[Fin k]]] Named M c where
  toEquiv := e.toEquiv
  map_fun' := by
    rintro n (f | f) x
    · exact e.map_fun f x
    · cases n with
      | zero => exact he f
      | succ n => exact isEmptyElim f
  map_rel' := by
    rintro n (r | r) x
    · exact e.map_rel r x
    · exact isEmptyElim r

/-- An automorphism of the expansion is an `L`-automorphism. -/
def unnamedEquiv {c : Fin k → M} (e : Named M c ≃[L[[Fin k]]] Named M c) : M ≃[L] M where
  toEquiv := e.toEquiv
  map_fun' f x := e.map_fun (Sum.inl f) x
  map_rel' r x := e.map_rel (Sum.inl r) x

/-- An automorphism of the expansion fixes the parameters. -/
theorem unnamedEquiv_apply_param {c : Fin k → M} (e : Named M c ≃[L[[Fin k]]] Named M c)
    (i : Fin k) : unnamedEquiv e (c i) = c i :=
  e.map_fun (Sum.inr i : L[[Fin k]].Functions 0) default

/-! ### Atomicity over the parameters -/

/-- An `L`-formula over the parameter variables, read in the expansion. -/
theorem realize_named {c : Fin k → M} {n : ℕ} (ψ : L.Formula (Fin k ⊕ Fin n)) (b : Fin n → M) :
    Formula.Realize (M := Named M c)
        (BoundedFormula.constantsVarsEquiv.symm ψ : L[[Fin k]].Formula (Fin n)) b ↔
      ψ.Realize (Sum.elim c b) := by
  have h := BoundedFormula.realize_constantsVarsEquiv (M := Named M c)
    (φ := BoundedFormula.constantsVarsEquiv.symm ψ) (v := b) (xs := default)
  have e : BoundedFormula.constantsVarsEquiv (BoundedFormula.constantsVarsEquiv.symm ψ) = ψ :=
    BoundedFormula.constantsVarsEquiv.apply_symm_apply ψ
  exact h.symm.trans (iff_of_eq (congrArg (fun φ ↦ BoundedFormula.Realize (M := Named M c) φ
    (Sum.elim (fun a ↦ ((L.con a : L[[Fin k]].Constants) : Named M c)) b) default) e))

/-- **Atomicity over the parameters.** If every finite tuple has an `L`-formula over the parameters
defining its orbit under the automorphisms fixing `c`, the expansion is atomic over its own complete
theory. -/
theorem isAtomic_named_of_orbit_formulas [Nonempty M] (c : Fin k → M)
    (horbit : ∀ (n : ℕ) (a : Fin n → M), ∃ ψ : L.Formula (Fin k ⊕ Fin n),
      ∀ b : Fin n → M, ψ.Realize (Sum.elim c b) ↔
        ∃ e : M ≃[L] M, (∀ i, e (c i) = c i) ∧ ∀ j, e (a j) = b j) :
    IsAtomic (L[[Fin k]].completeTheory (Named M c)) (Named M c) := by
  apply isAtomic_of_orbit_formulas
  intro n a
  obtain ⟨ψ, hψ⟩ := horbit n a
  exact ⟨BoundedFormula.constantsVarsEquiv.symm ψ, fun b ↦ (realize_named ψ b).trans
    ((hψ b).trans ⟨fun ⟨e, he, hab⟩ ↦ ⟨namedEquiv e he, hab⟩,
      fun ⟨e, hab⟩ ↦ ⟨unnamedEquiv e, unnamedEquiv_apply_param e, hab⟩⟩)⟩

/-! ### Primeness over the parameters -/

/-- An elementary embedding of the expansions is `L`-elementary and sends the parameters to the
parameters. -/
theorem exists_of_named_elementaryEmbedding {N : Type w'} [L.Structure N] {c : Fin k → M}
    {d : Fin k → N} (g : Named M c ↪ₑ[L[[Fin k]]] Named N d) :
    ∃ f : M ↪ₑ[L] N, ∀ i, f (c i) = d i := by
  refine ⟨⟨g, fun n φ x ↦ ?_⟩, fun i ↦ ?_⟩
  · have h := g.map_formula ((L.lhomWithConstants (Fin k)).onFormula φ) x
    exact (LHom.realize_onFormula (M := Named N d) _ φ).symm.trans
      (h.trans (LHom.realize_onFormula (M := Named M c) _ φ))
  · exact g.map_fun (Sum.inr i : L[[Fin k]].Functions 0) default

/-- **Primeness over the parameters.** A countable nonempty `M`, atomic over the complete theory of
its expansion by `c`, embeds `L`-elementarily into any `N` with parameters `d` whose expansion
models that expanded theory, sending `c` to `d`. No countability of `L` or `N`; universes
independent. -/
theorem exists_elementaryEmbedding_named [Countable M] [Nonempty M] {N : Type w'}
    [L.Structure N] (c : Fin k → M) (d : Fin k → N)
    [Named N d ⊨ L[[Fin k]].completeTheory (Named M c)]
    (hatomic : IsAtomic (L[[Fin k]].completeTheory (Named M c)) (Named M c)) :
    ∃ f : M ↪ₑ[L] N, ∀ i, f (c i) = d i := by
  obtain ⟨g⟩ := exists_elementaryEmbedding_of_countable_atomic (N := Named N d) hatomic
  exact exists_of_named_elementaryEmbedding g

end FirstOrder.Language
