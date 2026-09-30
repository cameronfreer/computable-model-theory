/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Types

/-! # First-order isolation from definable automorphism orbits

Isolation is semantic entailment over a theory, rather than a condition on its realizations
in one structure. An orbit formula in a structure isolates the tuple's complete type over
that structure's own theory: universal implications transfer to every model of that theory.
Here the pinned first-order API calls the theory of a structure `Language.completeTheory`.
-/

namespace FirstOrder.Language

open FirstOrder Language

universe u v w w'

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {n : ℕ}

/-- A realized formula isolates a tuple's complete type over `T` when its implications
over `T` are exactly the formulas true at the tuple. Modelhood is a separate hypothesis. -/
def IsolatesTuple (T : L.Theory) (φ : L.Formula (Fin n)) (a : Fin n → M) : Prop :=
  φ.Realize a ∧ ∀ ψ : L.Formula (Fin n), (T ⊨ᵇ φ.imp ψ) ↔ ψ.Realize a

/-- Every finite tuple has an isolated complete type over `T`. To say that `M` is an
atomic model of `T`, additionally assume `M ⊨ T`. Empty tuples and repetitions are included. -/
def IsAtomic (T : L.Theory) (M : Type w) [L.Structure M] : Prop :=
  ∀ (n : ℕ) (a : Fin n → M), ∃ φ : L.Formula (Fin n), IsolatesTuple T φ a

/-- A universal formula true in a structure is entailed by its complete theory.
The proof puts its universal closure in the theory before transferring it. -/
theorem models_formula_of_forall_realize (ψ : L.Formula (Fin n))
    (h : ∀ a : Fin n → M, ψ.Realize a) : L.completeTheory M ⊨ᵇ ψ := by
  let σ : L.Sentence := (ψ.relabel (Sum.inr : Fin n → Empty ⊕ Fin n)).iAlls (Fin n)
  have hσ : M ⊨ σ := by
    simpa only [σ, Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel,
      Function.comp_def, Sum.elim_inr] using h
  apply Theory.models_formula_iff.mpr
  intro N b
  have hN : N ⊨ σ :=
    Theory.realize_sentence_of_mem (L.completeTheory M) (mem_completeTheory.mpr hσ)
  have hN' : ∀ c : Fin n → N, ψ.Realize c := by
    simpa only [σ, Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel,
      Function.comp_def, Sum.elim_inr] using hN
  exact hN' b

/-- Any realizer of an isolating formula, in any nonempty model of the theory and
in any universe, has exactly the same first-order type as the original tuple. -/
theorem IsolatesTuple.realize_iff {T : L.Theory} {φ : L.Formula (Fin n)}
    {a : Fin n → M} (h : IsolatesTuple T φ a)
    {N : Type w'} [L.Structure N] [Nonempty N] [N ⊨ T]
    {b : Fin n → N} (hb : φ.Realize b) (ψ : L.Formula (Fin n)) :
    ψ.Realize b ↔ ψ.Realize a := by
  classical
  constructor
  · intro hψ
    by_contra ha
    have hnot : T ⊨ᵇ φ.imp ψ.not := (h.2 ψ.not).mpr (Formula.realize_not.mpr ha)
    exact (Formula.realize_not.mp
      (Formula.realize_imp.mp (hnot.realize_formula N) hb)) hψ
  · intro ha
    exact Formula.realize_imp.mp (((h.2 ψ).mpr ha).realize_formula N) hb

/-- Semantic isolation singles out the tuple's type among all complete types,
including types not realized in the original structure. -/
theorem IsolatesTuple.typesWith_eq_singleton {T : L.Theory} [Nonempty M] [M ⊨ T]
    {φ : L.Formula (Fin n)} {a : Fin n → M} (h : IsolatesTuple T φ a) :
    T.typesWith (Formula.equivSentence φ) = {T.typeOf a} := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨N, b, rfl⟩ := Theory.exists_modelType_is_realized_in T p
    have hb : φ.Realize b := Theory.CompleteType.formula_mem_typeOf.mp hp
    apply Set.mem_singleton_iff.mpr
    apply SetLike.ext
    intro ψ
    simp only [Theory.CompleteType.mem_typeOf]
    exact h.realize_iff hb (Formula.equivSentence.symm ψ)
  · intro hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact Theory.CompleteType.formula_mem_typeOf.mpr h.1

/-- A formula defining the automorphism orbit of a tuple isolates its type over
the complete theory of the structure. No countability assumption is needed here. -/
theorem isolatesTuple_of_orbit_formula [Nonempty M] (a : Fin n → M)
    (φ : L.Formula (Fin n))
    (horbit : ∀ b : Fin n → M, φ.Realize b ↔
      ∃ e : M ≃[L] M, ∀ i, e (a i) = b i) :
    IsolatesTuple (L.completeTheory M) φ a := by
  have ha : φ.Realize a := (horbit a).mpr ⟨Language.Equiv.refl L M, fun _ => rfl⟩
  refine ⟨ha, fun ψ => ⟨fun h => ?_, fun hψ => ?_⟩⟩
  · exact Formula.realize_imp.mp (h.realize_formula M) ha
  · apply models_formula_of_forall_realize
    intro b
    apply Formula.realize_imp.mpr
    intro hb
    obtain ⟨e, he⟩ := (horbit b).mp hb
    have heq : e ∘ a = b := funext he
    rw [← heq]
    exact (StrongHomClass.realize_formula e ψ).mpr hψ

/-- Definability of all finite tuple orbits implies atomicity over the structure's
own complete first-order theory. -/
theorem isAtomic_of_orbit_formulas [Nonempty M]
    (horbit : ∀ (n : ℕ) (a : Fin n → M), ∃ φ : L.Formula (Fin n),
      ∀ b : Fin n → M, φ.Realize b ↔ ∃ e : M ≃[L] M, ∀ i, e (a i) = b i) :
    IsAtomic (L.completeTheory M) M := by
  intro n a
  obtain ⟨φ, hφ⟩ := horbit n a
  exact ⟨φ, isolatesTuple_of_orbit_formula a φ hφ⟩

end FirstOrder.Language
