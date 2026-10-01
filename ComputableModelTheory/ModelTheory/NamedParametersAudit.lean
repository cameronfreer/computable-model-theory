/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.NamedParameters
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: isolation and primeness over named parameters

Outside the root import spine; CI checks it through `scripts/run-audit-modules.sh`, and with
warnings as errors through `scripts/check-classical-layer.sh`.

* **Signatures** in independent universes, no countability of the language or the target
  (`test_atomic_signature`, `test_prime_signature`).
* **The fixture `(ℤ, succ)` with the parameter `0`**, discharged: explicit orbit formulas over the
  parameter (`intOrbit`, defining exactly the orbit under the automorphisms fixing `0`, which are
  the identity), hence atomicity of the expansion (`test_int_isAtomic`) and an elementary embedding
  into every target in `Type 3` whose expansion models the expanded theory, sending `0` to the
  target's parameter (`test_int_prime`).
* **Definability is not generation**: the coordinate `-1` has an isolating formula over the
  parameter (`succ x = c`; `test_negOne_isolated`) but is not in the substructure the parameter
  generates (`test_negOne_not_generated`), and that substructure is infinite
  (`test_closure_infinite`).
* **Standard axioms** for every declaration of the production module and for the regression rows.
* **Import isolation**: the production module imports only `CountablePrime` besides `Init`, and its
  transitive closure contains no module of this library other than `CountablePrime` and
  `OrbitIsolation`, and no module of `InfinitaryLogic`.
-/

universe u v w w'

open FirstOrder Language Structure

namespace FirstOrder.Language

/-! ### Signatures -/

theorem test_atomic_signature {L : Language.{u, v}} {M : Type w} [L.Structure M] [Nonempty M]
    {k : ℕ} (c : Fin k → M)
    (horbit : ∀ (n : ℕ) (a : Fin n → M), ∃ ψ : L.Formula (Fin k ⊕ Fin n),
      ∀ b : Fin n → M, ψ.Realize (Sum.elim c b) ↔
        ∃ e : M ≃[L] M, (∀ i, e (c i) = c i) ∧ ∀ j, e (a j) = b j) :
    IsAtomic (L[[Fin k]].completeTheory (Named M c)) (Named M c) :=
  isAtomic_named_of_orbit_formulas c horbit

theorem test_prime_signature {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M]
    [L.Structure N] [Countable M] [Nonempty M] {k : ℕ} (c : Fin k → M) (d : Fin k → N)
    [Named N d ⊨ L[[Fin k]].completeTheory (Named M c)]
    (hatomic : IsAtomic (L[[Fin k]].completeTheory (Named M c)) (Named M c)) :
    ∃ f : M ↪ₑ[L] N, ∀ i, f (c i) = d i :=
  exists_elementaryEmbedding_named c d hatomic

/-! ### The fixture `(ℤ, succ)` with the parameter `0` -/

/-- One unary function symbol. -/
inductive SuccFun : ℕ → Type
  | succ : SuccFun 1

/-- A language with one unary function symbol and no relation symbols. -/
def succLang : Language.{0, 0} :=
  ⟨SuccFun, fun _ ↦ Empty⟩

/-- The symbol interpreted as `· + 1`. -/
def succMap : ∀ {n : ℕ}, SuccFun n → (Fin n → ℤ) → ℤ
  | _, .succ, x => x 0 + 1

instance : succLang.Structure ℤ where
  funMap f x := succMap f x
  RelMap r := Empty.elim r

/-- The successor symbol. -/
abbrev succSym : succLang.Functions 1 := SuccFun.succ

/-- `succ` iterated `n` times on a term. -/
def succIter {α : Type} : ℕ → succLang.Term α → succLang.Term α
  | 0, t => t
  | n + 1, t => Functions.apply₁ succSym (succIter n t)

theorem realize_succIter {α : Type} (v : α → ℤ) (t : succLang.Term α) (n : ℕ) :
    (succIter n t).realize v = t.realize v + n := by
  induction n with
  | zero => simp [succIter]
  | succ n ih =>
    change (succIter n t).realize v + 1 = _
    rw [ih]
    omega

/-- The parameter tuple `![0]`. -/
abbrev zeroParam : Fin 1 → ℤ := ![0]

/-- An automorphism of `(ℤ, succ)` fixing `0` is the identity. -/
theorem eq_of_fix_zero (e : ℤ ≃[succLang] ℤ) (h0 : e 0 = 0) (x : ℤ) : e x = x := by
  have hs : ∀ y, e (y + 1) = e y + 1 := fun y ↦ e.map_fun succSym ![y]
  induction x using Int.induction_on with
  | zero => exact h0
  | succ i ih => rw [hs, ih]
  | pred i ih =>
    have := hs (-(i : ℤ) - 1)
    rw [sub_add_cancel, ih] at this
    omega

/-- The orbit formula of `a` over the parameter: each coordinate as an iterated successor of the
parameter, or the parameter as an iterated successor of the coordinate. -/
noncomputable def intOrbit {n : ℕ} (a : Fin n → ℤ) : succLang.Formula (Fin 1 ⊕ Fin n) :=
  Formula.iInf fun j : Fin n ↦
    if 0 ≤ a j then (Term.var (Sum.inr j)).equal (succIter (a j).toNat (Term.var (Sum.inl 0)))
    else (succIter (-a j).toNat (Term.var (Sum.inr j))).equal (Term.var (Sum.inl 0))

theorem realize_intOrbit {n : ℕ} (a b : Fin n → ℤ) :
    (intOrbit a).Realize (Sum.elim zeroParam b) ↔ ∀ j, b j = a j := by
  simp only [intOrbit, Formula.realize_iInf]
  refine forall_congr' fun j ↦ ?_
  split_ifs with h
  · simp only [Formula.realize_equal, Term.realize_var, realize_succIter, Sum.elim_inr,
      Sum.elim_inl]
    simp only [Matrix.cons_val_fin_one, zero_add, Int.toNat_of_nonneg h]
  · simp only [Formula.realize_equal, Term.realize_var, realize_succIter, Sum.elim_inr,
      Sum.elim_inl]
    simp only [Matrix.cons_val_fin_one]
    omega

/-- `intOrbit a` defines exactly the orbit of `a` under the automorphisms fixing `0`. -/
theorem intOrbit_spec {n : ℕ} (a b : Fin n → ℤ) :
    (intOrbit a).Realize (Sum.elim zeroParam b) ↔
      ∃ e : ℤ ≃[succLang] ℤ, (∀ i, e (zeroParam i) = zeroParam i) ∧ ∀ j, e (a j) = b j := by
  rw [realize_intOrbit]
  constructor
  · intro h
    exact ⟨Language.Equiv.refl _ _, fun _ ↦ rfl, fun j ↦ (h j).symm⟩
  · rintro ⟨e, he, hab⟩ j
    rw [← hab j, eq_of_fix_zero e (he 0)]

/-- **Atomicity over the parameter `0`.** -/
theorem test_int_isAtomic :
    IsAtomic (succLang[[Fin 1]].completeTheory (Named ℤ zeroParam)) (Named ℤ zeroParam) :=
  isAtomic_named_of_orbit_formulas zeroParam fun _ a ↦ ⟨intOrbit a, intOrbit_spec a⟩

/-- **Primeness over the parameter `0`**, into any target in `Type 3` whose expansion models the
expanded theory. -/
theorem test_int_prime (N : Type 3) [succLang.Structure N] (d : Fin 1 → N)
    [Named N d ⊨ succLang[[Fin 1]].completeTheory (Named ℤ zeroParam)] :
    ∃ f : ℤ ↪ₑ[succLang] N, f 0 = d 0 := by
  obtain ⟨f, hf⟩ := exists_elementaryEmbedding_named zeroParam d test_int_isAtomic
  exact ⟨f, hf 0⟩

/-- **`-1` is defined over the parameter**: `succ x = c`, so its type is isolated. -/
theorem test_negOne_isolated :
    (intOrbit ![(-1 : ℤ)]).Realize (Sum.elim zeroParam ![(-1 : ℤ)]) ∧
      ∃ φ, IsolatesTuple (succLang[[Fin 1]].completeTheory (Named ℤ zeroParam)) φ
        (![(-1 : ℤ)] : Fin 1 → Named ℤ zeroParam) :=
  ⟨(realize_intOrbit _ _).2 fun _ ↦ rfl, test_int_isAtomic 1 _⟩

/-- The nonnegative integers, closed under `succ`. -/
def nonnegSub : succLang.Substructure ℤ where
  carrier := {x | 0 ≤ x}
  fun_mem := by
    rintro _ ⟨⟩ x hx
    exact Int.add_nonneg (hx 0) zero_le_one

/-- **`-1` is not generated by the parameter.** -/
theorem test_negOne_not_generated :
    (-1 : ℤ) ∉ Substructure.closure succLang (Set.range zeroParam) := by
  intro h
  have hle : Substructure.closure succLang (Set.range zeroParam) ≤ nonnegSub :=
    (Substructure.closure_le).2 (by
      rintro _ ⟨i, rfl⟩
      change (0 : ℤ) ≤ zeroParam i
      simp)
  have := hle h
  change (0 : ℤ) ≤ -1 at this
  omega

/-- **The substructure the parameter generates is infinite.** -/
theorem test_closure_infinite :
    (Substructure.closure succLang (Set.range zeroParam) : Set ℤ).Infinite := by
  have hmem : ∀ m : ℕ, (m : ℤ) ∈ Substructure.closure succLang (Set.range zeroParam) := by
    intro m
    induction m with
    | zero => exact Substructure.subset_closure ⟨0, rfl⟩
    | succ m ih =>
      have := (Substructure.closure succLang (Set.range zeroParam)).fun_mem succSym ![(m : ℤ)]
        (fun i ↦ by rw [Subsingleton.elim i 0]; exact ih)
      push_cast
      exact this
  exact Set.infinite_of_injective_forall_mem Nat.cast_injective hmem

end FirstOrder.Language

/-! ### Import isolation -/

open Lean in
run_cmd do
  let env ← getEnv
  let target := `ComputableModelTheory.ModelTheory.NamedParameters
  let allowed : List Name := [`ComputableModelTheory.ModelTheory.CountablePrime,
    `ComputableModelTheory.ModelTheory.OrbitIsolation]
  let some idx := env.getModuleIdx? target | throwError "{target} is not imported"
  let direct := (env.header.moduleData[idx.toNat]!).imports.map (·.module)
  unless direct.filter (· != `Init) == #[allowed[0]!] do
    throwError "unexpected direct imports of {target}: {direct}"
  let mut seen : NameSet := {}
  let mut todo : Array Name := direct
  while h : todo.size > 0 do
    let m := todo.back
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    if !allowed.contains m &&
        ((`ComputableModelTheory).isPrefixOf m || (`InfinitaryLogic).isPrefixOf m) then
      throwError "{target} transitively imports {m}"
    if let some j := env.getModuleIdx? m then
      todo := todo ++ (env.header.moduleData[j.toNat]!).imports.map (·.module)

#assert_standard_axioms FirstOrder.Language.test_atomic_signature
#assert_standard_axioms FirstOrder.Language.test_prime_signature
#assert_standard_axioms FirstOrder.Language.test_int_isAtomic
#assert_standard_axioms FirstOrder.Language.test_int_prime
#assert_standard_axioms FirstOrder.Language.test_negOne_isolated
#assert_standard_axioms FirstOrder.Language.test_negOne_not_generated
#assert_standard_axioms FirstOrder.Language.test_closure_infinite

#assert_module_standard_axioms ComputableModelTheory.ModelTheory.NamedParameters
