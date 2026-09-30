/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.OrbitIsolation
import Mathlib.Basic.Countable.Basic

/-! # Countable atomic structures are prime

The construction is one-sided: successive finite tuples preserve every first-order formula.
Only the source is enumerated; the target is an arbitrary model of the source's complete
theory. No receiving or homogeneity assumption is made on the target.
-/

universe u v w w'

namespace FirstOrder.Language

open FirstOrder Language

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- Agreement on the full first-order type of two finite tuples. -/
def SameFormulaType {n : ℕ} (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∀ ψ : L.Formula (Fin n), ψ.Realize b ↔ ψ.Realize a

private noncomputable def existsLast {n : ℕ} (φ : L.Formula (Fin (n + 1))) :
    L.Formula (Fin n) :=
  (φ.relabel (Fin.lastCases (Sum.inr ()) Sum.inl)).iExs Unit

private theorem realize_existsLast {n : ℕ} (φ : L.Formula (Fin (n + 1)))
    (a : Fin n → M) :
    (existsLast φ).Realize a ↔ ∃ m : M, φ.Realize (Fin.snoc a m) := by
  simp only [existsLast, Formula.realize_iExs, Formula.realize_relabel]
  have heq : ∀ z : Unit → M,
      Sum.elim a z ∘ Fin.lastCases (Sum.inr ()) Sum.inl = Fin.snoc a (z ()) := by
    intro z
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  simp only [heq]
  exact ⟨fun ⟨z, hz⟩ => ⟨z (), hz⟩, fun ⟨m, hm⟩ => ⟨fun _ => m, hm⟩⟩

/-- Isolation supplies the one-sided extension of a tuple agreeing on all formulas. -/
theorem SameFormulaType.exists_extension [Nonempty N] [N ⊨ L.completeTheory M]
    (hatomic : IsAtomic (L.completeTheory M) M) {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (h : SameFormulaType (L := L) a b) (m : M) :
    ∃ z : N, SameFormulaType (L := L) (Fin.snoc a m) (Fin.snoc b z) := by
  obtain ⟨φ, hφ⟩ := hatomic (n + 1) (Fin.snoc a m)
  have ha : (existsLast φ).Realize a := (realize_existsLast φ a).2 ⟨m, hφ.1⟩
  obtain ⟨z, hz⟩ := (realize_existsLast φ b).1 ((h (existsLast φ)).2 ha)
  exact ⟨z, fun ψ => hφ.realize_iff hz ψ⟩

private theorem empty_sameFormulaType [N ⊨ L.completeTheory M] :
    SameFormulaType (L := L) (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  intro ψ
  have h := realize_iff_of_model_completeTheory M N (ψ.relabel Fin.elim0)
  have hM : (default : Empty → M) ∘ (Fin.elim0 : Fin 0 → Empty) = Fin.elim0 :=
    Subsingleton.elim _ _
  have hN : (default : Empty → N) ∘ (Fin.elim0 : Fin 0 → Empty) = Fin.elim0 :=
    Subsingleton.elim _ _
  simpa only [Sentence.Realize, Formula.realize_relabel, hM, hN] using h

private theorem snoc_prefix (e : ℕ → M) (n : ℕ) :
    Fin.snoc (fun i : Fin n => e i) (e n) = (fun i : Fin (n + 1) => e i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

private noncomputable def typeChain [Nonempty N] [N ⊨ L.completeTheory M]
    (hatomic : IsAtomic (L.completeTheory M) M) (e : ℕ → M) :
    (n : ℕ) → {b : Fin n → N // SameFormulaType (L := L) (fun i => e i) b}
  | 0 => ⟨Fin.elim0, by
      have h : (fun i : Fin 0 => e i) = Fin.elim0 := funext fun i => i.elim0
      rw [h]
      exact empty_sameFormulaType⟩
  | n + 1 =>
    let b := typeChain hatomic e n
    let h := b.2.exists_extension hatomic (e n)
    ⟨Fin.snoc b.1 h.choose, by simpa only [snoc_prefix] using h.choose_spec⟩

private theorem typeChain_coherent [Nonempty N] [N ⊨ L.completeTheory M]
    (hatomic : IsAtomic (L.completeTheory M) M) (e : ℕ → M) (n : ℕ) (i : Fin n) :
    (typeChain (N := N) hatomic e (n + 1)).1 i.castSucc =
      (typeChain (N := N) hatomic e n).1 i := by
  simp only [typeChain, Fin.snoc_castSucc]

private theorem typeChain_value [Nonempty N] [N ⊨ L.completeTheory M]
    (hatomic : IsAtomic (L.completeTheory M) M) (e : ℕ → M) {k j : ℕ} (hjk : j < k) :
    (typeChain (N := N) hatomic e k).1 ⟨j, hjk⟩ =
      (typeChain (N := N) hatomic e (j + 1)).1 (Fin.last j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : j < k
    · exact (typeChain_coherent hatomic e k ⟨j, h⟩).trans (ih h)
    · have : j = k := by omega
      subst j
      rfl

/-- A countable nonempty atomic structure embeds elementarily into every model
of its complete theory, without any bound on the target cardinality or universe. -/
theorem exists_elementaryEmbedding_of_countable_atomic [Countable M] [Nonempty M]
    [N ⊨ L.completeTheory M]
    (hatomic : IsAtomic (L.completeTheory M) M) : Nonempty (M ↪ₑ[L] N) := by
  classical
  have : N ⊨ L.nonemptyTheory :=
    Theory.Model.mono (inferInstance : N ⊨ L.completeTheory M)
      (Theory.completeTheory.subset (M := M))
  have : Nonempty N := (model_nonemptyTheory_iff L).1 inferInstance
  obtain ⟨e, he⟩ := exists_surjective_nat M
  let chain := typeChain (N := N) hatomic e
  let s : ℕ → N := fun j => (chain (j + 1)).1 (Fin.last j)
  have hs : ∀ {k j : ℕ} (hjk : j < k), (chain k).1 ⟨j, hjk⟩ = s j :=
    fun hjk => typeChain_value hatomic e hjk
  let idx : M → ℕ := fun m => (he m).choose
  have hidx : ∀ m, e (idx m) = m := fun m => (he m).choose_spec
  let f : M → N := fun m => s (idx m)
  refine ⟨{ toFun := f, map_formula' := ?_ }⟩
  intro n φ a
  let k := (Finset.univ.sup (fun i : Fin n => idx (a i))) + 1
  have hi : ∀ i : Fin n, idx (a i) < k := fun i =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i : Fin n => idx (a i))
      (Finset.mem_univ i))
  let p : Fin n → Fin k := fun i => ⟨idx (a i), hi i⟩
  have h := (chain k).2 (φ.relabel p)
  have hM : (fun i : Fin k => e i) ∘ p = a := funext fun i => hidx (a i)
  have hN : (chain k).1 ∘ p = f ∘ a := funext fun i => hs (hi i)
  simpa only [Formula.realize_relabel, hM, hN] using h

end FirstOrder.Language
