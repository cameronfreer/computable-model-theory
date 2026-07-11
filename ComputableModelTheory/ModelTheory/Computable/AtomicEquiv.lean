/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.TupleClosure
import ComputableModelTheory.ModelTheory.Syntax.Complexity

/-!
# Atomic equivalence of tuples

Two tuples in possibly different structures are atomically equivalent when they agree
on all term equalities and on all relation atoms. This is equivalent to agreement on
all atomic formulas (`atomicEquivalent_iff_forall_atomicFormula`), and — the core
theorem — to the existence of a generator-preserving equivalence between the tuple
closures (`atomicEquivalent_iff_exists_closure_equiv`): the forward map sends the
value of a term at one tuple to its value at the other, well-defined by agreement on
term equalities, function-preserving by term formation, and relation-preserving by
agreement on relation atoms; the reverse direction transports term values and
relation atoms along the equivalence.

The equivalence construction chooses term representatives for closure elements, so it
is noncomputable; its effective content is developed separately.
-/

open FirstOrder Language Language.BoundedFormula

namespace FirstOrder.Language

variable {L : Language} {M N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variable {k : ℕ}

/-- Two tuples agree on term equalities. -/
def TermEqualitiesAgree (L : Language) {M N : Type*} [L.Structure M] [L.Structure N]
    {k : ℕ} (a : Fin k → M) (b : Fin k → N) : Prop :=
  ∀ t₁ t₂ : L.Term (Fin k),
    t₁.realize a = t₂.realize a ↔ t₁.realize b = t₂.realize b

/-- Two tuples agree on relation atoms. -/
def RelationsAgree (L : Language) {M N : Type*} [L.Structure M] [L.Structure N]
    {k : ℕ} (a : Fin k → M) (b : Fin k → N) : Prop :=
  ∀ {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term (Fin k)),
    Structure.RelMap R (fun i ↦ (ts i).realize a) ↔
      Structure.RelMap R fun i ↦ (ts i).realize b

/-- Atomic equivalence of two tuples in possibly different structures: agreement on
term equalities and on relation atoms. -/
def AtomicEquivalent (L : Language) {M N : Type*} [L.Structure M] [L.Structure N]
    {k : ℕ} (a : Fin k → M) (b : Fin k → N) : Prop :=
  TermEqualitiesAgree L a b ∧ RelationsAgree L a b

namespace AtomicEquivalent

theorem refl (a : Fin k → M) : AtomicEquivalent L a a :=
  ⟨fun _ _ ↦ Iff.rfl, fun _ _ ↦ Iff.rfl⟩

theorem symm {a : Fin k → M} {b : Fin k → N} (h : AtomicEquivalent L a b) :
    AtomicEquivalent L b a :=
  ⟨fun t₁ t₂ ↦ (h.1 t₁ t₂).symm, fun R ts ↦ (h.2 R ts).symm⟩

theorem trans {a : Fin k → M} {b : Fin k → N} {c : Fin k → P}
    (hab : AtomicEquivalent L a b) (hbc : AtomicEquivalent L b c) :
    AtomicEquivalent L a c :=
  ⟨fun t₁ t₂ ↦ (hab.1 t₁ t₂).trans (hbc.1 t₁ t₂),
    fun R ts ↦ (hab.2 R ts).trans (hbc.2 R ts)⟩

end AtomicEquivalent

section FormulaCharacterization

private theorem realize_relabelElim (t : L.Term (Fin k ⊕ Fin 0)) (v : Fin k → M)
    (xs : Fin 0 → M) :
    (t.relabel (Sum.elim id Fin.elim0)).realize v = t.realize (Sum.elim v xs) := by
  rw [Term.realize_relabel]
  congr 1
  funext x
  rcases x with x | x
  · rfl
  · exact x.elim0

private theorem realize_relabelInl (t : L.Term (Fin k)) (v : Fin k → M)
    (xs : Fin 0 → M) :
    (t.relabel Sum.inl : L.Term (Fin k ⊕ Fin 0)).realize (Sum.elim v xs) =
      t.realize v := by
  rw [Term.realize_relabel]
  rfl

/-- Atomic equivalence is agreement on all atomic formulas. -/
theorem atomicEquivalent_iff_forall_atomicFormula (a : Fin k → M) (b : Fin k → N) :
    AtomicEquivalent L a b ↔
      ∀ φ : AtomicFormula L (Fin k),
        ((φ : L.Formula (Fin k)).Realize a ↔ (φ : L.Formula (Fin k)).Realize b) := by
  constructor
  · rintro ⟨hEq, hRel⟩ ⟨φ, hφ⟩
    rcases hφ with ⟨t₁, t₂⟩ | ⟨R, ts⟩
    · show Formula.Realize _ a ↔ Formula.Realize _ b
      rw [Formula.Realize, Formula.Realize, realize_bdEqual, realize_bdEqual,
        ← realize_relabelElim t₁ a, ← realize_relabelElim t₂ a,
        ← realize_relabelElim t₁ b, ← realize_relabelElim t₂ b]
      exact hEq _ _
    · show Formula.Realize _ a ↔ Formula.Realize _ b
      rw [Formula.Realize, Formula.Realize, realize_rel, realize_rel,
        show (fun i ↦ (ts i).realize (Sum.elim a default)) =
          fun i ↦ ((ts i).relabel (Sum.elim id Fin.elim0)).realize a from
          funext fun i ↦ (realize_relabelElim _ a _).symm,
        show (fun i ↦ (ts i).realize (Sum.elim b default)) =
          fun i ↦ ((ts i).relabel (Sum.elim id Fin.elim0)).realize b from
          funext fun i ↦ (realize_relabelElim _ b _).symm]
      exact hRel R _
  · intro h
    constructor
    · intro t₁ t₂
      have := h ⟨Term.bdEqual (t₁.relabel Sum.inl) (t₂.relabel Sum.inl),
        IsAtomic.equal _ _⟩
      rw [Formula.Realize, Formula.Realize, realize_bdEqual, realize_bdEqual,
        realize_relabelInl t₁ a, realize_relabelInl t₂ a,
        realize_relabelInl t₁ b, realize_relabelInl t₂ b] at this
      exact this
    · intro n R ts
      have := h ⟨Relations.boundedFormula R fun i ↦ (ts i).relabel Sum.inl,
        IsAtomic.rel _ _⟩
      rw [Formula.Realize, Formula.Realize, realize_rel, realize_rel,
        show (fun i ↦ ((ts i).relabel Sum.inl : L.Term (Fin k ⊕ Fin 0)).realize
            (Sum.elim a default)) = fun i ↦ (ts i).realize a from
          funext fun i ↦ realize_relabelInl _ a _,
        show (fun i ↦ ((ts i).relabel Sum.inl : L.Term (Fin k ⊕ Fin 0)).realize
            (Sum.elim b default)) = fun i ↦ (ts i).realize b from
          funext fun i ↦ realize_relabelInl _ b _] at this
      exact this

end FormulaCharacterization

section ClosureEquiv

/-- A chosen term representing a closure element. -/
private noncomputable def termFor (a : Fin k → M)
    (x : Substructure.closure L (Set.range a)) : L.Term (Fin k) :=
  ((mem_closure_range_iff_exists_term a).1 x.2).choose

private theorem termFor_spec (a : Fin k → M)
    (x : Substructure.closure L (Set.range a)) : (termFor a x).realize a = ↑x :=
  ((mem_closure_range_iff_exists_term a).1 x.2).choose_spec

/-- The transfer map on closures: realize the chosen term at the other tuple. -/
private noncomputable def transfer (a : Fin k → M) (b : Fin k → N)
    (x : Substructure.closure L (Set.range a)) :
    Substructure.closure L (Set.range b) :=
  ⟨(termFor a x).realize b, (mem_closure_range_iff_exists_term b).2 ⟨_, rfl⟩⟩

/-- Any term representing the source computes the transfer value. -/
private theorem coe_transfer_eq {a : Fin k → M} {b : Fin k → N}
    (hEq : TermEqualitiesAgree L a b) {x : Substructure.closure L (Set.range a)}
    {t : L.Term (Fin k)} (ht : t.realize a = ↑x) :
    (↑(transfer a b x) : N) = t.realize b :=
  (hEq (termFor a x) t).1 ((termFor_spec a x).trans ht.symm)

/-- The core theorem: atomic equivalence is the existence of a generator-preserving
equivalence between the tuple closures. -/
theorem atomicEquivalent_iff_exists_closure_equiv (a : Fin k → M) (b : Fin k → N) :
    AtomicEquivalent L a b ↔
      ∃ e : Substructure.closure L (Set.range a) ≃[L]
          Substructure.closure L (Set.range b),
        ∀ i, e ⟨a i, Substructure.subset_closure ⟨i, rfl⟩⟩ =
          ⟨b i, Substructure.subset_closure ⟨i, rfl⟩⟩ := by
  constructor
  · rintro ⟨hEq, hRel⟩
    have hinj : Function.Injective (transfer (L := L) a b) := by
      intro x y hxy
      have h1 : (termFor a x).realize b = (termFor a y).realize b :=
        congrArg Subtype.val hxy
      have h2 := (hEq (termFor a x) (termFor a y)).2 h1
      exact Subtype.ext (by rw [← termFor_spec a x, ← termFor_spec a y, h2])
    have hsurj : Function.Surjective (transfer (L := L) a b) := by
      intro y
      obtain ⟨t, ht⟩ := (mem_closure_range_iff_exists_term b).1 y.2
      refine ⟨⟨t.realize a, (mem_closure_range_iff_exists_term a).2 ⟨t, rfl⟩⟩, ?_⟩
      exact Subtype.ext ((coe_transfer_eq hEq rfl).trans ht)
    refine ⟨{ toEquiv := Equiv.ofBijective _ ⟨hinj, hsurj⟩
              map_fun' := ?_
              map_rel' := ?_ }, ?_⟩
    · intro n F xs
      refine Subtype.ext ?_
      have hT : (Term.func F fun j ↦ termFor a (xs j)).realize a =
          ↑(Structure.funMap F xs) := by
        rw [Term.realize_func]
        show _ = Structure.funMap F fun j ↦ (↑(xs j) : M)
        congr 1
        funext j
        exact termFor_spec a (xs j)
      have h1 := coe_transfer_eq hEq hT
      rw [Term.realize_func] at h1
      exact h1
    · intro n R xs
      show Structure.RelMap R (fun j ↦ (↑(transfer a b (xs j)) : N)) ↔
        Structure.RelMap R fun j ↦ (↑(xs j) : M)
      have hb := hRel R fun j ↦ termFor a (xs j)
      rw [show (fun j ↦ ((termFor a (xs j)).realize a)) = fun j ↦ (↑(xs j) : M) from
        funext fun j ↦ termFor_spec a (xs j)] at hb
      exact hb.symm
    · intro i
      refine Subtype.ext ?_
      show (↑(transfer a b ⟨a i, Substructure.subset_closure ⟨i, rfl⟩⟩) : N) = _
      exact coe_transfer_eq hEq
        (show (Term.var i).realize a =
          ↑(⟨a i, Substructure.subset_closure ⟨i, rfl⟩⟩ :
            Substructure.closure L (Set.range a)) from rfl)
  · rintro ⟨e, he⟩
    have hval_a : ∀ t : L.Term (Fin k),
        (↑(t.realize fun i ↦ (⟨a i, Substructure.subset_closure ⟨i, rfl⟩⟩ :
          Substructure.closure L (Set.range a))) : M) = t.realize a := by
      intro t
      have := HomClass.realize_term
        (Substructure.closure L (Set.range a)).subtype (t := t)
        (v := fun i ↦ ⟨a i, Substructure.subset_closure ⟨i, rfl⟩⟩)
      exact this.symm.trans rfl
    have hval_b : ∀ t : L.Term (Fin k),
        (↑(t.realize fun i ↦ (⟨b i, Substructure.subset_closure ⟨i, rfl⟩⟩ :
          Substructure.closure L (Set.range b))) : N) = t.realize b := by
      intro t
      have := HomClass.realize_term
        (Substructure.closure L (Set.range b)).subtype (t := t)
        (v := fun i ↦ ⟨b i, Substructure.subset_closure ⟨i, rfl⟩⟩)
      exact this.symm.trans rfl
    have hmap : ∀ t : L.Term (Fin k),
        e (t.realize fun i ↦ ⟨a i, Substructure.subset_closure ⟨i, rfl⟩⟩) =
          t.realize fun i ↦ ⟨b i, Substructure.subset_closure ⟨i, rfl⟩⟩ := by
      intro t
      have := HomClass.realize_term (F := _ ≃[L] _) e (t := t)
        (v := fun i ↦ ⟨a i, Substructure.subset_closure ⟨i, rfl⟩⟩)
      rw [show (⇑e ∘ fun i ↦ (⟨a i, Substructure.subset_closure ⟨i, rfl⟩⟩ :
          Substructure.closure L (Set.range a))) =
          fun i ↦ (⟨b i, Substructure.subset_closure ⟨i, rfl⟩⟩ :
            Substructure.closure L (Set.range b)) from funext fun i ↦ he i] at this
      exact this.symm
    constructor
    · intro t₁ t₂
      constructor
      · intro h'
        have h₁ := congrArg e (Subtype.ext
          (((hval_a t₁).trans h').trans (hval_a t₂).symm))
        rw [hmap t₁, hmap t₂] at h₁
        rw [← hval_b t₁, ← hval_b t₂, h₁]
      · intro h'
        have hb := Subtype.ext (((hval_b t₁).trans h').trans (hval_b t₂).symm)
        rw [← hmap t₁, ← hmap t₂] at hb
        have h₂ := e.injective hb
        rw [← hval_a t₁, ← hval_a t₂, h₂]
    · intro n R ts
      have h₁ := e.map_rel' R fun i ↦
        (ts i).realize fun j ↦ ⟨a j, Substructure.subset_closure ⟨j, rfl⟩⟩
      rw [show (e.toFun ∘ fun i ↦ (ts i).realize fun j ↦
          (⟨a j, Substructure.subset_closure ⟨j, rfl⟩⟩ :
            Substructure.closure L (Set.range a))) =
          fun i ↦ (ts i).realize fun j ↦ ⟨b j, Substructure.subset_closure ⟨j, rfl⟩⟩
          from funext fun i ↦ hmap (ts i)] at h₁
      refine Iff.trans ?_ (Iff.trans h₁.symm ?_)
      · show Structure.RelMap R _ ↔ Structure.RelMap R fun i ↦
          (↑((ts i).realize fun j ↦
            (⟨a j, Substructure.subset_closure ⟨j, rfl⟩⟩ :
              Substructure.closure L (Set.range a))) : M)
        rw [show (fun i ↦ (↑((ts i).realize fun j ↦
            (⟨a j, Substructure.subset_closure ⟨j, rfl⟩⟩ :
              Substructure.closure L (Set.range a))) : M)) =
            fun i ↦ (ts i).realize a from funext fun i ↦ hval_a (ts i)]
      · show Structure.RelMap R (fun i ↦
          (↑((ts i).realize fun j ↦
            (⟨b j, Substructure.subset_closure ⟨j, rfl⟩⟩ :
              Substructure.closure L (Set.range b))) : N)) ↔ _
        rw [show (fun i ↦ (↑((ts i).realize fun j ↦
            (⟨b j, Substructure.subset_closure ⟨j, rfl⟩⟩ :
              Substructure.closure L (Set.range b))) : N)) =
            fun i ↦ (ts i).realize b from funext fun i ↦ hval_b (ts i)]

end ClosureEquiv

end FirstOrder.Language
