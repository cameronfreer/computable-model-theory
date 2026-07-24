/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ComputableAge
import ComputableModelTheory.ModelTheory.Computable.PartialCePresentation

/-!
# Empty-capable uniform representations

The general representation notion CHMM Theorem 2.8 requires as **input**: a uniformly
computable indexed family of finitely generated structures whose members may be finite
or empty. `ComputableAgeIn` cannot serve — it fixes every carrier to ℕ, so it can hold
neither a finite member nor (in a constant-free relational language) an empty one.

A `PartialAgeIn` is that family:

* a uniform `Option`-valued enumeration `enum? i m` (the member's carrier is the set of
  enumerated values, possibly empty);
* uniform partial function/relation evaluators, correct on-domain;
* recorded finite generators `gens i` (possibly `[]`);
* the generation law — each member's carrier is exactly the term-closure of its
  recorded generators — from which domain-closure is derived.

`memberAt i` projects to the single-member possibly-empty layer
(`PartialCePresentationIn`), and `ComputableAgeIn.toPartialAge` embeds the all-ℕ
family (with the identity enumeration), so every existing all-ℕ example is a member of
the general setting. The two agree wherever both apply.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- An empty-capable uniformly computable representation: an indexed family of
finitely generated, possibly-empty c.e. presentations, uniform in the index. -/
structure PartialAgeIn (O : Set (ℕ →. ℕ)) (L : Language) [L.EffectiveLanguage] where
  /-- The structure data at each index, total on codes; only its on-domain behavior is
  meaningful. -/
  structureAt : ℕ → L.Structure ℕ
  /-- The uniform `Option`-valued enumeration; the member's carrier is its range. -/
  enum? : ℕ → ℕ → Option ℕ
  /-- The enumeration is computable uniformly in the index. -/
  enum?_computableIn : ComputableIn O fun p : ℕ × ℕ ↦ enum? p.1 p.2
  /-- The recorded finite generators, possibly `[]`. -/
  gens : ℕ → Tuple ℕ
  /-- The generators are computable uniformly in the index. -/
  gens_computableIn : ComputableIn O gens
  /-- The uniform partial function evaluator. -/
  funEval : ℕ → FunctionApplicationData L ℕ →. ℕ
  /-- The function evaluator is partial recursive uniformly in the index. -/
  funEval_recursiveIn :
    RecursiveIn O fun p : ℕ × FunctionApplicationData L ℕ ↦ funEval p.1 p.2
  /-- On domain-valued arguments, the evaluator halts with the interpretation. -/
  funEval_correct : ∀ (i : ℕ) (d : FunctionApplicationData L ℕ),
    (∀ k, ∃ m, enum? i m = Option.some (d.args k)) →
      @FunctionApplicationData.funMap L ℕ (structureAt i) d ∈ funEval i d
  /-- The uniform partial relation decider. -/
  relEval : ℕ → RelationApplicationData L ℕ →. Bool
  /-- The relation decider is partial recursive uniformly in the index. -/
  relEval_recursiveIn :
    RecursiveIn O fun p : ℕ × RelationApplicationData L ℕ ↦ relEval p.1 p.2
  /-- On domain-valued arguments, the decider halts with the truth value. -/
  relEval_correct : ∀ (i : ℕ) (d : RelationApplicationData L ℕ),
    (∀ k, ∃ m, enum? i m = Option.some (d.args k)) →
      ∃ b ∈ relEval i d, (b = true ↔ @RelationApplicationData.relMap L ℕ (structureAt i) d)
  /-- The generation law: each member's carrier is exactly the term-closure of its
  recorded generators. Domain-closure under functions follows from this. -/
  generates : ∀ (i x : ℕ),
    (∃ m, enum? i m = Option.some x) ↔
      ∃ T : L.Term (Fin (gens i).length),
        x = @Term.realize L ℕ (structureAt i) _ (Tuple.view (gens i)) T

namespace PartialAgeIn

variable (A : PartialAgeIn O L)

/-- The (possibly empty) carrier of member `i`: the enumerated values. -/
def domainAt (i : ℕ) : Set ℕ :=
  {x | ∃ m, A.enum? i m = Option.some x}

theorem mem_domainAt_iff {i x : ℕ} :
    x ∈ A.domainAt i ↔ ∃ m, A.enum? i m = Option.some x :=
  Iff.rfl

/-- The generation law, at the level of the carrier. -/
theorem mem_domainAt_iff_term {i x : ℕ} :
    x ∈ A.domainAt i ↔
      ∃ T : L.Term (Fin (A.gens i).length),
        x = @Term.realize L ℕ (A.structureAt i) _ (Tuple.view (A.gens i)) T :=
  A.generates i x

/-- Each generator lies in its member's carrier. -/
theorem gens_mem_domainAt {i : ℕ} (k : Fin (A.gens i).length) :
    (A.gens i).get k ∈ A.domainAt i :=
  (A.mem_domainAt_iff_term).2 ⟨Term.var k, by
    letI : L.Structure ℕ := A.structureAt i
    rw [Term.realize_var]
    rfl⟩

/-- Domain-closure under function interpretations, derived from the generation law. -/
theorem domainAt_closed {i n : ℕ} (f : L.Functions n) {v : Fin n → ℕ}
    (hv : ∀ k, v k ∈ A.domainAt i) :
    @Structure.funMap L ℕ (A.structureAt i) n f v ∈ A.domainAt i := by
  letI : L.Structure ℕ := A.structureAt i
  choose Ts hTs using fun k ↦ (A.mem_domainAt_iff_term).1 (hv k)
  refine (A.mem_domainAt_iff_term).2 ⟨Term.func f Ts, ?_⟩
  rw [Term.realize_func]
  exact congrArg _ (funext fun k ↦ hTs k)

/-- The single-member projection: member `i` as a possibly-empty presentation. -/
noncomputable def memberAt (i : ℕ) : PartialCePresentationIn O L where
  str := A.structureAt i
  enum? := A.enum? i
  enum?_computableIn :=
    (A.enum?_computableIn.comp ((ComputableIn.const i).pair ComputableIn.id)).of_eq
      fun _ ↦ rfl
  domain_closed := fun _ f _ hv ↦ A.domainAt_closed f hv
  funEval := A.funEval i
  funEval_recursiveIn :=
    (A.funEval_recursiveIn.comp ((ComputableIn.const i).pair ComputableIn.id)).of_eq
      fun _ ↦ rfl
  funEval_correct := A.funEval_correct i
  relEval := A.relEval i
  relEval_recursiveIn :=
    (A.relEval_recursiveIn.comp ((ComputableIn.const i).pair ComputableIn.id)).of_eq
      fun _ ↦ rfl
  relEval_correct := A.relEval_correct i

@[simp]
theorem memberAt_str (i : ℕ) : (A.memberAt i).str = A.structureAt i :=
  rfl

@[simp]
theorem memberAt_domain (i : ℕ) : (A.memberAt i).domain = A.domainAt i :=
  rfl

end PartialAgeIn

namespace ComputableAgeIn

variable (K : ComputableAgeIn O L)

/-- Each member of an all-ℕ computable age is a computable structure. -/
theorem isComputableStructureAt (i : ℕ) :
    @IsComputableStructureIn O L _ (K.structureAt i) :=
  @IsComputableStructureIn.mk O L _ (K.structureAt i)
    (K.funMap_computableIn.comp ((ComputableIn.const i).pair ComputableIn.id))
    (by
      obtain ⟨inst, hcomp⟩ := K.relMap_computablePredIn
      exact ⟨fun d ↦ inst (i, d),
        (hcomp.comp ((ComputableIn.const i).pair ComputableIn.id)).of_eq
          fun _ ↦ rfl⟩)

open Classical in
/-- The embedding of the all-ℕ family into the empty-capable general setting: the
identity enumeration presents every member on its full carrier ℕ. -/
noncomputable def toPartialAge : PartialAgeIn O L where
  structureAt := K.structureAt
  enum? _ m := Option.some m
  enum?_computableIn := ComputableIn.option_some.comp ComputableIn.snd
  gens := K.gens
  gens_computableIn := K.gens_computableIn
  funEval i d := Part.some (@FunctionApplicationData.funMap L ℕ (K.structureAt i) d)
  funEval_recursiveIn := K.funMap_computableIn
  funEval_correct := fun _ _ _ ↦ Part.mem_some _
  relEval i d :=
    Part.some (decide (@RelationApplicationData.relMap L ℕ (K.structureAt i) d))
  relEval_recursiveIn := by
    obtain ⟨inst, hcomp⟩ := K.relMap_computablePredIn
    have h : ComputableIn O fun p : ℕ × RelationApplicationData L ℕ ↦
        @decide (@RelationApplicationData.relMap L ℕ (K.structureAt p.1) p.2)
          (inst (p.1, p.2)) := hcomp
    exact h.of_eq fun _ ↦ decide_eq_decide.2 Iff.rfl
  relEval_correct := fun _ _ _ ↦ ⟨_, Part.mem_some _, decide_eq_true_iff⟩
  generates := fun i x ↦ by
    constructor
    · intro _
      exact (@Tuple.generates_iff L ℕ (K.structureAt i) (K.gens i)).1
        (K.generates i) x |>.imp fun _ h ↦ h.symm
    · intro _
      exact ⟨x, rfl⟩

/-- The all-ℕ bridge presents every member on its full carrier ℕ. -/
@[simp]
theorem toPartialAge_domainAt (i : ℕ) : K.toPartialAge.domainAt i = Set.univ := by
  ext x
  exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨x, rfl⟩⟩

end ComputableAgeIn

end FirstOrder.Language
