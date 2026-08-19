/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ComputableAge
import ComputableModelTheory.ModelTheory.Computable.PartialCePresentation

/-!
# Empty-capable uniform representations — CHMM Definition 2.1

`PartialAgeIn` is the formalization of **CHMM Definition 2.1**: an indexed sequence of
finitely generated structures whose domains are subsets of `ℕ`, with uniformly computable
generators and operations. The domains are consequently **uniformly c.e.**, not computable
— `domainAt_uniformly_ce` exhibits the single computable certificate that witnesses this,
and that c.e.-ness is the whole reason downstream selectors must stay partial.

Definition 2.1 has two halves, kept apart here on purpose: this file is the *computational*
family data, and the *semantic* claim about which isomorphism classes the family enumerates
lives in `PartialAgeSemantics` (`SameClass`, `HasHP`). `PartialCePresentationIn` is only the
per-member component, and `ComputableAgeIn` is the all-carrier-`ℕ` **fragment** of
Definition 2.1, not Definition 2.1 itself: it fixes every carrier to `ℕ`, so it can hold
neither a finite member nor (in a constant-free relational language) an empty one — which is
exactly why Theorem 2.8 needs the notion here as its input.

The family:

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

/-- **CHMM Definition 2.1** (computational half): an indexed family of finitely generated,
possibly-empty c.e. presentations, uniform in the index. Carriers are subsets of `ℕ`, given
by a uniform enumeration, so they are uniformly c.e. rather than computable. -/
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

/-! ### Rebasing to a stronger oracle

Every piece of computational data is carried over **definitionally**; only the computability proofs
are lifted. The family is unchanged — same structures, same enumeration, same generators, same
evaluators — and only the effectivity evidence is restated at a larger oracle. The `simp` lemmas are
what make that enforceable, and `mono_memberAt` is the one that lets member-level facts cross the
boundary untouched. -/

/-- The same representation, presented as evidence at a stronger oracle. -/
def mono {E : Set (ℕ →. ℕ)} (hOE : O ⊆ E) : PartialAgeIn E L where
  structureAt := A.structureAt
  enum? := A.enum?
  enum?_computableIn := RecursiveIn.mono hOE A.enum?_computableIn
  gens := A.gens
  gens_computableIn := RecursiveIn.mono hOE A.gens_computableIn
  funEval := A.funEval
  funEval_recursiveIn := RecursiveIn.mono hOE A.funEval_recursiveIn
  funEval_correct := A.funEval_correct
  relEval := A.relEval
  relEval_recursiveIn := RecursiveIn.mono hOE A.relEval_recursiveIn
  relEval_correct := A.relEval_correct
  generates := A.generates

@[simp] theorem mono_structureAt {E : Set (ℕ →. ℕ)} (hOE : O ⊆ E) :
    (A.mono hOE).structureAt = A.structureAt := rfl

@[simp] theorem mono_enum? {E : Set (ℕ →. ℕ)} (hOE : O ⊆ E) :
    (A.mono hOE).enum? = A.enum? := rfl

@[simp] theorem mono_gens {E : Set (ℕ →. ℕ)} (hOE : O ⊆ E) :
    (A.mono hOE).gens = A.gens := rfl

@[simp] theorem mono_funEval {E : Set (ℕ →. ℕ)} (hOE : O ⊆ E) :
    (A.mono hOE).funEval = A.funEval := rfl

@[simp] theorem mono_relEval {E : Set (ℕ →. ℕ)} (hOE : O ⊆ E) :
    (A.mono hOE).relEval = A.relEval := rfl

/-- The (possibly empty) carrier of member `i`: the enumerated values. -/
def domainAt (i : ℕ) : Set ℕ :=
  {x | ∃ m, A.enum? i m = Option.some x}

theorem mem_domainAt_iff {i x : ℕ} :
    x ∈ A.domainAt i ↔ ∃ m, A.enum? i m = Option.some x :=
  Iff.rfl

@[simp] theorem mono_domainAt {E : Set (ℕ →. ℕ)} (hOE : O ⊆ E) (i : ℕ) :
    (A.mono hOE).domainAt i = A.domainAt i := rfl

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

/-- The list form: every recorded generator lies in its member's carrier. -/
theorem mem_domainAt_of_mem_gens {i x : ℕ} (hx : x ∈ A.gens i) : x ∈ A.domainAt i := by
  obtain ⟨k, hk⟩ := List.mem_iff_get.1 hx
  exact hk ▸ A.gens_mem_domainAt k

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

/-- **Rebasing commutes with taking a member**, definitionally — so every member-level fact crosses
the oracle boundary with no transport. -/
@[simp] theorem mono_memberAt {E : Set (ℕ →. ℕ)} (hOE : O ⊆ E) (i : ℕ) :
    (A.mono hOE).memberAt i = (A.memberAt i).mono hOE :=
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
