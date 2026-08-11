/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.RepresentationWitnessTransport
import ComputableModelTheory.ModelTheory.Computable.ConstantExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# CHP is not invariant under computable isomorphism of representations

The counterexample behind the boundary recorded in `RepresentationWitnessTransport`: two
representation-isomorphic families, one with CHP and one without. Kernel-checked, so the negative
result the transport API stops at is a theorem rather than an argument.

Both families live over the one-constant language with the constant interpreted as `7`, so **every
member has carrier `{7}`** whatever its recorded generators — the empty tuple already generates a
nonempty substructure. The families therefore differ *only* in their recorded generator tuples:

* `chpWide` records `i` copies of `7` at member `i`, so every tuple width occurs;
* `chpNarrow` records `[7]` at every member, so only width one occurs.

They are isomorphic as representations by the domain-restricted identity at constant index maps —
legitimately, since all their members are isomorphic structures, which is all CHMM Definition 2.3
asks. `chpWide` has CHP: answer a query `s` with the member of width `s.length`. `chpNarrow` fails
CHP outright at the carrier-valid query `s = []`, since every candidate has exactly one recorded
generator and the required length equation `1 = 0` is unsatisfiable.

The moral is precise: `PartialAgeIn.MappedPartialCHPIn` pins the range tuple to a query supplied from *outside*,
and a representation isomorphism carries no information about recorded generator tuples — not even
their lengths. A transport controls the image of the selected member's generators and cannot force
that image to be the query. Length compatibility alone would not repair this; the fix, if ever
needed, is genuine generator equality on the relevant cover.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

section

variable {O : Set (ℕ →. ℕ)}

attribute [local instance] constStructure

/-! ### The family constructor

Only `gens` is a parameter. Everything else — the structure, the enumeration, the evaluators — is
fixed, which is what makes the two families below differ in exactly one respect. -/

/-- A constant-language family whose every member has carrier `{7}`, with the recorded generator
tuples supplied. The generators must consist of `7`s, since anything else would have to lie in the
carrier. -/
noncomputable def constAgeOf (g : ℕ → List ℕ) (hg : ComputableIn O g)
    (h7 : ∀ i, ∀ x ∈ g i, x = 7) : PartialAgeIn O constLang where
  structureAt _ := constStructure
  enum? _ _ := Option.some 7
  enum?_computableIn := ComputableIn.const _
  gens := g
  gens_computableIn := hg
  funEval _ _ := Part.some 7
  funEval_recursiveIn := ComputableIn.const 7
  funEval_correct := fun _ d _ ↦ by
    match d with
    | ⟨0, .c, _⟩ => exact Part.mem_some _
    | ⟨_ + 1, f, _⟩ => exact isEmptyElim f
  relEval _ _ := Part.none
  relEval_recursiveIn := RecursiveIn.none
  relEval_correct := fun _ d _ ↦ isEmptyElim d
  generates := fun i x ↦ by
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨Term.func ConstFunctions.c (fun k ↦ k.elim0), (Option.some_inj.1 hm).symm⟩
    · rintro ⟨T, rfl⟩
      exact ⟨0, congrArg Option.some
        (constStructure_realize_eq_seven _
          (fun k ↦ h7 i _ (List.get_mem _ _)) T).symm⟩

variable {g₁ g₂ : ℕ → List ℕ} {hg₁ : ComputableIn O g₁} {hg₂ : ComputableIn O g₂}
  {h₁ : ∀ i, ∀ x ∈ g₁ i, x = 7} {h₂ : ∀ i, ∀ x ∈ g₂ i, x = 7}

/-- **Every carrier is `{7}`** — independently of the recorded generators. -/
theorem mem_constAgeOf_iff (g : ℕ → List ℕ) (hg : ComputableIn O g)
    (h7 : ∀ i, ∀ x ∈ g i, x = 7) (i x : ℕ) :
    x ∈ (constAgeOf g hg h7).domainAt i ↔ x = 7 := by
  constructor
  · rintro ⟨m, hm⟩
    exact (Option.some_inj.1 hm).symm
  · rintro rfl
    exact ⟨0, rfl⟩

/-! ### The isomorphism

All members of all these families are the same structure, so the domain-restricted identity is an
isomorphism between any two of them. It halts exactly on `{7}`; a total identity would overclaim
the domain, which is the distinction `idFun` exists to keep. -/

/-- The domain-restricted identity between any two members of any two such families. -/
noncomputable def constIdIso (i j : ℕ) :
    PartialCeIsoIn O ((constAgeOf g₁ hg₁ h₁).memberAt i)
      ((constAgeOf g₂ hg₂ h₂).memberAt j) where
  toFun x := (constAgeOf g₁ hg₁ h₁).idFun (i, x)
  invFun y := (constAgeOf g₁ hg₁ h₁).idFun (i, y)
  toFun_recursiveIn :=
    ((constAgeOf g₁ hg₁ h₁).idFun_recursiveIn.comp
      ((ComputableIn.const i).pair ComputableIn.id))
  invFun_recursiveIn :=
    ((constAgeOf g₁ hg₁ h₁).idFun_recursiveIn.comp
      ((ComputableIn.const i).pair ComputableIn.id))
  toFun_dom := fun x ↦ (constAgeOf g₁ hg₁ h₁).idFun_dom i x
  invFun_dom := fun y ↦
    ((constAgeOf g₁ hg₁ h₁).idFun_dom i y).trans
      ((mem_constAgeOf_iff g₁ hg₁ h₁ i y).trans (mem_constAgeOf_iff g₂ hg₂ h₂ j y).symm)
  toFun_mem := fun h ↦ by
    obtain ⟨rfl, hx⟩ := (constAgeOf g₁ hg₁ h₁).mem_idFun.1 h
    exact (mem_constAgeOf_iff g₂ hg₂ h₂ j _).2 ((mem_constAgeOf_iff g₁ hg₁ h₁ i _).1 hx)
  invFun_toFun := fun h ↦ by
    obtain ⟨rfl, hx⟩ := (constAgeOf g₁ hg₁ h₁).mem_idFun.1 h
    exact (constAgeOf g₁ hg₁ h₁).mem_idFun.2 ⟨rfl, hx⟩
  toFun_invFun := fun h ↦ by
    obtain ⟨rfl, hx⟩ := (constAgeOf g₁ hg₁ h₁).mem_idFun.1 h
    exact (constAgeOf g₁ hg₁ h₁).mem_idFun.2 ⟨rfl, hx⟩
  toFun_funMap := fun n f v w hw ↦ by
    match n, f with
    | 0, .c =>
      exact (constAgeOf g₁ hg₁ h₁).mem_idFun.2
        ⟨rfl, (mem_constAgeOf_iff g₁ hg₁ h₁ i 7).2 rfl⟩
    | _ + 1, f => exact isEmptyElim f
  toFun_relMap := fun _ R _ _ _ ↦ isEmptyElim R

/-- The identity really is the identity on values — the fact every coordinate row below needs. -/
theorem constIdIso_val (i j : ℕ) (x : ((constAgeOf g₁ hg₁ h₁).memberAt i).domain) :
    (((constIdIso (g₂ := g₂) (hg₂ := hg₂) (h₂ := h₂) i j).toEquiv.toEmbedding x :
      ((constAgeOf g₂ hg₂ h₂).memberAt j).domain) : ℕ) = (x : ℕ) :=
  ((constAgeOf g₁ hg₁ h₁).mem_idFun.1
    ((constIdIso (g₂ := g₂) (hg₂ := hg₂) (h₂ := h₂) i j).toSubtypeFun_mem x)).1

/-- A cover along the constant index map `0`. Any index map would do — all members are isomorphic
— and a constant one makes the point that CHMM Definition 2.3 constrains nothing here. -/
noncomputable def constCover :
    RepresentationCoverIn O (constAgeOf g₁ hg₁ h₁) (constAgeOf g₂ hg₂ h₂) where
  indexMap := fun _ ↦ 0
  indexMap_computableIn := ComputableIn.const 0
  isoAt i := constIdIso (g₂ := g₂) (hg₂ := hg₂) (h₂ := h₂) i 0
  toFun_uniform := (constAgeOf g₁ hg₁ h₁).idFun_recursiveIn.of_eq fun _ ↦ rfl
  invFun_uniform := (constAgeOf g₁ hg₁ h₁).idFun_recursiveIn.of_eq fun _ ↦ rfl

/-! ### The two families -/

/-- **Wide**: member `i` records `i` copies of `7`, so every tuple width occurs. -/
private theorem replicate_computableIn :
    ComputableIn O fun i : ℕ ↦ List.replicate i 7 := by
  have h : Primrec fun i : ℕ ↦ (List.range i).map fun _ : ℕ ↦ (7 : ℕ) :=
    Primrec.list_map Primrec.list_range (Primrec.const (7 : ℕ)).to₂
  exact h.to_comp.computableIn.of_eq fun i ↦ by
    rw [List.map_const', List.length_range]

noncomputable abbrev chpWide : PartialAgeIn O constLang :=
  constAgeOf (fun i ↦ List.replicate i 7) replicate_computableIn
    fun _ _ hx ↦ List.eq_of_mem_replicate hx

/-- **Narrow**: every member records `[7]`, so only width one occurs. -/
noncomputable abbrev chpNarrow : PartialAgeIn O constLang :=
  constAgeOf (fun _ ↦ [7]) (ComputableIn.const _) fun _ x hx ↦ by simpa using hx

/-- The two are computably isomorphic as representations, by the domain-restricted identity in
each direction. -/
noncomputable def chpIso : RepresentationIsoIn O (chpWide (O := O)) (chpNarrow (O := O)) where
  forward := constCover
  backward := constCover

/-! ### Wide has CHP -/

/-- A carrier-valid query over these families is a tuple of `7`s. -/
private theorem query_entries {g : ℕ → List ℕ} {hg : ComputableIn O g}
    {h7 : ∀ i, ∀ x ∈ g i, x = 7} {e : ℕ} {s : List ℕ}
    (hs : ∀ x ∈ s, x ∈ (constAgeOf g hg h7).domainAt e) : ∀ x ∈ s, x = 7 :=
  fun x hx ↦ (mem_constAgeOf_iff g hg h7 e x).1 (hs x hx)

/-- **`chpWide` has CHP**: answer the query `s` with the member recording `s.length` generators.
Every width is available, and all values are `7`, so the coordinate conditions are immediate. -/
theorem chpWide_chp : PartialAgeIn.MappedPartialCHPIn O (chpWide (O := O)) := by
  refine ⟨fun _ s ↦ Part.some s.length,
    (Computable.list_length.comp Computable.snd).computableIn, ?_⟩
  intro e s hs
  have hlen : ((chpWide (O := O)).gens s.length).length = s.length :=
    List.length_replicate
  refine ⟨s.length, Part.mem_some _, hlen,
    (constIdIso (g₂ := fun i ↦ List.replicate i 7) s.length e).toEquiv.toEmbedding, fun k ↦ ?_⟩
  refine (constIdIso_val (g₂ := fun i ↦ List.replicate i 7) s.length e _).trans ?_
  have hl : ((chpWide (O := O)).gens s.length).get k = 7 :=
    List.eq_of_mem_replicate (List.get_mem _ _)
  show ((chpWide (O := O)).gens s.length).get k = s.get (Fin.cast hlen k)
  rw [hl]
  exact (query_entries hs _ (List.get_mem _ _)).symm

/-! ### Narrow does not -/

/-- **`chpNarrow` fails CHP**, at the carrier-valid empty query. Every candidate member records
exactly one generator, so the length equation reads `1 = 0`.

The query is valid vacuously, so no carrier condition rescues it — this is a failure of the
recorded generator *widths*, which is exactly the data a representation isomorphism does not
carry. -/
theorem chpNarrow_not_chp : ¬ PartialAgeIn.MappedPartialCHPIn O (chpNarrow (O := O)) := by
  rintro ⟨sel, -, hspec⟩
  obtain ⟨c, -, hlen, -⟩ := hspec 0 [] (by simp)
  have : (1 : ℕ) = 0 := hlen
  exact absurd this (by decide)

/-! ### The separation -/

/-- **CHP is not invariant under computable isomorphism of representations.** Two
representation-isomorphic families, one with CHP and one without.

This is the theorem the transport API's boundary rests on: no strengthening of the transport
machinery can establish general CHP invariance, because it is false. -/
theorem test_chp_not_invariant :
    ∃ A B : PartialAgeIn O constLang,
      Nonempty (RepresentationIsoIn O A B) ∧
        PartialAgeIn.MappedPartialCHPIn O A ∧ ¬ PartialAgeIn.MappedPartialCHPIn O B :=
  ⟨chpWide, chpNarrow, ⟨chpIso⟩, chpWide_chp, chpNarrow_not_chp⟩

/-- The two families really do differ only in recorded generator widths: their carriers agree
everywhere. Without this row the separation could be dismissed as a carrier artifact. -/
theorem test_chp_families_same_carriers (i j x : ℕ) :
    (x ∈ (chpWide (O := O)).domainAt i ↔ x = 7) ∧
      (x ∈ (chpNarrow (O := O)).domainAt j ↔ x = 7) :=
  ⟨mem_constAgeOf_iff _ _ _ i x, mem_constAgeOf_iff _ _ _ j x⟩

/-- And the widths are what differ. -/
theorem test_chp_families_differ (i : ℕ) :
    ((chpWide (O := O)).gens i).length = i ∧ ((chpNarrow (O := O)).gens i).length = 1 :=
  ⟨List.length_replicate, rfl⟩

end

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.chpWide_chp
#assert_standard_axioms FirstOrder.Language.chpNarrow_not_chp
#assert_standard_axioms FirstOrder.Language.test_chp_not_invariant
#assert_standard_axioms FirstOrder.Language.test_chp_families_same_carriers
#assert_standard_axioms FirstOrder.Language.test_chp_families_differ
