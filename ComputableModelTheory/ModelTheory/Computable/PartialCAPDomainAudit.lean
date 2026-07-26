/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialCAP
import ComputableModelTheory.ModelTheory.Computable.GraphExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for the partial amalgamation selector's domain behavior

The row of `PartialCAPIn`'s contract that the all-ℕ adapter structurally cannot reach: on a
full carrier every raw span is carrier-valid, so nothing there exhibits a selector that
actually **diverges**. This module does, on a proper finite carrier — which is enough to
prove the interface point without dragging in an undecidable carrier, a harder and separate
computability question.

The fixture is a **rigid** two-element relational family. Every member has carrier `{0,1}`,
recorded generators `[0, 1]`, and the single binary relation is interpreted asymmetrically,
`R x y ↔ x = 0`. Rigidity matters: with a symmetric edge the swap would be an automorphism and
the non-embedding row below would not be a non-embedding. (This is why the path-graph fixture of
`GraphExample` is unsuitable here.) Everything is audit-local; none of it is production API.

This file establishes the fixture and its rigidity. The selector and the four-row matrix follow.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)}

/-! ### A rigid two-element structure -/

/-- The rigid interpretation: `R x y` holds exactly when the first argument is `0`. Asymmetric,
so the transposition of `{0,1}` is not an embedding. -/
@[reducible] def rigidStructure : Language.graph.Structure ℕ where
  RelMap | .adj => fun x ↦ x 0 = 0

section

attribute [local instance] rigidStructure

private theorem rigid_relMap_iff (d : RelationApplicationData Language.graph ℕ) :
    ((d.argsList.head?).getD 0 = 0) ↔ d.relMap :=
  match d with
  | ⟨0, r, _⟩ => isEmptyElim r
  | ⟨1, r, _⟩ => isEmptyElim r
  | ⟨2, .adj, _⟩ => Iff.rfl
  | ⟨_ + 3, r, _⟩ => isEmptyElim r

/-- Terms over a relational language are variables. -/
private theorem graph_term_eq_var {k : ℕ} (T : Language.graph.Term (Fin k)) :
    ∃ i, T = Term.var i := by
  cases T with
  | var i => exact ⟨i, rfl⟩
  | func f _ => exact isEmptyElim f

/-! ### The fixture family -/

/-- A rigid two-element family: every member has carrier `{0,1}` with the asymmetric relation,
and records `[0, 1]` as its generators. -/
def rigidFamily : PartialAgeIn O Language.graph where
  structureAt _ := rigidStructure
  enum? _ m := Option.some (m % 2)
  enum?_computableIn :=
    (Primrec.option_some.comp (Primrec.nat_mod.comp Primrec.snd
      (Primrec.const 2))).to_comp.computableIn
  gens _ := [0, 1]
  gens_computableIn := ComputableIn.const _
  funEval _ _ := Part.some 0
  funEval_recursiveIn := ComputableIn.const 0
  funEval_correct := fun _ d _ ↦ isEmptyElim d
  relEval _ d := Part.some (decide ((d.argsList.head?).getD 0 = 0))
  relEval_recursiveIn := by
    have hval : ComputableIn O fun p : ℕ × RelationApplicationData Language.graph ℕ ↦
        (p.2.argsList.head?).getD 0 :=
      (Primrec.option_getD.comp
        (Primrec.list_head?.comp
          (RelationApplicationData.primrec_argsList.comp Primrec.snd))
        (Primrec.const 0)).to_comp.computableIn
    exact ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp hval
      (ComputableIn.const 0)
  relEval_correct := fun _ d _ ↦ ⟨_, Part.mem_some _, decide_eq_true_iff.trans
    (rigid_relMap_iff d)⟩
  generates := fun _ x ↦ by
    constructor
    · rintro ⟨m, hm⟩
      have hx : x = m % 2 := (Option.some_inj.1 hm).symm
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · exact ⟨Term.var 0, by rw [hx, h]; rfl⟩
      · exact ⟨Term.var 1, by rw [hx, h]; rfl⟩
    · rintro ⟨T, hT⟩
      obtain ⟨i, rfl⟩ := graph_term_eq_var T
      refine ⟨x, ?_⟩
      rw [hT]
      show Option.some _ = Option.some _
      rw [Term.realize_var]
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl

/-! ### The carrier is exactly `{0, 1}` -/

@[simp]
theorem rigidFamily_domainAt (i : ℕ) :
    (rigidFamily (O := O)).domainAt i = {0, 1} := by
  ext x
  constructor
  · rintro ⟨m, hm⟩
    have hx : x = m % 2 := (Option.some_inj.1 hm).symm
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · exact Or.inl (by rw [hx, h])
    · exact Or.inr (by rw [hx, h]; rfl)
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- Gate: the fixture's members are genuinely finite and proper — `2` is outside every
carrier, which is what makes an off-carrier input available at all. -/
theorem test_rigidFamily_carrier (i : ℕ) :
    (0 : ℕ) ∈ (rigidFamily (O := O)).domainAt i ∧
      (1 : ℕ) ∈ (rigidFamily (O := O)).domainAt i ∧
      (2 : ℕ) ∉ (rigidFamily (O := O)).domainAt i := by
  refine ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ?_⟩
  rw [rigidFamily_domainAt]
  simp

/-- Gate: the fixture is **rigid** — the transposition of `{0,1}` does not preserve the
relation, so the swap is not an embedding and the non-embedding row of the matrix is genuinely
a non-embedding. -/
theorem test_rigidFamily_asymmetric :
    @Structure.RelMap Language.graph ℕ rigidStructure 2 .adj ![0, 1] ∧
      ¬@Structure.RelMap Language.graph ℕ rigidStructure 2 .adj ![1, 0] := by
  refine ⟨rfl, ?_⟩
  intro h
  exact absurd (h : (1 : ℕ) = 0) Nat.one_ne_zero

end

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_rigidFamily_carrier
#assert_standard_axioms FirstOrder.Language.test_rigidFamily_asymmetric
