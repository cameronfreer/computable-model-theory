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

This file establishes the fixture, its rigidity, and the selector. Two audit-local facts make
the matrix immediate: `rigidGuard_eq_true_iff_carrierValidSpan` and
`rigidSelector_dom_iff_carrierValidSpan`. The latter is *stronger* than `PartialCAPIn` demands —
the contract only requires halting on carrier-valid input, not divergence elsewhere — but it is
a harmless and useful theorem about this particular fixture, and it is what makes the
off-carrier row a genuine divergence rather than an absence of promise.

`rigidFamily_partialCAPIn` is the witness; the four rows then exercise its clauses:

| input `t` | row | behaviour |
| --------- | --- | --------- |
| `[0]`     | wrong length  | carrier-valid, selector halts, unconditional clauses hold |
| `[1,0]`   | non-embedding | carrier-valid and well-formed, breaks `R`, still halts |
| `[2,0]`   | off-carrier   | selector reduces to `Part.none`, hence genuinely not `Dom` |
| `[0,1]`   | actual        | identity span; selected diagram actual and commuting |
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

/-! ### Rigidity, semantically

The asymmetry gate says the swap is not an automorphism. What the amalgamation rows actually
need is stronger and is proved here: *every* embedding between two members is the identity on
underlying values. `0` is pinned by preservation of `R 0 0`, and `1` follows from injectivity
together with carrier membership. Consequently every leg of an actual span is the identity, so
the canonical output square commutes. -/

private theorem rigid_mem_zero (i : ℕ) :
    (0 : ℕ) ∈ ((rigidFamily (O := O)).memberAt i).domain :=
  ⟨0, rfl⟩

private theorem rigid_mem_one (i : ℕ) :
    (1 : ℕ) ∈ ((rigidFamily (O := O)).memberAt i).domain :=
  ⟨1, rfl⟩

/-- Carrier membership, read off the computed carrier without rewriting under a subtype. -/
private theorem rigid_eq_zero_or_one {i : ℕ}
    (y : ((rigidFamily (O := O)).memberAt i).domain) : (y : ℕ) = 0 ∨ (y : ℕ) = 1 :=
  (Set.ext_iff.1 (rigidFamily_domainAt (O := O) i) (y : ℕ)).1 y.2

/-- **Every member embedding of the rigid family is the identity on values.** -/
theorem rigid_memberEmbedding_eq_identity {i j : ℕ}
    (f : ((rigidFamily (O := O)).memberAt i).domain ↪[Language.graph]
      ((rigidFamily (O := O)).memberAt j).domain)
    (x : ((rigidFamily (O := O)).memberAt i).domain) : ((f x : _) : ℕ) = (x : ℕ) := by
  -- `0` is pinned by preservation of `R 0 0`.
  have hzero : ((f ⟨0, rigid_mem_zero i⟩ : _) : ℕ) = 0 :=
    (f.map_rel' .adj ![⟨0, rigid_mem_zero i⟩, ⟨0, rigid_mem_zero i⟩]).2 rfl
  -- `1` then follows from injectivity: it cannot also go to `0`.
  have hone : ((f ⟨1, rigid_mem_one i⟩ : _) : ℕ) = 1 := by
    rcases rigid_eq_zero_or_one (f ⟨1, rigid_mem_one i⟩) with h | h
    · exfalso
      have : f ⟨1, rigid_mem_one i⟩ = f ⟨0, rigid_mem_zero i⟩ :=
        Subtype.ext (h.trans hzero.symm)
      exact absurd (congrArg Subtype.val (f.injective this) : (1 : ℕ) = 0) Nat.one_ne_zero
    · exact h
  -- every carrier element is `0` or `1`
  rcases rigid_eq_zero_or_one x with h | h
  · rw [show x = ⟨0, rigid_mem_zero i⟩ from Subtype.ext h, hzero]
  · rw [show x = ⟨1, rigid_mem_one i⟩ from Subtype.ext h, hone]

/-- Gate: the fixture is **rigid** — the transposition of `{0,1}` does not preserve the
relation, so the swap is not an embedding and the non-embedding row of the matrix is genuinely
a non-embedding. -/
theorem test_rigidFamily_asymmetric :
    @Structure.RelMap Language.graph ℕ rigidStructure 2 .adj ![0, 1] ∧
      ¬@Structure.RelMap Language.graph ℕ rigidStructure 2 .adj ![1, 0] := by
  refine ⟨rfl, ?_⟩
  intro h
  exact absurd (h : (1 : ℕ) = 0) Nat.one_ne_zero

/-! ### The identity output data

Every member's carrier is `{0,1}` with the same structure, so the identity on values is an
embedding between any two members, and the data `⟨d, a, [0,1]⟩` is realized by it. This makes
the canonical diagram's unconditional clauses uniform in the input indices. -/

/-- The identity embedding between any two members. -/
def rigidIdentityEmb (d a : ℕ) :
    ((rigidFamily (O := O)).memberAt d).domain ↪[Language.graph]
      ((rigidFamily (O := O)).memberAt a).domain where
  toFun x := ⟨x.1, x.2⟩
  inj' _ _ h := Subtype.ext (congrArg Subtype.val h : (_ : ℕ) = _)
  map_fun' f _ := isEmptyElim f
  map_rel' _ _ := Iff.rfl

/-- The identity data between any two members is realized. -/
theorem rigidIdentityData_partialIsEmbedding (d a : ℕ) :
    (rigidFamily (O := O)).PartialIsEmbedding ⟨d, a, [0, 1]⟩ :=
  ⟨rigidIdentityEmb d a, rfl, fun _ ↦ rfl⟩

/-! ### The selector

The guard is built up in stages so that no fused `Primrec` chain ever runs over the encoded
span structure: the list predicate is proved once, composed separately with each range-tuple
projection, and the two booleans combined only afterwards. -/

private theorem all_le_one_computableIn :
    ComputableIn O fun l : List ℕ ↦ l.all fun x ↦ decide (x ≤ 1) := by
  have hstep : ComputableIn₂ O fun (_ : List ℕ) (p : ℕ × Bool) ↦
      (decide (p.1 ≤ 1) && p.2) :=
    ((Primrec.and.comp
      ((Primrec.nat_le.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)).decide)
      (Primrec.snd.comp Primrec.snd)).to_comp.computableIn).to₂
  have h : ComputableIn O fun l : List ℕ ↦
      l.foldr (fun b s ↦ decide (b ≤ 1) && s) true :=
    ComputableIn.list_foldr ComputableIn.id (ComputableIn.const true) hstep
  refine h.of_eq fun l ↦ ?_
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.foldr_cons, ih, List.all_cons]

/-- The selector's guard: every entry of both range tuples is at most `1`. -/
def rigidGuard (S : PotentialSpanData) : Bool :=
  (S.left.rangeTuple.all fun x ↦ decide (x ≤ 1)) &&
    (S.right.rangeTuple.all fun x ↦ decide (x ≤ 1))

private theorem all_le_one_iff_carrierValid (F : PotentialEmbeddingData) :
    (F.rangeTuple.all fun x ↦ decide (x ≤ 1)) = true ↔
      (rigidFamily (O := O)).CarrierValid F := by
  rw [List.all_eq_true]
  constructor
  · intro h x hx
    rw [rigidFamily_domainAt]
    have hle : x ≤ 1 := of_decide_eq_true (h x hx)
    have : x = 0 ∨ x = 1 := by omega
    rcases this with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · intro h x hx
    have hmem := h x hx
    rw [rigidFamily_domainAt] at hmem
    rcases hmem with h' | h'
    · exact decide_eq_true (by rw [h']; exact Nat.zero_le 1)
    · exact decide_eq_true (by rw [show x = 1 from h'])

/-- The guard decides carrier validity of the span. -/
theorem rigidGuard_eq_true_iff_carrierValidSpan (S : PotentialSpanData) :
    rigidGuard S = true ↔ (rigidFamily (O := O)).CarrierValidSpan S := by
  rw [rigidGuard, Bool.and_eq_true]
  exact and_congr (all_le_one_iff_carrierValid _) (all_le_one_iff_carrierValid _)

/-- The canonical output: both codomains mapped identically into the member at index `0`. -/
def rigidDiagram (S : PotentialSpanData) : AmalgamationDiagramData :=
  ⟨⟨S.left.codIdx, 0, [0, 1]⟩, ⟨S.right.codIdx, 0, [0, 1]⟩⟩

/-- The selector, as a total computable `Option` before crossing to `Part`, so that its
divergence off-carrier is a literal `none` branch. -/
def rigidSelectorOption (S : PotentialSpanData) : Option AmalgamationDiagramData :=
  bif rigidGuard S then Option.some (rigidDiagram S) else Option.none

/-- The amalgamation selector of the rigid fixture. -/
def rigidSelector (S : PotentialSpanData) : Part AmalgamationDiagramData :=
  (rigidSelectorOption S : Option AmalgamationDiagramData)

private theorem rigidSelector_eq (S : PotentialSpanData) :
    rigidSelector S =
      bif rigidGuard S then Part.some (rigidDiagram S) else Part.none := by
  rw [rigidSelector, rigidSelectorOption]
  cases rigidGuard S <;> rfl

/-- **The selector converges exactly on carrier-valid spans.** Stronger than `PartialCAPIn`
requires — the contract only demands halting on carrier-valid input — but true of this
fixture, and it makes both the halting obligation and the off-carrier divergence immediate. -/
theorem rigidSelector_dom_iff_carrierValidSpan (S : PotentialSpanData) :
    (rigidSelector S).Dom ↔ (rigidFamily (O := O)).CarrierValidSpan S := by
  rw [← rigidGuard_eq_true_iff_carrierValidSpan (O := O), rigidSelector_eq]
  cases h : rigidGuard S with
  | false => simp
  | true => simp

/-! ### The witness -/

private theorem rigidIdentityData_computableIn (g : PotentialSpanData → PotentialEmbeddingData)
    (hg : ComputableIn O g) :
    ComputableIn O fun S ↦
      (PotentialEmbeddingData.ofTriple ((g S).codIdx, 0, [0, 1])) :=
  (PotentialEmbeddingData.ofTriple_computableIn).comp
    ((PotentialEmbeddingData.codIdx_computable.comp hg).pair
      ((ComputableIn.const 0).pair (ComputableIn.const [0, 1])))

theorem rigidSelector_recursiveIn : RecursiveIn O rigidSelector := by
  have hguard : ComputableIn O rigidGuard :=
    (Primrec.and.to_comp.computableIn₂).comp
      (all_le_one_computableIn.comp
        (PotentialEmbeddingData.rangeTuple_computable.comp
          PotentialSpanData.left_computable))
      (all_le_one_computableIn.comp
        (PotentialEmbeddingData.rangeTuple_computable.comp
          PotentialSpanData.right_computable))
  have hleft := rigidIdentityData_computableIn (O := O) PotentialSpanData.left
    PotentialSpanData.left_computable
  have hright := rigidIdentityData_computableIn (O := O) PotentialSpanData.right
    PotentialSpanData.right_computable
  -- The diagram-valued composition trips the `ofEquiv` whnf problem, so cross through
  -- `encode_iff` on the pair rather than unfolding `ofPair`.
  have hdiag : ComputableIn O fun S ↦ rigidDiagram S :=
    ComputableIn.encode_iff.1
      ((ComputableIn.encode.comp (hleft.pair hright)).of_eq fun _ ↦ rfl)
  have hopt : ComputableIn O rigidSelectorOption :=
    ComputableIn.cond hguard (ComputableIn.option_some.comp hdiag)
      (ComputableIn.const Option.none)
  exact ComputableIn.ofOption hopt

private theorem eq_rigidDiagram_of_mem {S : PotentialSpanData}
    {D : AmalgamationDiagramData} (h : D ∈ rigidSelector S) : D = rigidDiagram S := by
  rw [rigidSelector_eq] at h
  cases hg : rigidGuard S with
  | false => rw [hg] at h; exact absurd h (by simp)
  | true => rw [hg] at h; exact Part.mem_some_iff.1 h

/-- The unconditional clauses, on any returned diagram, with no hypothesis on the input. -/
theorem rigidSelector_unconditional (S : PotentialSpanData) (D : AmalgamationDiagramData)
    (hD : D ∈ rigidSelector S) :
    D.WellShapedFor S ∧ (rigidFamily (O := O)).PartialIsEmbedding D.leftToApex ∧
      (rigidFamily (O := O)).PartialWellFormed D.rightToApex := by
  obtain rfl := eq_rigidDiagram_of_mem hD
  exact ⟨⟨rfl, rfl, rfl⟩, rigidIdentityData_partialIsEmbedding _ 0,
    (rigidIdentityData_partialIsEmbedding _ 0).partialWellFormed⟩

/-- Conditional soundness, on an actual input span. -/
theorem rigidSelector_sound (S : PotentialSpanData) (D : AmalgamationDiagramData)
    (hD : D ∈ rigidSelector S) (hS : (rigidFamily (O := O)).PartialSpanActual S) :
    (rigidFamily (O := O)).PartialIsEmbedding D.rightToApex ∧
      (rigidFamily (O := O)).PartialCommutes S D := by
  obtain rfl := eq_rigidDiagram_of_mem hD
  refine ⟨rigidIdentityData_partialIsEmbedding _ 0, ?_⟩
  obtain ⟨hSd, ⟨fl, hfl⟩, ⟨fr, hfr⟩⟩ := hS
  refine (PartialAgeIn.partialCommutes_iff_of_realizers
    (d := S.left.domIdx) (m₁ := S.left.codIdx) (m₂ := S.right.codIdx) (apex := 0)
    (fl := fl) (fr := fr)
    (gl := rigidIdentityEmb S.left.codIdx 0) (gr := rigidIdentityEmb S.right.codIdx 0)
    ⟨rfl, rfl, hfl⟩ ⟨Eq.symm hSd, rfl, hfr⟩ ⟨rfl, rfl, rfl, fun _ ↦ rfl⟩
    ⟨rfl, rfl, rfl, fun _ ↦ rfl⟩).2 ?_
  refine DFunLike.ext _ _ fun x ↦ Subtype.ext ?_
  show ((rigidIdentityEmb S.left.codIdx 0) (fl x) : ℕ) = _
  rw [rigid_memberEmbedding_eq_identity (rigidIdentityEmb S.left.codIdx 0) (fl x),
    rigid_memberEmbedding_eq_identity fl x]
  show _ = ((rigidIdentityEmb S.right.codIdx 0) (fr x) : ℕ)
  rw [rigid_memberEmbedding_eq_identity (rigidIdentityEmb S.right.codIdx 0) (fr x),
    rigid_memberEmbedding_eq_identity fr x]

/-- **The fixture is a legitimate `PartialCAPIn` witness.** -/
theorem rigidFamily_partialCAPIn :
    PartialAgeIn.PartialCAPIn O (rigidFamily (O := O)) :=
  ⟨rigidSelector, rigidSelector_recursiveIn,
    fun S hS ↦ (rigidSelector_dom_iff_carrierValidSpan S).2 hS,
    rigidSelector_unconditional, rigidSelector_sound⟩

/-! ### The four-row matrix

All four inputs are spans with both legs `⟨0, 0, t⟩`, differing only in the range tuple `t`.
The rows exercise the constructed witness's clauses, not merely the predicates. -/

/-- The matrix's input spans. -/
def rigidSpan (t : Tuple ℕ) : PotentialSpanData := ⟨⟨0, 0, t⟩, ⟨0, 0, t⟩⟩

/-- **Row 1 — carrier-valid but wrong length.** The selector halts and the unconditional
clauses hold of its output, even though the input leg is not well-formed. -/
theorem test_row_wrongLength :
    (rigidFamily (O := O)).CarrierValidSpan (rigidSpan [0]) ∧
      (rigidSelector (rigidSpan [0])).Dom ∧
      (∀ D ∈ rigidSelector (rigidSpan [0]),
        D.WellShapedFor (rigidSpan [0]) ∧
          (rigidFamily (O := O)).PartialIsEmbedding D.leftToApex) ∧
      ¬(rigidFamily (O := O)).PartialWellFormed (rigidSpan [0]).left := by
  have hcv : (rigidFamily (O := O)).CarrierValidSpan (rigidSpan [0]) :=
    (rigidGuard_eq_true_iff_carrierValidSpan (O := O) _).1 rfl
  refine ⟨hcv, (rigidSelector_dom_iff_carrierValidSpan _).2 hcv,
    fun D hD ↦ ⟨(rigidSelector_unconditional (O := O) _ D hD).1,
      (rigidSelector_unconditional (O := O) _ D hD).2.1⟩, ?_⟩
  intro hwf
  have h : (2 : ℕ) = 1 := hwf.length
  omega

/-- **Row 2 — carrier-valid and well-formed, but not an embedding.** The selector still
halts; rigidity is what makes `[1,0]` fail. -/
theorem test_row_nonEmbedding :
    (rigidFamily (O := O)).CarrierValidSpan (rigidSpan [1, 0]) ∧
      (rigidFamily (O := O)).PartialWellFormed (rigidSpan [1, 0]).left ∧
      (rigidSelector (rigidSpan [1, 0])).Dom ∧
      ¬(rigidFamily (O := O)).PartialIsEmbedding (rigidSpan [1, 0]).left := by
  have hcv : (rigidFamily (O := O)).CarrierValidSpan (rigidSpan [1, 0]) :=
    (rigidGuard_eq_true_iff_carrierValidSpan (O := O) _).1 rfl
  refine ⟨hcv, ⟨hcv.1, rfl⟩, (rigidSelector_dom_iff_carrierValidSpan _).2 hcv, ?_⟩
  rintro ⟨f, hlen, hcoord⟩
  have hidx : 0 < ((rigidFamily (O := O)).gens (rigidSpan [1, 0]).left.domIdx).length := by
    show 0 < 2
    omega
  have h0 := hcoord ⟨0, hidx⟩
  rw [rigid_memberEmbedding_eq_identity f _] at h0
  have h1 : (0 : ℕ) = 1 := h0
  omega

/-- **Row 3 — off-carrier: the selector genuinely diverges.** Proved by reduction to the
selector's own `Part.none` branch, not from an absence of promise. -/
theorem test_row_offCarrier :
    rigidSelector (rigidSpan [2, 0]) = Part.none ∧
      ¬(rigidSelector (rigidSpan [2, 0])).Dom ∧
      ¬(rigidFamily (O := O)).CarrierValidSpan (rigidSpan [2, 0]) := by
  have hnone : rigidSelector (rigidSpan [2, 0]) = Part.none := by
    rw [rigidSelector_eq]
    rfl
  refine ⟨hnone, by rw [hnone]; simp, ?_⟩
  intro hcv
  have h2 : (2 : ℕ) ∈ (rigidFamily (O := O)).domainAt 0 := hcv.1 2 (by exact List.mem_cons_self)
  rw [rigidFamily_domainAt] at h2
  rcases h2 with h | h
  · have : (2 : ℕ) = 0 := h
    omega
  · have : (2 : ℕ) = 1 := h
    omega

/-- **Row 4 — actual input: full soundness.** The selected diagram's right map is realized
and the square commutes. -/
theorem test_row_actual :
    (rigidFamily (O := O)).PartialSpanActual (rigidSpan [0, 1]) ∧
      ∀ D ∈ rigidSelector (rigidSpan [0, 1]),
        (rigidFamily (O := O)).PartialIsEmbedding D.rightToApex ∧
          (rigidFamily (O := O)).PartialCommutes (rigidSpan [0, 1]) D := by
  have hact : (rigidFamily (O := O)).PartialSpanActual (rigidSpan [0, 1]) :=
    ⟨rfl, rigidIdentityData_partialIsEmbedding 0 0, rigidIdentityData_partialIsEmbedding 0 0⟩
  exact ⟨hact, fun D hD ↦ rigidSelector_sound (O := O) _ D hD hact⟩

end

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.rigid_memberEmbedding_eq_identity
#assert_standard_axioms FirstOrder.Language.rigidGuard_eq_true_iff_carrierValidSpan
#assert_standard_axioms FirstOrder.Language.rigidSelector_dom_iff_carrierValidSpan
#assert_standard_axioms FirstOrder.Language.rigidIdentityData_partialIsEmbedding
#assert_standard_axioms FirstOrder.Language.rigidSelector_recursiveIn
#assert_standard_axioms FirstOrder.Language.rigidFamily_partialCAPIn
#assert_standard_axioms FirstOrder.Language.test_row_wrongLength
#assert_standard_axioms FirstOrder.Language.test_row_nonEmbedding
#assert_standard_axioms FirstOrder.Language.test_row_offCarrier
#assert_standard_axioms FirstOrder.Language.test_row_actual
#assert_standard_axioms FirstOrder.Language.test_rigidFamily_carrier
#assert_standard_axioms FirstOrder.Language.test_rigidFamily_asymmetric
