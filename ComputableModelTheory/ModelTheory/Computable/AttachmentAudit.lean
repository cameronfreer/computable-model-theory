/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.Attachment
import ComputableModelTheory.ModelTheory.Computable.ListAgeExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: attachments evaluate without actualness, and cohere only with it

The fixture is `listAge` in the empty language. Its member `segIdx n` is the pure set
`{0, …, n}`, with generators `[0, …, n]`. Every entry below is a term over generator positions.

* **Well-formed nonactual data evaluates** (`nonactual`). `F = (segIdx 1, segIdx 1, [0, 0])`
  is carrier-valid and has the right width, so the attachment `[(10, x₀), (11, x₁)]` transports
  along it: both images halt, and both are `0`. But the representatives are `0` and `1`, and
  **no** embedding realizes `F`, since it would have to identify two generators. Evaluation
  succeeds where coherence has nothing to be coherent with.
* **Coherence under actualness** (`actual`). `G = (segIdx 0, segIdx 1, [1])` is realized by the
  embedding `0 ↦ 1`. Only there does the general theorem apply: the image of `x₀` is `1`, which
  is that embedding applied to the representative `0`.
* **Malformed widths are rejected** (`malformed`). The empty range tuple against variable `0` is
  carrier-valid, vacuously, but not well-formed. The guarded image is `Part.none` before any
  evaluation. Without the guard the evaluator would not halt either, since halting certifies the
  width.
* **Validity is decidable, and it fails on both counts.** It fails for a repeated label and for
  a term reaching past the generator count.
-/

open Encodable FirstOrder Language

namespace AttachmentAudit

open listAge

variable (O : Set (ℕ →. ℕ))

/-- The attachment used throughout: label `10` at generator `0`, label `11` at generator `1`. -/
def att : Attachment Language.empty :=
  [⟨10, Term.var 0⟩, ⟨11, Term.var 1⟩]

theorem gens_segIdx (n : ℕ) : (listAge O).gens (segIdx n) = List.range (n + 1) :=
  listOf_segIdx n

/-- Validity is decided by evaluation, and `att` is valid at width `2`. -/
theorem test_att_valid : att.Valid 2 := by decide

/-- A repeated label is invalid. -/
theorem test_dup_label_invalid :
    ¬ Attachment.Valid 2 ([⟨10, Term.var 0⟩, ⟨10, Term.var 1⟩] : Attachment Language.empty) := by
  decide

/-- A term reaching past the generator count is invalid. -/
theorem test_unbounded_term_invalid :
    ¬ Attachment.Valid 2 ([⟨10, Term.var 2⟩] : Attachment Language.empty) := by decide

theorem att_validAt : PartialAgeIn.Attachment.ValidAt (listAge O) (segIdx 1) att := by
  rw [PartialAgeIn.Attachment.ValidAt, gens_segIdx]
  exact test_att_valid

/-- The representatives at `segIdx 1` are the generators themselves: `0` and `1`. -/
theorem test_att_reps :
    (listAge O).attRep (segIdx 1) (Term.var 0) = Part.some 0 ∧
      (listAge O).attRep (segIdx 1) (Term.var 1) = Part.some 1 := by
  have henv : ∀ x ∈ (listAge O).gens (segIdx 1), x ∈ (listAge O).domainAt (segIdx 1) :=
    fun _ hx ↦ (listAge O).mem_domainAt_of_mem_gens hx
  have hlen : ((listAge O).gens (segIdx 1)).length = 2 := by rw [gens_segIdx]; rfl
  refine ⟨?_, ?_⟩ <;>
  · rw [PartialAgeIn.attRep, (listAge O).partialRealize_eq_some henv
      (Term.varsBelow_var_iff.2 (by omega)), Term.realize_var, ComputableAgeIn.envFun, gens_segIdx]
    rfl

/-! ### Well-formed, nonactual -/

/-- Both generators of `{0, 1}` sent to `0`. -/
def nonactual : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple (segIdx 1, segIdx 1, [0, 0])

theorem nonactual_wellFormed : (listAge O).PartialWellFormed nonactual := by
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · have hx0 : x = 0 := by simpa [nonactual] using hx
    exact (mem_domainAt_segIdx O).2 (by omega)
  · change ((listAge O).gens (segIdx 1)).length = 2
    rw [gens_segIdx]
    rfl

/-- **No embedding realizes `nonactual`**: it would send the distinct generators `0` and `1` to
the same point. -/
theorem test_nonactual_not_embedding : ¬ (listAge O).PartialIsEmbedding nonactual := by
  rintro ⟨f, hf⟩
  let x0 : ((listAge O).memberAt (segIdx 1)).domain := ⟨0, (mem_domainAt_segIdx O).2 (by omega)⟩
  let x1 : ((listAge O).memberAt (segIdx 1)).domain := ⟨1, (mem_domainAt_segIdx O).2 (by omega)⟩
  have h0 := PartialAgeIn.getElem?_of_realizes hf (k := 0) (x := x0)
    (by change (listOf (segIdx 1))[0]? = some (0 : ℕ); rw [listOf_segIdx]; rfl)
  have h1 := PartialAgeIn.getElem?_of_realizes hf (k := 1) (x := x1)
    (by change (listOf (segIdx 1))[1]? = some (1 : ℕ); rw [listOf_segIdx]; rfl)
  have hx : x0 = x1 := f.injective (Subtype.ext (by
    have e0 := (Option.some.inj h0).symm
    have e1 := (Option.some.inj h1).symm
    exact e0.trans e1.symm))
  exact absurd (congrArg Subtype.val hx) (by simp [x0, x1])

/-- **Evaluation succeeds on the nonactual data**, entry by entry, with no actualness hypothesis. -/
theorem test_nonactual_evaluates :
    ∀ e ∈ att, ((listAge O).attImage nonactual e.term).Dom :=
  fun _ he ↦ PartialAgeIn.attImage_dom_of_valid (nonactual_wellFormed O) (att_validAt O) he

/-- **The evaluated images collide** — both labels go to `0` — while the representatives are `0`
and `1`. The images are not those of any embedding, as `test_nonactual_not_embedding` shows. -/
theorem test_nonactual_images :
    (listAge O).attImage nonactual (Term.var 0) = Part.some 0 ∧
      (listAge O).attImage nonactual (Term.var 1) = Part.some 0 := by
  have hlen : ((listAge O).gens nonactual.domIdx).length = 2 := by
    rw [show nonactual.domIdx = segIdx 1 from rfl, gens_segIdx]; rfl
  refine ⟨?_, ?_⟩ <;>
  · rw [PartialAgeIn.attImage_eq_some (nonactual_wellFormed O)
      (Term.varsBelow_var_iff.2 (by omega))]
    rfl

/-! ### Actual -/

/-- `{0}` into `{0, 1}`, sending the generator `0` to `1`. -/
def actual : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple (segIdx 0, segIdx 1, [1])

/-- The realizer of `actual`: the constant map at `1` on the one-point member. -/
noncomputable def toOne :
    ((listAge O).memberAt (segIdx 0)).domain ↪[Language.empty]
      ((listAge O).memberAt (segIdx 1)).domain :=
  emptyEmbedding ⟨fun _ ↦ ⟨1, (mem_domainAt_segIdx O).2 (by omega)⟩, fun x y _ ↦ by
    have hx := (mem_domainAt_segIdx O).1 x.2
    have hy := (mem_domainAt_segIdx O).1 y.2
    exact Subtype.ext (by omega)⟩

theorem toOne_realizes : (listAge O).PartialRealizes actual (toOne O) := by
  refine PartialAgeIn.realizes_of_getElem? (by rw [gens_segIdx]; rfl) fun k x hk ↦ ?_
  rw [gens_segIdx] at hk
  rcases k with _ | k
  · rfl
  · simp at hk

/-- The representative of `x₀` at `{0}`, as a point of the carrier. -/
theorem actual_repView (hv) :
    (((listAge O).repView (segIdx 0) (t := Term.var 0) hv :
      ((listAge O).memberAt (segIdx 0)).domain) : ℕ) = 0 := by
  have h := (mem_domainAt_segIdx O).1 ((listAge O).repView (segIdx 0) (t := Term.var 0) hv).2
  omega

/-- **Coherence, under actualness**: the image of `x₀` is `toOne` applied to its representative,
and is `1`. -/
theorem test_actual_coherent :
    ∃ hv, (listAge O).attImage actual (Term.var 0) =
        Part.some ((toOne O ((listAge O).repView (segIdx 0) (t := Term.var 0) hv) :
          ((listAge O).memberAt (segIdx 1)).domain) : ℕ) ∧
      (listAge O).attImage actual (Term.var 0) = Part.some 1 := by
  have hv : Term.VarsBelow ((listAge O).gens actual.domIdx).length
      (Term.var 0 : Language.empty.Term ℕ) := by
    rw [show actual.domIdx = segIdx 0 from rfl, gens_segIdx]
    exact Term.varsBelow_var_iff.2 (by simp)
  exact ⟨hv, PartialAgeIn.attImage_eq_of_realizes (toOne_realizes O) hv,
    (PartialAgeIn.attImage_eq_of_realizes (toOne_realizes O) hv).trans rfl⟩

/-! ### Malformed width -/

/-- The empty range tuple, against a member with one generator. -/
def malformed : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple (segIdx 0, segIdx 1, [])

/-- Carrier validity holds vacuously, so it alone does not license evaluation. -/
theorem test_malformed_carrierValid : (listAge O).CarrierValid malformed :=
  fun _ hx ↦ absurd hx List.not_mem_nil

theorem test_malformed_not_wellFormed : ¬ (listAge O).PartialWellFormed malformed := by
  rintro ⟨-, hlen⟩
  rw [show malformed.domIdx = segIdx 0 from rfl, gens_segIdx] at hlen
  exact absurd hlen (by decide)

/-- **Rejected up front**: the guarded image is `Part.none`. -/
theorem test_malformed_rejected :
    (listAge O).attImage malformed (Term.var 0) = Part.none :=
  PartialAgeIn.attImage_of_length_ne _ fun h ↦ by
    rw [show malformed.domIdx = segIdx 0 from rfl, gens_segIdx] at h
    exact absurd h (by decide)

/-- The raw evaluator does not halt there either: halting would certify `0 < 0`. -/
theorem test_malformed_raw_diverges :
    ¬ ((listAge O).partialRealize (segIdx 1) [] (Term.var 0)).Dom := fun h ↦
  absurd (Term.varsBelow_var_iff.1 ((listAge O).varsBelow_of_partialRealize_dom h))
    (Nat.lt_irrefl 0)

end AttachmentAudit

#assert_standard_axioms AttachmentAudit.test_att_valid
#assert_standard_axioms AttachmentAudit.test_dup_label_invalid
#assert_standard_axioms AttachmentAudit.test_unbounded_term_invalid
#assert_standard_axioms AttachmentAudit.test_att_reps
#assert_standard_axioms AttachmentAudit.test_nonactual_not_embedding
#assert_standard_axioms AttachmentAudit.test_nonactual_evaluates
#assert_standard_axioms AttachmentAudit.test_nonactual_images
#assert_standard_axioms AttachmentAudit.actual_repView
#assert_standard_axioms AttachmentAudit.test_actual_coherent
#assert_standard_axioms AttachmentAudit.test_malformed_carrierValid
#assert_standard_axioms AttachmentAudit.test_malformed_not_wellFormed
#assert_standard_axioms AttachmentAudit.test_malformed_rejected
#assert_standard_axioms AttachmentAudit.test_malformed_raw_diverges

#assert_module_standard_axioms ComputableModelTheory.ModelTheory.Computable.Attachment
