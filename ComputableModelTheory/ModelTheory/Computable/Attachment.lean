/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialMemberEmbedding
import ComputableModelTheory.ModelTheory.Computable.PartialTermEvaluation

/-!
# Attachments and their transport along connecting data

A Definition 2.1 family records its members only as c.e. carriers of natural-number codes, and a
code in one member is not an identity shared with any other member. A construction that wants to
follow named points from member to member therefore stores, at each member, a finite
**attachment**: labels paired with **terms over that member's recorded generators**. A term can be
re-evaluated anywhere the generators are sent, which is what makes the image of a labelled point
under connecting data computable without deciding carrier membership.

This file separates three things that later arguments must not conflate.

* **Data and validity.** An `Attachment` is a proof-free list of `(label, term)` entries.
  `Attachment.Valid k` is the separate invariant: every term is *source-bounded* (its variables
  lie below `k`, the source member's generator count), and the labels are distinct. Validity is
  decidable.
* **Evaluation needs no actualness.** `attRep c t` evaluates `t` at member `c`'s own generators
  (the label's representative). `attImage F t` substitutes `F.rangeTuple` for the source
  generators and evaluates in `F.codIdx`; a width mismatch is rejected *before* any evaluation is
  attempted. On `PartialWellFormed` data — carrier-valid, correct width — and a source-bounded term
  the image halts (`attImage_dom`). Nothing requires `F` to be realized by an embedding.
* **Coherence needs actualness.** Only when `F` is realized by a member embedding `f` is the image
  of an attached term `f` applied to its representative (`attImage_eq_of_realizes`). This is the
  one-step coherence the staged construction maintains along links.

The audit pins the gap between the last two bullets: evaluation succeeds on well-formed data that no
embedding realizes, where the evaluated images visibly fail to cohere.

No CEP, diagram growth or priority action is coupled to attachments here.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

/-! ### Proof-free attachment data -/

/-- One attached entry: a label together with a term over the source member's generator
positions (variable `k` stands for the `k`-th recorded generator). -/
structure AttachmentEntry (L : Language) where
  /-- The label of the attached point. -/
  label : ℕ
  /-- The term naming the attached point over the source member's generators. -/
  term : L.Term ℕ

/-- A stored finite attachment: proof-free, a list of entries. -/
abbrev Attachment (L : Language) := List (AttachmentEntry L)

namespace Attachment

variable {L : Language}

/-- The labels an attachment mentions, in order. -/
def labels (a : Attachment L) : List ℕ :=
  a.map AttachmentEntry.label

/-- **The validity invariant at width `k`**: every attached term is source-bounded (its variables
lie below `k`), and the labels are distinct. Kept separate from the data, which carries no
proofs. -/
structure Valid (k : ℕ) (a : Attachment L) : Prop where
  varsBelow : ∀ e ∈ a, Term.VarsBelow k e.term
  nodup : a.labels.Nodup

theorem valid_iff {k : ℕ} {a : Attachment L} :
    a.Valid k ↔ (∀ e ∈ a, Term.VarsBelow k e.term) ∧ a.labels.Nodup :=
  ⟨fun h ↦ ⟨h.varsBelow, h.nodup⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Validity is decidable: the bounded-variable scan `varsBelowBool` decides source-boundedness. -/
instance (k : ℕ) (a : Attachment L) : Decidable (a.Valid k) :=
  decidable_of_iff ((a.all fun e ↦ Term.varsBelowBool k e.term) = true ∧ a.labels.Nodup) <| by
    rw [valid_iff, List.all_eq_true]
    exact and_congr_left' (forall₂_congr fun e _ ↦ Term.varsBelowBool_iff k e.term)

end Attachment

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace PartialAgeIn

variable (A : PartialAgeIn O L)

/-! ### Representatives and images -/

/-- The **representative** of a term at its source member `c`: evaluation at `c`'s recorded
generators. -/
noncomputable def attRep (c : ℕ) (t : L.Term ℕ) : Part ℕ :=
  A.partialRealize c (A.gens c) t

/-- The **image** of a term under connecting data `F`: substitute `F.rangeTuple` for the source
member's generators and evaluate in the target member. A width mismatch between the range tuple
and the source generators is **rejected before evaluation**: the result is then `Part.none`
without the evaluator being consulted. No actualness of `F` is assumed. -/
noncomputable def attImage (F : PotentialEmbeddingData) (t : L.Term ℕ) : Part ℕ :=
  if (A.gens F.domIdx).length = F.rangeTuple.length then
    A.partialRealize F.codIdx F.rangeTuple t
  else Part.none

variable {A}

theorem attImage_of_length_eq {F : PotentialEmbeddingData} (t : L.Term ℕ)
    (hlen : (A.gens F.domIdx).length = F.rangeTuple.length) :
    A.attImage F t = A.partialRealize F.codIdx F.rangeTuple t :=
  ite_eq_left hlen

/-- **Malformed widths are rejected up front.** -/
theorem attImage_of_length_ne {F : PotentialEmbeddingData} (t : L.Term ℕ)
    (hlen : (A.gens F.domIdx).length ≠ F.rangeTuple.length) :
    A.attImage F t = Part.none :=
  ite_eq_right hlen

/-- A source-bounded term restricted to the generator positions bounding it. -/
def restrictBelow {k : ℕ} (t : L.Term ℕ) (hv : Term.VarsBelow k t) : L.Term (Fin k) :=
  t.restrictVar fun x ↦ ⟨x.1, hv x.1 x.2⟩

variable (A) in
/-- The representative of a source-bounded term, as a point of the source member's carrier:
the restricted term realized at the recorded generators, read inside the member. -/
noncomputable def repView (c : ℕ) {t : L.Term ℕ} (hv : Term.VarsBelow (A.gens c).length t) :
    (A.memberAt c).domain :=
  (restrictBelow t hv).realize (A.gensView c)

/-- **The representative halts**, at the recorded generators, with the value of `repView`. -/
theorem attRep_eq_some {c : ℕ} {t : L.Term ℕ} (hv : Term.VarsBelow (A.gens c).length t) :
    A.attRep c t = Part.some (A.repView c hv : ℕ) := by
  rw [attRep, A.partialRealize_eq_realize_restrictVar (fun _ hx ↦ A.mem_domainAt_of_mem_gens hx)
    rfl t hv, repView, (A.memberAt c).realize_domain_val]
  rfl

theorem attRep_dom {c : ℕ} {t : L.Term ℕ} (hv : Term.VarsBelow (A.gens c).length t) :
    (A.attRep c t).Dom := by
  rw [attRep_eq_some hv]
  trivial

/-- **Evaluation on well-formed data halts**, with the ordinary realization at the range tuple.
No actualness hypothesis: `F` need not be realized by any embedding. -/
theorem attImage_eq_some {F : PotentialEmbeddingData} (hF : A.PartialWellFormed F)
    {t : L.Term ℕ} (hv : Term.VarsBelow (A.gens F.domIdx).length t) :
    A.attImage F t = Part.some
      (@Term.realize L ℕ (A.structureAt F.codIdx) ℕ (ComputableAgeIn.envFun F.rangeTuple) t) := by
  rw [attImage_of_length_eq t hF.length]
  exact A.partialRealize_eq_some hF.carrierValid (hF.length ▸ hv)

theorem attImage_dom {F : PotentialEmbeddingData} (hF : A.PartialWellFormed F)
    {t : L.Term ℕ} (hv : Term.VarsBelow (A.gens F.domIdx).length t) :
    (A.attImage F t).Dom := by
  rw [attImage_eq_some hF hv]
  trivial

/-- The image of a halting evaluation lies in the target member. -/
theorem attImage_mem_domainAt {F : PotentialEmbeddingData} (hF : A.CarrierValid F)
    {t : L.Term ℕ} {x : ℕ} (hx : x ∈ A.attImage F t) : x ∈ A.domainAt F.codIdx := by
  by_cases hlen : (A.gens F.domIdx).length = F.rangeTuple.length
  · rw [attImage_of_length_eq t hlen] at hx
    exact A.partialRealize_mem_domainAt hF
      (A.varsBelow_of_partialRealize_dom (Part.dom_iff_mem.2 ⟨_, hx⟩)) hx
  · rw [attImage_of_length_ne t hlen] at hx
    exact absurd hx (Part.notMem_none x)

/-- **A halting image certifies the width.** If an image evaluates, the range tuple has the source
generator count, and the term's variables lie below it. -/
theorem attImage_dom_imp {F : PotentialEmbeddingData} {t : L.Term ℕ}
    (h : (A.attImage F t).Dom) :
    (A.gens F.domIdx).length = F.rangeTuple.length ∧
      Term.VarsBelow F.rangeTuple.length t := by
  by_cases hlen : (A.gens F.domIdx).length = F.rangeTuple.length
  · rw [attImage_of_length_eq t hlen] at h
    exact ⟨hlen, A.varsBelow_of_partialRealize_dom h⟩
  · rw [attImage_of_length_ne t hlen] at h
    exact absurd h Part.not_none_dom

/-! ### Attachments under well-formed connecting data -/

namespace Attachment

/-- Validity of an attachment stored at member `c`: validity at `c`'s generator count. -/
abbrev ValidAt (A : PartialAgeIn O L) (c : ℕ) (a : FirstOrder.Language.Attachment L) : Prop :=
  a.Valid (A.gens c).length

end Attachment

/-- **Every entry of a valid attachment has a representative.** -/
theorem attRep_dom_of_valid {c : ℕ} {a : FirstOrder.Language.Attachment L}
    (ha : Attachment.ValidAt A c a) {e : AttachmentEntry L} (he : e ∈ a) :
    (A.attRep c e.term).Dom :=
  attRep_dom (ha.varsBelow e he)

/-- **Every entry of a valid attachment transports along well-formed data.** Evaluation needs the
width (validity and the length equation) and the carrier (carrier validity), and nothing more. -/
theorem attImage_dom_of_valid {F : PotentialEmbeddingData} (hF : A.PartialWellFormed F)
    {a : FirstOrder.Language.Attachment L} (ha : Attachment.ValidAt A F.domIdx a)
    {e : AttachmentEntry L} (he : e ∈ a) :
    (A.attImage F e.term).Dom :=
  attImage_dom hF (ha.varsBelow e he)

/-! ### Conditional coherence -/

/-- **Coherence, under actualness.** When `f` realizes `F`, the image of a source-bounded term
under `F` is `f` applied to the term's representative. Embeddings commute with term realization,
and `f` sends the recorded generators onto the range tuple. -/
theorem attImage_eq_of_realizes {F : PotentialEmbeddingData}
    {f : (A.memberAt F.domIdx).domain ↪[L] (A.memberAt F.codIdx).domain}
    (hf : A.PartialRealizes F f) {t : L.Term ℕ}
    (hv : Term.VarsBelow (A.gens F.domIdx).length t) :
    A.attImage F t =
      Part.some ((f (A.repView F.domIdx hv) : (A.memberAt F.codIdx).domain) : ℕ) := by
  have hvalid := hf.partialWellFormed.carrierValid
  obtain ⟨hlen, hcoord⟩ := hf
  rw [attImage_of_length_eq t hlen,
    A.partialRealize_eq_realize_restrictVar hvalid hlen.symm t hv,
    repView, ← HomClass.realize_term (L := L) f, (A.memberAt F.codIdx).realize_domain_val]
  congr 1
  refine congrArg (fun v ↦ @Term.realize L ℕ (A.structureAt F.codIdx) _ v (restrictBelow t hv))
    (funext fun k ↦ ?_)
  rw [Function.comp_apply, hcoord k, Tuple.view_eq_get]

/-- Coherence, read as membership: under actualness, the representative's image under `f` is the
evaluated image. -/
theorem mem_attImage_of_realizes {F : PotentialEmbeddingData}
    {f : (A.memberAt F.domIdx).domain ↪[L] (A.memberAt F.codIdx).domain}
    (hf : A.PartialRealizes F f) {t : L.Term ℕ}
    (hv : Term.VarsBelow (A.gens F.domIdx).length t) :
    ((f (A.repView F.domIdx hv) : (A.memberAt F.codIdx).domain) : ℕ) ∈ A.attImage F t := by
  rw [attImage_eq_of_realizes hf hv]
  exact Part.mem_some _

/-- **Coherence for a whole valid attachment**, under actualness: every attached label's image is
`f` of its representative. This is the one-step form of attachment coherence along a link. -/
theorem attImage_coherent {F : PotentialEmbeddingData}
    {f : (A.memberAt F.domIdx).domain ↪[L] (A.memberAt F.codIdx).domain}
    (hf : A.PartialRealizes F f) {a : FirstOrder.Language.Attachment L}
    (ha : Attachment.ValidAt A F.domIdx a) {e : AttachmentEntry L} (he : e ∈ a) :
    A.attImage F e.term =
      Part.some ((f (A.repView F.domIdx (ha.varsBelow e he)) :
        (A.memberAt F.codIdx).domain) : ℕ) :=
  attImage_eq_of_realizes hf _

/-! ### Uniform computability -/

variable (A)

/-- **Transport is partial recursive** uniformly in the connecting data and the term: the width
check is a computable guard, followed by a single call of the uniform evaluator. -/
theorem attImage_recursiveIn :
    RecursiveIn O fun p : PotentialEmbeddingData × L.Term ℕ ↦ A.attImage p.1 p.2 := by
  have hguard : ComputableIn O fun p : PotentialEmbeddingData × L.Term ℕ ↦
      if (A.gens p.1.domIdx).length = p.1.rangeTuple.length then
        some ((p.1.codIdx, p.1.rangeTuple), p.2)
      else none :=
    ComputableIn.ite
      (((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
        ((Primrec.list_length.to_comp.computableIn).comp
          (A.gens_computableIn.comp
            ((PotentialEmbeddingData.domIdx_computable).comp ComputableIn.fst)))
        ((Primrec.list_length.to_comp.computableIn).comp
          ((PotentialEmbeddingData.rangeTuple_computable).comp ComputableIn.fst)))
      (ComputableIn.option_some.comp
        ((((PotentialEmbeddingData.codIdx_computable).comp ComputableIn.fst).pair
          ((PotentialEmbeddingData.rangeTuple_computable).comp ComputableIn.fst)).pair
          ComputableIn.snd))
      (ComputableIn.const none)
  refine (RecursiveIn.bind (ComputableIn.ofOption hguard)
    ((A.partialRealize_recursiveIn.comp ComputableIn.snd).to₂)).of_eq fun p ↦ ?_
  by_cases h : (A.gens p.1.domIdx).length = p.1.rangeTuple.length
  · simp [attImage, h]
  · simp [attImage, h]

end PartialAgeIn

end FirstOrder.Language
