/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialTupleReindex
import ComputableModelTheory.ModelTheory.Computable.PartialMemberEmbedding

/-!
# Applying potential embedding data as a partial map

Potential embedding data is pure code: a pair of member indices and a range tuple. When the data
is *actual* it names a unique member embedding, and this file evaluates that embedding partially,
without ever choosing a realizer.

The route is the obvious one. To send `x`, find a term over the source member's recorded
generators whose value is `x`, then realize the same term over the range tuple. Both halves are
already available: `Term.boundedDecode` supplies bounded terms with their `VarsBelow` certificate,
and `partialRealize` evaluates a term against an on-domain environment.

**The search tests a total predicate.** `gensTermValue?` is `Option`-valued and *total*:
undecodable codes give `none`, and a decoded bounded term always evaluates, because the recorded
generators are on-domain and bounded decoding supplies the variable bound. So the `rfind` ranges
over a total Boolean test; only the search itself is partial, halting exactly when `x` lies in the
generated carrier.

**No exact-domain theorem for the public operation, deliberately.** On malformed or nonactual data
`applyPotentialPart` may halt accidentally, so a characterization of its domain would be false or
misleading. The internal search has one; the operation does not, and nothing at Level 1 totalizes
it.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (A : PartialAgeIn O L)

/-! ### The total generator-value enumerator -/

/-- The value of a term over member `i`'s recorded generators. Named because it is the *source*
side of every transport statement below, and repeating the explicit structure instance obscures
which of the two members is meant. -/
noncomputable def gensRealize (i : ℕ) (t : L.Term ℕ) : ℕ :=
  @Term.realize L ℕ (A.structureAt i) ℕ (ComputableAgeIn.envFun (A.gens i)) t

/-- The value of the `m`-th bounded term over member `i`'s recorded generators, if `m` decodes to
one. Total: the environment is on-domain and the decoded term is variable-bounded, so evaluation
always succeeds. -/
noncomputable def gensTermValue? (i m : ℕ) : Option ℕ :=
  (Term.boundedDecode (L := L) (A.gens i).length m).map (A.gensRealize i)

variable {A}

/-- The recorded generators are on-domain — the hypothesis every correctness statement of the
partial machine needs. -/
theorem gens_forall_mem_domainAt (i : ℕ) : ∀ x ∈ A.gens i, x ∈ A.domainAt i := by
  intro x hx
  obtain ⟨k, hk⟩ := List.mem_iff_get.1 hx
  exact hk ▸ A.gens_mem_domainAt k

/-- A bounded term's value over the recorded generators lies in the member's carrier. Stated
against `(A.memberAt i).domain` rather than the definitionally equal `A.domainAt i`: the subtype
constructor `⟨_, _⟩` used below elaborates against the former, and the two are not
interchangeable in that position. -/
theorem gensRealize_mem_domainAt {i : ℕ} {t : L.Term ℕ}
    (ht : Term.VarsBelow (A.gens i).length t) :
    A.gensRealize i t ∈ (A.memberAt i).domain :=
  realize_mem_domainAt (gens_forall_mem_domainAt i) ht

theorem gensTermValue?_eq_some_iff {i m x : ℕ} :
    A.gensTermValue? i m = Option.some x ↔
      ∃ t : L.Term ℕ,
        Term.boundedDecode (L := L) (A.gens i).length m = Option.some t ∧
          A.gensRealize i t = x := by
  rw [gensTermValue?, Option.map_eq_some_iff]

variable (A)

/-- The enumerator is computable — the partial machine is what actually computes it, exactly as
for `genEnum?`. -/
theorem gensTermValue?_computableIn :
    ComputableIn O fun p : ℕ × ℕ ↦ A.gensTermValue? p.1 p.2 := by
  have henv : ComputableIn O fun p : ℕ × ℕ ↦ A.gens p.1 :=
    A.gens_computableIn.comp ComputableIn.fst
  have hdec : ComputableIn O fun p : ℕ × ℕ ↦
      Term.boundedDecode (L := L) (A.gens p.1).length p.2 :=
    (Term.primrec₂_boundedDecode (L := L)).to_comp.computableIn₂.comp
      ((Computable.list_length.computableIn).comp henv) ComputableIn.snd
  have hcall : RecursiveIn O fun q : (ℕ × ℕ) × L.Term ℕ ↦
      A.partialRealize q.1.1 (A.gens q.1.1) q.2 :=
    RecursiveIn.comp (O := O) (α := (ℕ × ℕ) × L.Term ℕ)
      (β := (ℕ × Tuple ℕ) × L.Term ℕ) (σ := ℕ)
      (f := fun r : (ℕ × Tuple ℕ) × L.Term ℕ ↦ A.partialRealize r.1.1 r.1.2 r.2)
      (g := fun q : (ℕ × ℕ) × L.Term ℕ ↦ ((q.1.1, A.gens q.1.1), q.2))
      A.partialRealize_recursiveIn
      (ComputableIn.pair (O := O) (α := (ℕ × ℕ) × L.Term ℕ)
        (β := ℕ × Tuple ℕ) (γ := L.Term ℕ)
        (f := fun q ↦ (q.1.1, A.gens q.1.1)) (g := fun q ↦ q.2)
        (ComputableIn.pair (O := O) (α := (ℕ × ℕ) × L.Term ℕ) (β := ℕ) (γ := Tuple ℕ)
          (f := fun q ↦ q.1.1) (g := fun q ↦ A.gens q.1.1)
          ((Primrec.fst.comp Primrec.fst).to_comp.computableIn)
          (henv.comp (ComputableIn.fst (O := O) (α := ℕ × ℕ) (β := L.Term ℕ))))
        (ComputableIn.snd (O := O) (α := ℕ × ℕ) (β := L.Term ℕ)))
  have hpart : RecursiveIn O fun p : ℕ × ℕ ↦
      Option.casesOn (motive := fun _ ↦ Part (Option ℕ))
        (Term.boundedDecode (L := L) (A.gens p.1).length p.2)
        (Part.some Option.none)
        fun t ↦ (A.partialRealize p.1 (A.gens p.1) t).map Option.some :=
    RecursiveIn.option_casesOn_right (O := O) (α := ℕ × ℕ) (β := L.Term ℕ)
      (σ := Option ℕ)
      (o := fun p ↦ Term.boundedDecode (L := L) (A.gens p.1).length p.2)
      (f := fun _ ↦ Option.none)
      (g := fun p t ↦ (A.partialRealize p.1 (A.gens p.1) t).map Option.some)
      hdec (ComputableIn.const Option.none)
      ((RecursiveIn.map (O := O) (α := (ℕ × ℕ) × L.Term ℕ) (β := ℕ) (σ := Option ℕ)
        (f := fun q ↦ A.partialRealize q.1.1 (A.gens q.1.1) q.2)
        (g := fun _ (v : ℕ) ↦ Option.some v)
        hcall (ComputableIn.option_some.comp ComputableIn.snd).to₂).to₂)
  refine hpart.of_eq fun p ↦ ?_
  show _ = Part.some (A.gensTermValue? p.1 p.2)
  rw [gensTermValue?]
  rcases h : Term.boundedDecode (L := L) (A.gens p.1).length p.2 with - | t
  · rfl
  · show (A.partialRealize p.1 (A.gens p.1) t).map Option.some = _
    rw [partialRealize_eq_some (gens_forall_mem_domainAt p.1)
      (Term.boundedDecode_eq_some_iff.1 h).2]
    rfl

/-! ### The search, and the partial application

The search is `rfind` over a **total** Boolean test, so no partial-search obstruction arises.
Only the search itself is partial, halting exactly when `x` is a value of some bounded term over
the recorded generators — that is, exactly when `x` lies in the generated carrier. -/

variable {A}

/-- The least code of a bounded term over member `i`'s generators whose value is `x`. -/
noncomputable def gensTermCode (A : PartialAgeIn O L) (i x : ℕ) : Part ℕ :=
  Nat.rfind fun m ↦ Part.some (decide (A.gensTermValue? i m = Option.some x))

variable (A)

/-- The repacking the search's value lookup needs, named with its exact type. -/
private def gensTermTestInput (q : (ℕ × ℕ) × ℕ) : ℕ × ℕ := (q.1.1, q.2)

private theorem gensTermTestInput_computableIn :
    ComputableIn O gensTermTestInput :=
  ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd).of_eq fun _ ↦ rfl

private theorem gensTermValue_at_computableIn :
    ComputableIn O fun q : (ℕ × ℕ) × ℕ ↦ A.gensTermValue? q.1.1 q.2 := by
  have hbase : ComputableIn O fun p : ℕ × ℕ ↦ A.gensTermValue? p.1 p.2 :=
    A.gensTermValue?_computableIn
  have hcomposed : ComputableIn O fun q : (ℕ × ℕ) × ℕ ↦
      A.gensTermValue? (gensTermTestInput q).1 (gensTermTestInput q).2 :=
    ComputableIn.comp (α := (ℕ × ℕ) × ℕ) (β := ℕ × ℕ) (σ := Option ℕ)
      (f := fun p : ℕ × ℕ ↦ A.gensTermValue? p.1 p.2) (g := gensTermTestInput)
      hbase gensTermTestInput_computableIn
  exact hcomposed.of_eq fun _ ↦ rfl

/-- The search's Boolean test, as its own declaration. Extracted because fusing it into
`gensTermCode_recursiveIn` stalls at `whnf` — the established remedy for a composition whose
input is a projection repacking. Equality of `Option ℕ` goes through encodings, never through
`Primrec.eq` at `Option ℕ`. -/
theorem gensTermTest_computableIn :
    ComputableIn O fun q : (ℕ × ℕ) × ℕ ↦
      decide (Encodable.encode (A.gensTermValue? q.1.1 q.2) =
        Encodable.encode (Option.some q.1.2 : Option ℕ)) := by
  have hval : ComputableIn O fun q : (ℕ × ℕ) × ℕ ↦ A.gensTermValue? q.1.1 q.2 :=
    A.gensTermValue_at_computableIn
  have htgt : ComputableIn O fun q : (ℕ × ℕ) × ℕ ↦ (Option.some q.1.2 : Option ℕ) :=
    ComputableIn.option_some.comp (ComputableIn.snd.comp ComputableIn.fst)
  exact ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
    (ComputableIn.encode.comp hval) (ComputableIn.encode.comp htgt)

theorem gensTermCode_recursiveIn :
    RecursiveIn O fun p : ℕ × ℕ ↦ A.gensTermCode p.1 p.2 := by
  have h : ComputableIn₂ O fun (p : ℕ × ℕ) (m : ℕ) ↦
      decide (A.gensTermValue? p.1 m = Option.some p.2) :=
    ComputableIn.of_eq (A.gensTermTest_computableIn).to₂ fun q ↦
      Bool.eq_iff_iff.2 (by
        rw [decide_eq_true_iff, decide_eq_true_iff]
        exact Encodable.encode_inj)
  exact RecursiveIn.rfind_total h

variable {A}

/-! #### Search semantics

The generator search's behaviour, exposed so that later proofs consume named facts instead of
reopening `Nat.rfind`. -/

/-- The generator enumerator agrees with `genEnum?` on any step list presenting the recorded
generators — which lets the closure characterization be inherited rather than reproved. -/
theorem gensTermValue?_eq_genEnum? {i : ℕ} {steps : List ℕ}
    (h : A.tupleAtSteps i steps = A.gens i) (m : ℕ) :
    A.gensTermValue? i m = A.genEnum? i steps m := by
  rw [gensTermValue?, genEnum?, h]
  rfl

/-- **The search succeeds exactly on the member's carrier.** -/
theorem exists_gensTermValue?_eq_some_iff {i x : ℕ} :
    (∃ m, A.gensTermValue? i m = Option.some x) ↔ x ∈ A.domainAt i := by
  obtain ⟨steps, hsteps⟩ :=
    A.exists_steps_of_forall_mem_domainAt (gens_forall_mem_domainAt i)
  have hval : ∀ m, A.gensTermValue? i m = A.genEnum? i steps m :=
    gensTermValue?_eq_genEnum? hsteps
  have hiff : (∃ m, A.gensTermValue? i m = Option.some x) ↔
      ∃ m, A.genEnum? i steps m = Option.some x :=
    exists_congr fun m ↦ by rw [hval m]
  rw [hiff, exists_genEnum?_eq_some_iff, hsteps, A.mem_domainAt_iff_term]
  exact (@mem_closure_range_iff_exists_term L ℕ (A.structureAt i) _ (A.gens i).view x).trans
    (exists_congr fun _ ↦ eq_comm)

/-- **The code search halts exactly on the carrier.** -/
theorem gensTermCode_dom_iff {i x : ℕ} :
    (A.gensTermCode i x).Dom ↔ x ∈ A.domainAt i := by
  have h := Nat.rfind_some_dom_iff
    (f := fun (y : ℕ) k ↦ decide (A.gensTermValue? i k = Option.some y)) (a := x)
  rw [gensTermCode]
  refine h.trans (Iff.trans ?_ exists_gensTermValue?_eq_some_iff)
  exact ⟨fun ⟨n, hn⟩ ↦ ⟨n, of_decide_eq_true hn⟩, fun ⟨n, hn⟩ ↦ ⟨n, decide_eq_true hn⟩⟩

/-- **A returned code really names a term with the queried value** — the selected term is
exposed without reopening `rfind`. -/
theorem gensTermValue?_of_mem_gensTermCode {i x m : ℕ} (h : m ∈ A.gensTermCode i x) :
    A.gensTermValue? i m = Option.some x := by
  rw [gensTermCode, Nat.mem_rfind] at h
  exact of_decide_eq_true (Part.mem_some_iff.1 h.1).symm

variable (A)

/-- **Apply potential embedding data to a value.** Find a bounded term over the source member's
recorded generators whose value is `x`, then realize that same term over the range tuple.

No exact-domain theorem: on malformed or nonactual data this may halt accidentally. -/
noncomputable def applyPotentialPart (F : PotentialEmbeddingData) (x : ℕ) : Part ℕ :=
  (A.gensTermCode F.domIdx x).bind fun m ↦
    ((Term.boundedDecode (L := L) (A.gens F.domIdx).length m : Option (L.Term ℕ)) :
        Part (L.Term ℕ)).bind fun t ↦
      A.partialRealize F.codIdx F.rangeTuple t

/-! #### Computability of the application

The `partialRealize` call's input is a projection repacking, which stalls `comp` inside the
enclosing declaration. Extracted and fully pinned, as elsewhere. No encoded-result crossing is
needed: the result is `Part ℕ`, not an `ofEquiv`-encoded structure. -/

private def applyPotentialCodeInput (p : PotentialEmbeddingData × ℕ) : ℕ × ℕ :=
  (p.1.domIdx, p.2)

private theorem applyPotentialCodeInput_computableIn :
    ComputableIn O applyPotentialCodeInput :=
  ((PotentialEmbeddingData.domIdx_computable.comp ComputableIn.fst).pair
    ComputableIn.snd).of_eq fun _ ↦ rfl

private theorem applyPotentialCode_recursiveIn :
    RecursiveIn O fun p : PotentialEmbeddingData × ℕ ↦ A.gensTermCode p.1.domIdx p.2 := by
  have h := RecursiveIn.comp (O := O) (α := PotentialEmbeddingData × ℕ) (β := ℕ × ℕ) (σ := ℕ)
    (f := fun q : ℕ × ℕ ↦ A.gensTermCode q.1 q.2) (g := applyPotentialCodeInput)
    A.gensTermCode_recursiveIn applyPotentialCodeInput_computableIn
  exact h.of_eq fun _ ↦ rfl

private def applyPotentialRealizeInput
    (q : ((PotentialEmbeddingData × ℕ) × ℕ) × L.Term ℕ) : (ℕ × Tuple ℕ) × L.Term ℕ :=
  ((q.1.1.1.codIdx, q.1.1.1.rangeTuple), q.2)

private theorem applyPotentialRealizeInput_computableIn :
    ComputableIn O (applyPotentialRealizeInput (L := L)) :=
  ((((PotentialEmbeddingData.codIdx_computable.comp
        (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst))).pair
      (PotentialEmbeddingData.rangeTuple_computable.comp
        (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst)))).pair
    ComputableIn.snd)).of_eq fun _ ↦ rfl

private theorem applyPotentialRealize_recursiveIn :
    RecursiveIn O fun z : ((PotentialEmbeddingData × ℕ) × ℕ) × L.Term ℕ ↦
      A.partialRealize z.1.1.1.codIdx z.1.1.1.rangeTuple z.2 := by
  have h := RecursiveIn.comp
    (O := O) (α := ((PotentialEmbeddingData × ℕ) × ℕ) × L.Term ℕ)
    (β := (ℕ × Tuple ℕ) × L.Term ℕ) (σ := ℕ)
    (f := fun r : (ℕ × Tuple ℕ) × L.Term ℕ ↦ A.partialRealize r.1.1 r.1.2 r.2)
    (g := applyPotentialRealizeInput (L := L))
    A.partialRealize_recursiveIn applyPotentialRealizeInput_computableIn
  exact h.of_eq fun _ ↦ rfl

/-- **The application is partial recursive in the base oracle.** No `O ⊆ E` appears: the
operation depends only on `A`. The inclusion enters later, when this is lifted to a map oracle
and combined with a cover's traversals. -/
theorem applyPotentialPart_recursiveIn :
    RecursiveIn O fun p : PotentialEmbeddingData × ℕ ↦ A.applyPotentialPart p.1 p.2 := by
  have hcode := A.applyPotentialCode_recursiveIn
  have hdec : ComputableIn O fun q : (PotentialEmbeddingData × ℕ) × ℕ ↦
      Term.boundedDecode (L := L) (A.gens q.1.1.domIdx).length q.2 :=
    (Term.primrec₂_boundedDecode (L := L)).to_comp.computableIn₂.comp
      ((Computable.list_length.computableIn).comp
        (A.gens_computableIn.comp
          (PotentialEmbeddingData.domIdx_computable.comp
            (ComputableIn.fst.comp ComputableIn.fst))))
      ComputableIn.snd
  have hinner : RecursiveIn₂ O fun (p : PotentialEmbeddingData × ℕ) (m : ℕ) ↦
      ((Term.boundedDecode (L := L) (A.gens p.1.domIdx).length m : Option (L.Term ℕ)) :
          Part (L.Term ℕ)).bind fun t ↦ A.partialRealize p.1.codIdx p.1.rangeTuple t :=
    (RecursiveIn.bind hdec.ofOption (A.applyPotentialRealize_recursiveIn).to₂).to₂
  exact RecursiveIn.bind hcode hinner

/-! ### Correctness against a realizer

Two named layers, deliberately kept apart from the `Nat.rfind` layer above.
`partialRealize_rangeTuple_eq_some` is pure term-homomorphism reasoning: it says nothing about the
search, only that realizing a source-bounded term against the range tuple *is* applying the
realizer. `applyPotentialPart_mem_realizer` then does nothing but thread the search's output into
it.

The realizer is an **explicit** argument throughout. By `PartialRealizes.unique` there is at most
one, so an existential would lose no information — but it would force every consumer to reopen the
choice, and the conjugated pipeline needs to name the map it is transporting. -/

variable {A}

/-- **The target half applies the realizer.** Realizing a term bounded by the source member's
recorded generators against `F`'s range tuple halts, with the realizer's value at the source
realization.

Both sides restrict `t` to the *same* fixed-width term — the `VarsBelow` certificate `ht` is
shared, and only the length equation differs (`rfl` on the source side, `hf.length` on the target
side). That is what makes the two realizations comparable at all. -/
theorem partialRealize_rangeTuple_eq_some {F : PotentialEmbeddingData}
    {f : (A.memberAt F.domIdx).domain ↪[L] (A.memberAt F.codIdx).domain}
    (hf : A.PartialRealizes F f) {t : L.Term ℕ}
    (ht : Term.VarsBelow (A.gens F.domIdx).length t) :
    A.partialRealize F.codIdx F.rangeTuple t =
      Part.some ((f ⟨A.gensRealize F.domIdx t, gensRealize_mem_domainAt ht⟩ :
        (A.memberAt F.codIdx).domain) : ℕ) := by
  have hcoord := hf.choose_spec
  -- The source value, read inside the source member: the restricted term at the generator view.
  have hsrc : (⟨A.gensRealize F.domIdx t, gensRealize_mem_domainAt ht⟩ :
      (A.memberAt F.domIdx).domain) =
        (t.restrictVar fun x ↦ (⟨x.1, ht x.1 x.2⟩ : Fin (A.gens F.domIdx).length)).realize
          (A.gensView F.domIdx) := by
    letI : L.Structure ℕ := A.structureAt F.domIdx
    refine (Subtype.ext ?_).symm
    rw [(A.memberAt F.domIdx).realize_domain_val (A.gensView F.domIdx) _]
    exact (Term.realize_envFun_restrictVar (L := L) rfl t ht).symm
  -- The target evaluation: the same restricted term at the range tuple's view.
  rw [partialRealize_eq_realize_restrictVar hf.partialWellFormed.carrierValid hf.length.symm t ht,
    hsrc, ← HomClass.realize_term (L := L) f,
    (A.memberAt F.codIdx).realize_domain_val (⇑f ∘ A.gensView F.domIdx) _]
  exact congrArg Part.some (congrArg
    (fun v : Fin (A.gens F.domIdx).length → ℕ ↦
      @Term.realize L ℕ (A.structureAt F.codIdx) _ v
        (t.restrictVar fun x ↦ (⟨x.1, ht x.1 x.2⟩ : Fin (A.gens F.domIdx).length)))
    (funext fun x ↦ (hcoord x).symm))

/-- **The application computes the realizer.** On any element of the source member's carrier,
`applyPotentialPart` halts with the realizer's value there.

Membership, not equality of `Part`s: the search returns the *least* code, and nothing here needs
to know which one that is. -/
theorem applyPotentialPart_mem_realizer {F : PotentialEmbeddingData}
    {f : (A.memberAt F.domIdx).domain ↪[L] (A.memberAt F.codIdx).domain}
    (hf : A.PartialRealizes F f) {x : ℕ} (hx : x ∈ (A.memberAt F.domIdx).domain) :
    ((f ⟨x, hx⟩ : (A.memberAt F.codIdx).domain) : ℕ) ∈ A.applyPotentialPart F x := by
  obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 (gensTermCode_dom_iff.2 hx)
  obtain ⟨t, hdec, hrel⟩ := gensTermValue?_eq_some_iff.1 (gensTermValue?_of_mem_gensTermCode hm)
  have ht : Term.VarsBelow (A.gens F.domIdx).length t :=
    (Term.boundedDecode_eq_some_iff.1 hdec).2
  refine Part.mem_bind_iff.2 ⟨m, hm, Part.mem_bind_iff.2 ⟨t, Part.mem_ofOption.2 hdec, ?_⟩⟩
  rw [partialRealize_rangeTuple_eq_some hf ht]
  exact Part.mem_some_iff.2 (congrArg _ (congrArg _ (Subtype.ext hrel.symm)))

end PartialAgeIn

end FirstOrder.Language
