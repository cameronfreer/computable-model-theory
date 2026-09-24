/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ListAgeExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: the bridge from one-point extensions to the full extension property

**Layer 1, the run.** `test_square_of_firesAt` is conditional CAP soundness in the run: actual
coded maps in, an actual right leg, a commuting member square, and the diagram's left leg as the
run's next step out. `test_one_point_from_firing` is the one-point extension property of the run's
chain, with its square in the limit; its only hypotheses beyond the run are the two maps and the
`(n+1)` width guard.

**Layer 2, the induction.** `test_extension_from_one_point` is the full extension property from
abstract one-point data and the mapped hereditary property; `test_run_isFraisseLimit` and
`test_omega_isFraisseLimit` are the criterion applied to the run and its ω structure.

**Discharged on the list age.** `test_listAge_isFraisseLimit` is `IsFraisseLimit` for the
initial-segment chain's limit, every hypothesis discharged through the bridge. The three pins the
bridge owes:

* `test_zero_added_generators` — prefix zero represents exactly `g(gens A)`: the zeroth prefix
  tuple has `A`'s width, and the prefix-zero state (the equivalence onto that image) holds.
* `test_repeated_generator` — recorded width increases without carrier growth: from `A = {0}` with
  generators `[0]` into `B = {0}` with generators `[0, 0]`, the `(n+1)` guard holds, the prefix
  tuples reach width `3`, and every member representing them is still a subsingleton.
* `test_nontrivial_square` — a stage that is not a subsingleton, and a request whose square has
  content: with `f` sending the point to `1` and `g` sending it to `0`, every extension produced by
  the one-point property is forced to disagree, in the limit, with the image of `0`.

Two rows exercise `.extension` end to end:

* `test_extension_zero_iterations` — a target recorded on generators `[]`: the prefix induction
  takes no step, and `.extension` passes from prefix zero straight through final identification.
* `test_prefix_induction` — `[0]` into `[0, 0, 1]` with `f` sending the point to `1` and `g` to
  `0`. The width gap is two, so the one-point property cannot be applied directly;
  `prefixState_succ` steps through prefix widths `1, 2, 3` on the unchanged singleton carrier `{0}`
  and then adds `1`, and the final square, obtained through `.extension`, sends the point away
  from the image of `0`.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section General

variable {K : PartialAgeIn O L} {W : PartialCAPWitness E K} {i : ℕ} (hOE : O ⊆ E)
  (h0 : (K.domainAt i).Nonempty) (Z : (PartialAgeIn.runChain K W i hOE h0).LimitIn)

/-- **Conditional CAP soundness in the run.** -/
theorem test_square_of_firesAt {q : RequirementData} {s : ℕ}
    (hfire : (PartialAgeIn.schedule K W i).FiresAt (encode q) s)
    (hf : K.PartialIsEmbedding (q.chainMap (PartialAgeIn.memberIdx K W i)))
    (hg : K.PartialIsEmbedding q.targetMap) :
    ∃ δ ∈ K.transportPart (PartialAgeIn.run K W i s).stages q.chainStage s,
      ∃ F ∈ K.compPart δ (q.chainMap (PartialAgeIn.memberIdx K W i)),
        ∃ D : AmalgamationDiagramData,
          K.PartialIsEmbedding D.rightToApex ∧
            K.PartialCommutes (PotentialSpanData.ofPair (F, q.targetMap)) D ∧
              PartialAgeIn.runStep K W i s = D.leftToApex := by
  obtain ⟨-, δ, hδ, -, -, -, F, hF, D, hD⟩ := PartialAgeIn.exists_square_of_firesAt hfire hf hg
  exact ⟨δ, hδ, F, hF, D, hD⟩

/-- **The one-point extension property of the run**, from firing. -/
theorem test_one_point_from_firing {r a b : ℕ}
    (f : (K.memberAt a).domain ↪[L] (K.memberAt (PartialAgeIn.memberIdx K W i r)).domain)
    (g : (K.memberAt a).domain ↪[L] (K.memberAt b).domain)
    (hw : (K.gens b).length = (K.gens a).length + 1) :
    ∃ s, r ≤ s ∧
      ∃ h : (K.memberAt b).domain ↪[L] (K.memberAt (PartialAgeIn.memberIdx K W i s)).domain,
        ∀ x, Z.stageEmbedding s (PartialAgeIn.runStageEquiv K W i hOE h0 s (h (g x))) =
          Z.stageEmbedding r (PartialAgeIn.runStageEquiv K W i hOE h0 r (f x)) :=
  PartialAgeIn.exists_one_point_extension hOE h0 Z f g hw

/-- **The full extension property from one-point data**, abstractly. -/
theorem test_extension_from_one_point {D : CeStructureChainIn E L} {Z : D.LimitIn}
    (P : K.OnePointExtension Z) (hHP : K.HasMappedHP) (r i j : ℕ)
    (f : (K.memberAt i).domain ↪[L] (D.stageAt r).domain)
    (g : (K.memberAt i).domain ↪[L] (K.memberAt j).domain) :
    ∃ (s : ℕ) (h : (K.memberAt j).domain ↪[L] (D.stageAt s).domain),
      r ≤ s ∧ ∀ a, Z.stageEmbedding s (h (g a)) = Z.stageEmbedding r (f a) :=
  P.extension hHP r i j f g

theorem test_run_isFraisseLimit (hHP : K.HasMappedHP) (hJ : K.HasJEP) :
    L.IsFraisseLimit K.classSet Z.presentation.domain :=
  PartialAgeIn.run_isFraisseLimit hOE h0 Z hHP hJ

theorem test_omega_isFraisseLimit (hHP : K.HasMappedHP) (hJ : K.HasJEP)
    (cert : Z.presentation.InfinitudeCertificate) :
    letI : L.Structure ℕ := (Z.omegaStructure cert).inst
    L.IsFraisseLimit K.classSet ℕ :=
  PartialAgeIn.omegaStructure_isFraisseLimit hOE h0 Z hHP hJ cert

/-- The selector properties give the semantic ones. -/
theorem test_semantic_of_selectors (hHP : PartialAgeIn.MappedPartialCHPIn E K)
    (hJ : PartialAgeIn.PartialCJEPIn E K) :
    K.HasMappedHP ∧ K.HasHP ∧ K.HasJEP :=
  ⟨hHP.hasMappedHP, hHP.hasMappedHP.hasHP, hJ.hasJEP⟩

end General

/-! ### The list age -/

section Fixture

open PartialAgeIn.OnePointExtension

variable (O : Set (ℕ →. ℕ))

theorem mem_domainAt_encode {l : List ℕ} {x : ℕ} :
    x ∈ (listAge O).domainAt (encode l) ↔ x ∈ l := by
  rw [listAge.mem_domainAt_iff, listOf_encode]

/-- Members coded by lists whose entries are all `0` are subsingletons. -/
theorem subsingleton_of_forall_zero {l : List ℕ} (hl : ∀ x ∈ l, x = 0) :
    Subsingleton ((listAge O).memberAt (encode l)).domain :=
  ⟨fun a b ↦ Subtype.ext (((hl _ ((mem_domainAt_encode O).1 a.2)).trans
    (hl _ ((mem_domainAt_encode O).1 b.2)).symm))⟩

/-- **`IsFraisseLimit` on the initial-segment chain's limit**, every hypothesis discharged. -/
theorem test_listAge_isFraisseLimit :
    Language.empty.IsFraisseLimit (listAge O).classSet (listAge.limit O).presentation.domain :=
  listAge.limit_isFraisseLimit O

/-- **Zero added generators**: the zeroth prefix tuple has `A`'s width, and the prefix-zero state
holds — the source is identified with the representative of `g(gens A)`. -/
theorem test_zero_added_generators {r a b : ℕ}
    (f : ((listAge O).memberAt a).domain ↪[Language.empty]
      ((listAge O).memberAt (listAge.segIdx r)).domain)
    (g : ((listAge O).memberAt a).domain ↪[Language.empty] ((listAge O).memberAt b).domain) :
    (prefixTuple (listAge O) g 0).length = ((listAge O).gens a).length ∧
      (listAge.onePoint O).PrefixState g f 0 :=
  ⟨(prefixTuple_length g (Nat.zero_le _)).trans (Nat.add_zero _),
    (listAge.onePoint O).prefixState_zero g f (listAge.hasMappedHP O)⟩

/-- **A repeated generator**: from `{0}` on `[0]` into `{0}` on `[0, 0]`, the `(n+1)` guard holds,
the prefix tuples reach width `3`, and their representatives stay subsingletons — recorded width
increases without carrier growth. -/
theorem test_repeated_generator :
    ((listAge O).gens (encode [0, 0])).length = ((listAge O).gens (encode [0])).length + 1 ∧
      Subsingleton ((listAge O).memberAt (encode [0, 0])).domain ∧
        ∀ g : ((listAge O).memberAt (encode [0])).domain ↪[Language.empty]
          ((listAge O).memberAt (encode [0, 0])).domain,
          (prefixTuple (listAge O) g 2).length = 3 ∧
            Subsingleton ((listAge O).memberAt (encode (prefixTuple (listAge O) g 2))).domain := by
  refine ⟨by rw [listAge.gens_eq, listAge.gens_eq, listOf_encode, listOf_encode]; rfl,
    subsingleton_of_forall_zero O (by simp), fun g ↦ ⟨?_, subsingleton_of_forall_zero O ?_⟩⟩
  · rw [prefixTuple_length g (by rw [listAge.gens_eq, listOf_encode]; exact le_rfl),
      listAge.gens_eq, listOf_encode]
    rfl
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
      have := (mem_domainAt_encode O).1 (g ((listAge O).gensView (encode [0]) k)).2
      simpa using this
    · have := List.mem_of_mem_take hx
      rw [listAge.gens_eq, listOf_encode] at this
      simpa using this

instance : Subsingleton ((listAge O).memberAt (encode [0])).domain :=
  subsingleton_of_forall_zero O (by simp)

/-- The point of the member `{0}`. -/
def pt : ((listAge O).memberAt (encode [0])).domain :=
  ⟨0, (mem_domainAt_encode O).2 (by simp)⟩

/-- `0` and `1` in stage `1`. -/
def stage1 (x : ℕ) (hx : x < 2) : ((listAge.chain O).stageAt 1).domain :=
  ⟨x, (listAge.mem_stage_iff O).2 hx⟩

/-- **A nontrivial commuting square**: stage `1` is not a subsingleton; with `f` sending the point
to `1` and `g` sending it to `0`, an extension exists, and every extension the one-point property
produces is forced, in the limit, away from the image of `0`. -/
theorem test_nontrivial_square :
    stage1 O 0 (by omega) ≠ stage1 O 1 (by omega) ∧
      let f : ((listAge O).memberAt (encode [0])).domain ↪[Language.empty]
        ((listAge O).memberAt (listAge.segIdx 1)).domain :=
        emptyEmbedding (embOfSubsingleton ⟨1, (listAge.mem_domainAt_segIdx O).2 (by omega)⟩)
      let g : ((listAge O).memberAt (encode [0])).domain ↪[Language.empty]
        ((listAge O).memberAt (encode [0, 1])).domain :=
        listAge.inclusion O (by rw [listOf_encode, listOf_encode]; simp)
      (∃ s, 1 ≤ s ∧ ∃ h : ((listAge O).memberAt (encode [0, 1])).domain ↪[Language.empty]
        ((listAge O).memberAt (listAge.segIdx s)).domain,
        ∀ x, (listAge.limit O).stageEmbedding s (listAge.stageEquiv O s (h (g x))) =
          (listAge.limit O).stageEmbedding 1 (listAge.stageEquiv O 1 (f x))) ∧
      ∀ (s : ℕ) (h : ((listAge O).memberAt (encode [0, 1])).domain ↪[Language.empty]
        ((listAge O).memberAt (listAge.segIdx s)).domain),
        (∀ x, (listAge.limit O).stageEmbedding s (listAge.stageEquiv O s (h (g x))) =
          (listAge.limit O).stageEmbedding 1 (listAge.stageEquiv O 1 (f x))) →
        (listAge.limit O).stageEmbedding s (listAge.stageEquiv O s (h (g (pt O)))) ≠
          (listAge.limit O).stageEmbedding 1 (stage1 O 0 (by omega)) := by
  refine ⟨fun h ↦ absurd (congrArg Subtype.val h) Nat.zero_ne_one, ?_, ?_⟩
  · exact (listAge.onePoint O).one_point 1 _ _ _ _
      (by rw [listAge.gens_eq, listAge.gens_eq, listOf_encode, listOf_encode]; rfl)
  · intro s h hsq hcontra
    rw [hsq] at hcontra
    have := congrArg Subtype.val (((listAge.limit O).stageEmbedding 1).injective hcontra)
    exact absurd this Nat.one_ne_zero

/-- **Zero iterations, through final identification**: the target is recorded on generators `[]`,
so the prefix induction takes no step, and `.extension` passes from the prefix-zero state straight
to the identification of the representative with the target. -/
theorem test_extension_zero_iterations (r : ℕ)
    (f : ((listAge O).memberAt (encode ([] : List ℕ))).domain ↪[Language.empty]
      ((listAge.chain O).stageAt r).domain)
    (g : ((listAge O).memberAt (encode ([] : List ℕ))).domain ↪[Language.empty]
      ((listAge O).memberAt (encode ([] : List ℕ))).domain) :
    (listAge O).gens (encode ([] : List ℕ)) = [] ∧
      ∃ (s : ℕ) (h : ((listAge O).memberAt (encode ([] : List ℕ))).domain ↪[Language.empty]
        ((listAge.chain O).stageAt s).domain),
        r ≤ s ∧ ∀ x, (listAge.limit O).stageEmbedding s (h (g x)) =
          (listAge.limit O).stageEmbedding r (f x) :=
  ⟨by rw [listAge.gens_eq, listOf_encode],
    (listAge.onePoint O).extension (listAge.hasMappedHP O) r _ _ f g⟩

/-- `f`: the point of `{0}` to `1` in stage `1`'s member. -/
noncomputable def ptToOne : ((listAge O).memberAt (encode [0])).domain ↪[Language.empty]
    ((listAge O).memberAt (listAge.segIdx 1)).domain :=
  emptyEmbedding (embOfSubsingleton ⟨1, (listAge.mem_domainAt_segIdx O).2 (by omega)⟩)

/-- `g`: `{0}` on `[0]` into `{0, 1}` on `[0, 0, 1]`, the point to `0`. -/
noncomputable def ptToWide : ((listAge O).memberAt (encode [0])).domain ↪[Language.empty]
    ((listAge O).memberAt (encode [0, 0, 1])).domain :=
  listAge.inclusion O (by rw [listOf_encode, listOf_encode]; simp)

/-- **The prefix induction itself**: from `[0]` into `[0, 0, 1]` the width gap is two, so the
one-point property does not apply directly. The prefix tuples have widths `1, 2, 3` on the
unchanged singleton carrier `{0}`, and `prefixState_succ` steps through each of them; the last step
adds `1`. The final square then comes through `.extension`, and it has content: the image of the
point is forced, in the limit, away from the image of `0`. -/
theorem test_prefix_induction :
    ((listAge O).gens (encode [0, 0, 1])).length = ((listAge O).gens (encode [0])).length + 2 ∧
      (∀ t ≤ 2, (prefixTuple (listAge O) (ptToWide O) t).length = t + 1 ∧
        ∀ x ∈ prefixTuple (listAge O) (ptToWide O) t, x = 0) ∧
      1 ∈ prefixTuple (listAge O) (ptToWide O) 3 ∧
      (listAge.onePoint O).PrefixState (r := 1) (ptToWide O) (ptToOne O) 1 ∧
      (listAge.onePoint O).PrefixState (r := 1) (ptToWide O) (ptToOne O) 2 ∧
      (listAge.onePoint O).PrefixState (r := 1) (ptToWide O) (ptToOne O) 3 ∧
      ∃ (s : ℕ) (h : ((listAge O).memberAt (encode [0, 0, 1])).domain ↪[Language.empty]
        ((listAge.chain O).stageAt s).domain),
        1 ≤ s ∧ (∀ x, (listAge.limit O).stageEmbedding s (h (ptToWide O x)) =
          (listAge.limit O).stageEmbedding 1 (listAge.stageEquiv O 1 (ptToOne O x))) ∧
        (listAge.limit O).stageEmbedding s (h (ptToWide O (pt O))) ≠
          (listAge.limit O).stageEmbedding 1 (stage1 O 0 (by omega)) := by
  have hA : (listAge O).gens (encode [0]) = [0] := by rw [listAge.gens_eq, listOf_encode]
  have hB : (listAge O).gens (encode [0, 0, 1]) = [0, 0, 1] := by
    rw [listAge.gens_eq, listOf_encode]
  have hBlen : ((listAge O).gens (encode [0, 0, 1])).length = 3 := by rw [hB]; rfl
  have hHP := listAge.hasMappedHP O
  have h1 := (listAge.onePoint O).prefixState_succ (ptToWide O) (ptToOne O) hHP (t := 0)
    (by omega) ((listAge.onePoint O).prefixState_zero (ptToWide O) (ptToOne O) hHP)
  have h2 := (listAge.onePoint O).prefixState_succ (ptToWide O) (ptToOne O) hHP (t := 1)
    (by omega) h1
  have h3 := (listAge.onePoint O).prefixState_succ (ptToWide O) (ptToOne O) hHP (t := 2)
    (by omega) h2
  obtain ⟨s, h, hrs, hsq⟩ := (listAge.onePoint O).extension hHP 1 _ _
    ((listAge.stageEquiv O 1).toEmbedding.comp (ptToOne O)) (ptToWide O)
  refine ⟨by rw [hA, hB]; rfl, fun t ht ↦ ⟨?_, fun x hx ↦ ?_⟩, ?_, h1, h2, h3, s, h, hrs, hsq,
    fun hcontra ↦ ?_⟩
  · rw [prefixTuple_length _ (by rw [hBlen]; omega), hA, List.length_singleton]
    omega
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
      have hk := (mem_domainAt_encode O).1 ((listAge O).gensView (encode [0]) k).2
      exact List.mem_singleton.1 hk
    · rw [hB] at hx
      obtain _ | _ | _ | t := t
      · simp at hx
      · simpa using hx
      · simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
          or_false, or_self] at hx
        exact hx
      · omega
  · refine List.mem_append_right _ ?_
    rw [hB]
    simp
  · rw [hsq] at hcontra
    have := congrArg Subtype.val (((listAge.limit O).stageEmbedding 1).injective hcontra)
    exact absurd this Nat.one_ne_zero

end Fixture

end FirstOrder.Language

#assert_standard_axioms FirstOrder.Language.test_square_of_firesAt
#assert_standard_axioms FirstOrder.Language.test_one_point_from_firing
#assert_standard_axioms FirstOrder.Language.test_extension_from_one_point
#assert_standard_axioms FirstOrder.Language.test_run_isFraisseLimit
#assert_standard_axioms FirstOrder.Language.test_omega_isFraisseLimit
#assert_standard_axioms FirstOrder.Language.test_semantic_of_selectors
#assert_standard_axioms FirstOrder.Language.test_listAge_isFraisseLimit
#assert_standard_axioms FirstOrder.Language.test_zero_added_generators
#assert_standard_axioms FirstOrder.Language.test_repeated_generator
#assert_standard_axioms FirstOrder.Language.test_nontrivial_square
#assert_standard_axioms FirstOrder.Language.test_extension_zero_iterations
#assert_standard_axioms FirstOrder.Language.test_prefix_induction
