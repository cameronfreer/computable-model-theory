/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ExtensionBridge
import ComputableModelTheory.ModelTheory.Computable.PureSetExample

/-!
# The age of all finite lists, and the initial-segment chain

A spine fixture for the extension-bridge audit: an age in the empty language whose member `i` is the
pure set of the entries of the list coded by `i`, with that list — repetitions included — as its
recorded generators. It has the mapped hereditary property by inclusion (a list of entries of a
member *is* the generator list of the member it codes) and joint embedding by concatenation.

Its **initial-segment chain** has stage `n` on the member `{0, …, n}` with inclusion steps. The
one-point extension property holds by extending a finite injection with fresh values, so
`OnePointExtension.extension` applies and the limit is a Fraïssé limit of the class of finite pure
sets. Stages here are not subsingletons, so the commuting squares have content.

`listOf`, the list coded by an index, is sealed: every statement about a member goes through
`listOf_encode`, and nothing unfolds the decoding on a free code.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

/-- The list coded by `i`. Sealed below; the fixture never unfolds it. -/
def listOf (i : ℕ) : List ℕ := Denumerable.ofNat (List ℕ) i

theorem listOf_encode (l : List ℕ) : listOf (encode l) = l := Denumerable.ofNat_encode l

theorem primrec_listOf : Primrec listOf := Primrec.ofNat (List ℕ)

attribute [irreducible] listOf

/-- In the empty language, the term-closure of a list's entries is its entries. -/
theorem empty_generates (l : List ℕ) (x : ℕ) :
    (∃ m : ℕ, l[m]? = some x) ↔ ∃ T : Language.empty.Term (Fin l.length),
      x = @Term.realize Language.empty ℕ emptyStructure _ (Tuple.view l) T := by
  rw [← List.mem_iff_getElem?]
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := List.mem_iff_get.1 hx
    exact ⟨Term.var k, (Tuple.view_eq_get l k).symm⟩
  · rintro ⟨T, rfl⟩
    obtain ⟨a, ha⟩ := empty_realize_mem_range T (Tuple.view l)
    rw [ha, Tuple.view_eq_get]
    exact List.get_mem _ _

/-- **The age of all finite lists**: member `i` is the pure set of the entries of `listOf i`, with
that list as its recorded generators. -/
noncomputable def listAge (O : Set (ℕ →. ℕ)) : PartialAgeIn O Language.empty where
  structureAt _ := emptyStructure
  enum? i m := (listOf i)[m]?
  enum?_computableIn :=
    (Primrec.list_getElem?.comp (primrec_listOf.comp Primrec.fst) Primrec.snd).to_comp.computableIn
  gens := listOf
  gens_computableIn := primrec_listOf.to_comp.computableIn
  funEval _ d := isEmptyElim d
  funEval_recursiveIn := RecursiveIn.none.of_eq fun p ↦ isEmptyElim p.2
  funEval_correct := fun _ d _ ↦ isEmptyElim d
  relEval _ d := isEmptyElim d
  relEval_recursiveIn := RecursiveIn.none.of_eq fun p ↦ isEmptyElim p.2
  relEval_correct := fun _ d _ ↦ isEmptyElim d
  generates := fun i x ↦ empty_generates (listOf i) x

namespace listAge

variable (O : Set (ℕ →. ℕ))

theorem mem_domainAt_iff {i x : ℕ} : x ∈ (listAge O).domainAt i ↔ x ∈ listOf i :=
  List.mem_iff_getElem?.symm

theorem gens_eq (i : ℕ) : (listAge O).gens i = listOf i := rfl

/-- The inclusion of one member into another whose list contains its entries. -/
noncomputable def inclusion {i j : ℕ} (h : ∀ x ∈ listOf i, x ∈ listOf j) :
    ((listAge O).memberAt i).domain ↪[Language.empty] ((listAge O).memberAt j).domain :=
  emptyEmbedding
    ⟨fun x ↦ ⟨x.1, (mem_domainAt_iff O).2 (h x.1 ((mem_domainAt_iff O).1 x.2))⟩,
      fun _ _ hxy ↦ Subtype.ext (Subtype.mk.inj hxy)⟩

@[simp] theorem inclusion_coe {i j : ℕ} (h : ∀ x ∈ listOf i, x ∈ listOf j)
    (x : ((listAge O).memberAt i).domain) :
    ((inclusion O h x : ((listAge O).memberAt j).domain) : ℕ) = x :=
  rfl

/-- **The mapped hereditary property, by inclusion**: a list of entries of a member is the
generator list of the member it codes. -/
theorem hasMappedHP : (listAge O).HasMappedHP := by
  intro e s hs
  have hs' : ∀ x ∈ listOf (encode s), x ∈ listOf e := by
    rw [listOf_encode]
    exact fun x hx ↦ (mem_domainAt_iff O).1 (hs x hx)
  refine ⟨encode s, congrArg List.length (listOf_encode s), inclusion O hs', fun k ↦ ?_⟩
  show (listOf (encode s)).get k = s.get _
  exact List.get_of_eq (listOf_encode s) k

/-- **Joint embedding, by concatenation.** -/
theorem hasJEP : (listAge O).HasJEP := fun i j ↦
  ⟨encode (listOf i ++ listOf j),
    ⟨inclusion O fun x hx ↦ by rw [listOf_encode]; exact List.mem_append_left _ hx⟩,
    ⟨inclusion O fun x hx ↦ by rw [listOf_encode]; exact List.mem_append_right _ hx⟩⟩

/-! ### The initial-segment chain -/

/-- The member `{0, …, n}`. -/
def segIdx (n : ℕ) : ℕ := encode (List.range (n + 1))

theorem listOf_segIdx (n : ℕ) : listOf (segIdx n) = List.range (n + 1) := listOf_encode _

theorem mem_domainAt_segIdx {n x : ℕ} : x ∈ (listAge O).domainAt (segIdx n) ↔ x < n + 1 := by
  rw [mem_domainAt_iff, listOf_segIdx, List.mem_range]

theorem segIdx_subset (n : ℕ) : ∀ x ∈ listOf (segIdx n), x ∈ listOf (segIdx (n + 1)) := by
  intro x hx
  rw [listOf_segIdx] at hx ⊢
  exact List.mem_range.2 (Nat.lt_succ_of_lt (List.mem_range.1 hx))

/-- The step from `{0, …, n}` to `{0, …, n + 1}`: the inclusion, coded by the generators. -/
def segStep (n : ℕ) : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple (segIdx n, segIdx (n + 1), List.range (n + 1))

theorem segStep_realizes (n : ℕ) :
    (listAge O).PartialRealizes (segStep n) (inclusion O (segIdx_subset n)) :=
  ⟨congrArg List.length (listOf_segIdx n), fun k ↦ List.get_of_eq (listOf_segIdx n) k⟩

/-- The chain data: initial segments with inclusion steps. -/
noncomputable def chainData : (listAge O).EmbeddingChainData where
  d := segIdx
  step := segStep
  step_domIdx _ := rfl
  step_codIdx _ := rfl
  step_isEmbedding n := ⟨_, segStep_realizes O n⟩

theorem segIdx_computableIn {E : Set (ℕ →. ℕ)} : ComputableIn E segIdx :=
  (Primrec.encode.comp (Primrec.list_range.comp Primrec.succ)).to_comp.computableIn

theorem segStep_computableIn {E : Set (ℕ →. ℕ)} : ComputableIn E segStep :=
  (PotentialEmbeddingData.primrec_ofTriple.comp
    ((Primrec.encode.comp (Primrec.list_range.comp Primrec.succ)).pair
      ((Primrec.encode.comp (Primrec.list_range.comp (Primrec.succ.comp Primrec.succ))).pair
        (Primrec.list_range.comp Primrec.succ)))).to_comp.computableIn

theorem chainData_nonempty : ((listAge O).domainAt ((chainData O).d 0)).Nonempty :=
  ⟨0, (mem_domainAt_segIdx O).2 Nat.one_pos⟩

/-- The assembled chain, at the family's own oracle. -/
noncomputable def chain : CeStructureChainIn O Language.empty :=
  (chainData O).toChain (chainData_nonempty O) (le_refl O) segIdx_computableIn
    segStep_computableIn

/-- Its Level-1 limit, by Lemma 2.9. -/
noncomputable def limit : (chain O).LimitIn :=
  (chain O).toLimit ((chainData O).toChain_uniformEvaluators _ (le_refl O) _ _)

/-- Each stage is its initial segment. -/
noncomputable def stageEquiv (n : ℕ) :
    ((listAge O).memberAt (segIdx n)).domain ≃[Language.empty] ((chain O).stageAt n).domain :=
  (chainData O).stageEquiv _ (le_refl O) _ _ n

theorem mem_stage_iff {n x : ℕ} : x ∈ ((chain O).stageAt n).domain ↔ x < n + 1 := by
  rw [show ((chain O).stageAt n).domain = (listAge O).domainAt (segIdx n) from
    (chainData O).toChain_stage_domain _ _ _ _ n]
  exact mem_domainAt_segIdx O

/-- **The steps are inclusions, in the limit**: an element of stage `r` is the same element of every
later stage. -/
theorem stageEmbedding_le {r s : ℕ} (hrs : r ≤ s) (x : ℕ) (hx : x ∈ ((chain O).stageAt r).domain) :
    ∃ hx' : x ∈ ((chain O).stageAt s).domain,
      (limit O).stageEmbedding r ⟨x, hx⟩ = (limit O).stageEmbedding s ⟨x, hx'⟩ := by
  induction s, hrs using Nat.le_induction with
  | base => exact ⟨hx, rfl⟩
  | succ s _ ih =>
    obtain ⟨hx', hEq⟩ := ih
    obtain ⟨hx'', hEq'⟩ := (limit O).stageEmbedding_step hx' (y := x) (by
      change x ∈ (listAge O).applyPotentialPart (segStep s) x
      exact (listAge O).applyPotentialPart_mem_realizer (segStep_realizes O s)
        ((stageEquiv O s).symm ⟨x, hx'⟩).2)
    exact ⟨hx'', hEq.trans hEq'⟩

/-! ### The one-point extension property, by fresh values -/

section OnePoint

variable {r a b : ℕ}
  (f : ((listAge O).memberAt a).domain ↪[Language.empty] ((listAge O).memberAt (segIdx r)).domain)
  (g : ((listAge O).memberAt a).domain ↪[Language.empty] ((listAge O).memberAt b).domain)

open scoped Classical in
/-- The value of the extension at `y`: `f`'s value on the preimage when `y` is in `g`'s range, and
a fresh value above `r` indexed by `y`'s position in `b`'s list otherwise. -/
noncomputable def extendVal (y : ((listAge O).memberAt b).domain) : ℕ :=
  if h : ∃ x, g x = y then (f h.choose : ℕ) else r + 1 + (listOf b).idxOf y.1

theorem extendVal_of_range (x : ((listAge O).memberAt a).domain) :
    extendVal O f g (g x) = f x := by
  unfold extendVal
  rw [dif_pos ⟨x, rfl⟩]
  exact congrArg (fun z ↦ ((f z : ((listAge O).memberAt (segIdx r)).domain) : ℕ))
    (g.injective (Classical.choose_spec (⟨x, rfl⟩ : ∃ x', g x' = g x)))

theorem extendVal_lt (y : ((listAge O).memberAt b).domain) :
    extendVal O f g y < r + 1 + (listOf b).length + 1 := by
  unfold extendVal
  split_ifs with h
  · exact lt_of_lt_of_le ((mem_domainAt_segIdx O).1 (f _).2) (by omega)
  · have := List.idxOf_lt_length_of_mem ((mem_domainAt_iff O).1 y.2)
    omega

theorem extendVal_injective : Function.Injective (extendVal O f g) := by
  intro y₁ y₂ hy
  unfold extendVal at hy
  split_ifs at hy with h₁ h₂ h₂
  · have := f.injective (Subtype.ext hy)
    rw [← Exists.choose_spec h₁, ← Exists.choose_spec h₂, this]
  · exact absurd hy (Nat.ne_of_lt (lt_of_lt_of_le ((mem_domainAt_segIdx O).1 (f _).2) (by omega)))
  · exact absurd hy.symm
      (Nat.ne_of_lt (lt_of_lt_of_le ((mem_domainAt_segIdx O).1 (f _).2) (by omega)))
  · exact Subtype.ext ((List.idxOf_inj ((mem_domainAt_iff O).1 y₁.2)).1 (Nat.add_left_cancel hy))

/-- The extension, as an embedding into `{0, …, r + |b| + 1}`. -/
noncomputable def extend : ((listAge O).memberAt b).domain ↪[Language.empty]
    ((listAge O).memberAt (segIdx (r + 1 + (listOf b).length))).domain :=
  emptyEmbedding
    ⟨fun y ↦ ⟨extendVal O f g y, (mem_domainAt_segIdx O).2 (extendVal_lt O f g y)⟩,
      fun _ _ h ↦ extendVal_injective O f g (congrArg Subtype.val h)⟩

theorem extend_coe (y : ((listAge O).memberAt b).domain) :
    ((extend O f g y : ((listAge O).memberAt (segIdx (r + 1 + (listOf b).length))).domain) : ℕ) =
      extendVal O f g y :=
  rfl

/-- **The one-point extension property** of the initial-segment chain. The width hypothesis is not
needed here: any finite member extends by fresh values. -/
theorem one_point (r a b : ℕ)
    (f : ((listAge O).memberAt a).domain ↪[Language.empty] ((listAge O).memberAt (segIdx r)).domain)
    (g : ((listAge O).memberAt a).domain ↪[Language.empty] ((listAge O).memberAt b).domain)
    (_ : ((listAge O).gens b).length = ((listAge O).gens a).length + 1) :
    ∃ s, r ≤ s ∧ ∃ h : ((listAge O).memberAt b).domain ↪[Language.empty]
      ((listAge O).memberAt (segIdx s)).domain,
      ∀ x, (limit O).stageEmbedding s (stageEquiv O s (h (g x))) =
        (limit O).stageEmbedding r (stageEquiv O r (f x)) := by
  refine ⟨r + 1 + (listOf b).length, by omega, extend O f g, fun x ↦ ?_⟩
  obtain ⟨hx', hEq⟩ := stageEmbedding_le O (r := r) (s := r + 1 + (listOf b).length) (by omega)
    (f x : ℕ) (stageEquiv O r (f x)).2
  refine (congrArg ((limit O).stageEmbedding _) (Subtype.ext ?_ :
    stageEquiv O _ (extend O f g (g x)) = ⟨(f x : ℕ), hx'⟩)).trans hEq.symm
  exact extendVal_of_range O f g x

end OnePoint

/-- **The one-point extension data** of the initial-segment chain. -/
noncomputable def onePoint : (listAge O).OnePointExtension (limit O) :=
  ⟨segIdx, stageEquiv O, one_point O⟩

/-- The chain hypotheses of Lemma 3.8, through the bridge. -/
theorem fraisseChainData : CeStructureChainIn.LimitIn.FraisseChainData (listAge O) (limit O) :=
  (onePoint O).toFraisseChainData (hasMappedHP O)

/-- **The limit of the initial segments is a Fraïssé limit of the finite pure sets**, from the
bridge and the criterion with every hypothesis discharged. -/
theorem limit_isFraisseLimit :
    Language.empty.IsFraisseLimit (listAge O).classSet (limit O).presentation.domain :=
  (fraisseChainData O).isFraisseLimit (hasMappedHP O).hasHP (hasJEP O)

end listAge

end FirstOrder.Language
