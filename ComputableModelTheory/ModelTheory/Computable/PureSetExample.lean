/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ChainAssembly
import ComputableModelTheory.ModelTheory.Computable.FraisseCriterion

/-!
# A finite fixture for the Fraïssé criterion: the two-member age in the empty language

`tinyAge` has two members up to isomorphism — the empty structure at index `0` and the one-point
structure at every positive index — in the empty language, where embeddings are injections and
every structure is trivially a structure. Its constant chain on the point, with identity steps,
assembles to a chain whose limit is a point; the criterion's hypotheses (semantic HP and JEP, stage
membership, the full extension property) are discharged on it by case analysis, and
`tinyAge.limit_isFraisseLimit` obtains `IsFraisseLimit` for that limit from the generic theorem.

This is the smallest fixture on which all four inputs of the criterion are non-vacuous: HP needs the
empty member (the closure of the empty tuple in the point is empty), JEP needs a common member, the
extension property has both an empty and a nonempty source case.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

/-! ### The empty language: injections are embeddings -/

/-- In the empty language, any injection is an embedding, for any two structure instances. -/
def emptyEmbedding {A B : Type*} [Language.empty.Structure A] [Language.empty.Structure B]
    (f : A ↪ B) : A ↪[Language.empty] B where
  toEmbedding := f
  map_fun' := fun g _ ↦ isEmptyElim g
  map_rel' := fun R _ ↦ isEmptyElim R

/-- In the empty language, any bijection is an isomorphism, for any two structure instances. -/
def emptyEquiv {A B : Type*} [Language.empty.Structure A] [Language.empty.Structure B]
    (e : A ≃ B) : A ≃[Language.empty] B where
  toEquiv := e
  map_fun' := fun g _ ↦ isEmptyElim g
  map_rel' := fun R _ ↦ isEmptyElim R

/-- A term of the empty language is a variable, so its value is a value of the valuation. -/
theorem empty_realize_mem_range {M α : Type*} [Language.empty.Structure M]
    (T : Language.empty.Term α) (v : α → M) : ∃ a, T.realize v = v a := by
  cases T with
  | var a => exact ⟨a, rfl⟩
  | func g _ => exact isEmptyElim g

/-- An injection out of a subsingleton into a pointed type. -/
def embOfSubsingleton {A B : Type*} [Subsingleton A] (b : B) : A ↪ B :=
  ⟨fun _ ↦ b, fun a a' _ ↦ Subsingleton.elim a a'⟩

/-! ### The two-member age -/

/-- The two-member age: the empty structure at `0`, the point `{0}` at every positive index. -/
noncomputable def tinyAge (O : Set (ℕ →. ℕ)) : PartialAgeIn O Language.empty where
  structureAt _ := emptyStructure
  enum? i m := if 0 < i ∧ m = 0 then some 0 else none
  enum?_computableIn :=
    ComputableIn.ite (c := fun p : ℕ × ℕ ↦ 0 < p.1 ∧ p.2 = 0)
      (((Primrec.and.to_comp.computableIn₂ (O := O)).comp
        ((Primrec.nat_lt.decide.to_comp.computableIn₂ (O := O)).comp (ComputableIn.const 0)
          ComputableIn.fst)
        (((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp ComputableIn.snd
          (ComputableIn.const 0))).of_eq fun _ ↦ by rw [Bool.decide_and])
      (ComputableIn.const (some 0)) (ComputableIn.const none)
  gens i := if i = 0 then [] else [0]
  gens_computableIn :=
    ComputableIn.ite (c := fun i : ℕ ↦ i = 0)
      (((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp ComputableIn.id
        (ComputableIn.const 0))
      (ComputableIn.const []) (ComputableIn.const [0])
  funEval _ d := isEmptyElim d
  funEval_recursiveIn := RecursiveIn.none.of_eq fun p ↦ isEmptyElim p.2
  funEval_correct := fun _ d _ ↦ isEmptyElim d
  relEval _ d := isEmptyElim d
  relEval_recursiveIn := RecursiveIn.none.of_eq fun p ↦ isEmptyElim p.2
  relEval_correct := fun _ d _ ↦ isEmptyElim d
  generates := fun i x ↦ by
    cases i with
    | zero =>
      change (∃ m, (if 0 < 0 ∧ m = 0 then some 0 else none) = some x) ↔
        ∃ T : Language.empty.Term (Fin ([] : Tuple ℕ).length),
          x = @Term.realize Language.empty ℕ emptyStructure _ (Tuple.view ([] : Tuple ℕ)) T
      constructor
      · rintro ⟨m, hm⟩
        rw [if_neg (fun h ↦ Nat.lt_irrefl 0 h.1)] at hm
        exact absurd hm (by simp)
      · rintro ⟨T, -⟩
        obtain ⟨a, -⟩ := empty_realize_mem_range T (Tuple.view ([] : Tuple ℕ))
        exact absurd a.2 (by simp)
    | succ i =>
      change (∃ m, (if 0 < i + 1 ∧ m = 0 then some 0 else none) = some x) ↔
        ∃ T : Language.empty.Term (Fin ([0] : Tuple ℕ).length),
          x = @Term.realize Language.empty ℕ emptyStructure _ (Tuple.view ([0] : Tuple ℕ)) T
      constructor
      · rintro ⟨m, hm⟩
        by_cases h : 0 < i + 1 ∧ m = 0
        · rw [if_pos h] at hm
          obtain rfl := Option.some.inj hm
          exact ⟨Term.var ⟨0, by simp⟩, rfl⟩
        · rw [if_neg h] at hm
          exact absurd hm (by simp)
      · rintro ⟨T, rfl⟩
        obtain ⟨a, ha⟩ := empty_realize_mem_range T (Tuple.view ([0] : Tuple ℕ))
        have ha0 : Tuple.view ([0] : Tuple ℕ) a = 0 := by
          obtain ⟨k, hk⟩ := a
          cases k with
          | zero => rfl
          | succ k => simp at hk
        exact ⟨0, by rw [ha, ha0, if_pos ⟨Nat.succ_pos i, rfl⟩]⟩

namespace tinyAge

variable (O : Set (ℕ →. ℕ))

theorem mem_domainAt_iff {i x : ℕ} : x ∈ (tinyAge O).domainAt i ↔ 0 < i ∧ x = 0 := by
  constructor
  · rintro ⟨m, hm⟩
    change (if 0 < i ∧ m = 0 then some 0 else none) = some x at hm
    by_cases h : 0 < i ∧ m = 0
    · rw [if_pos h] at hm
      exact ⟨h.1, (Option.some.inj hm).symm⟩
    · rw [if_neg h] at hm
      exact absurd hm (by simp)
  · rintro ⟨hi, rfl⟩
    refine ⟨0, ?_⟩
    change (if 0 < i ∧ 0 = 0 then some 0 else none) = some 0
    rw [if_pos ⟨hi, rfl⟩]

/-- Every member is a subsingleton: its only possible element is `0`. -/
instance (i : ℕ) : Subsingleton ((tinyAge O).memberAt i).domain :=
  ⟨fun a b ↦ Subtype.ext (((mem_domainAt_iff O).1 a.2).2.trans ((mem_domainAt_iff O).1 b.2).2.symm)⟩

theorem zero_mem_domainAt_one : (0 : ℕ) ∈ (tinyAge O).domainAt 1 :=
  (mem_domainAt_iff O).2 ⟨Nat.one_pos, rfl⟩

/-- The point of a positive member. -/
def point {i : ℕ} (hi : 0 < i) : ((tinyAge O).memberAt i).domain :=
  ⟨0, (mem_domainAt_iff O).2 ⟨hi, rfl⟩⟩

/-! ### Semantic HP and JEP -/

/-- **HP**: a substructure of a subsingleton member is empty or a point. -/
theorem hasHP : (tinyAge O).HasHP := by
  intro i n t
  by_cases h : Nonempty (Substructure.closure Language.empty (Set.range t))
  · refine ⟨1, ⟨emptyEquiv ⟨fun _ ↦ point O Nat.one_pos, fun _ ↦ Classical.choice h,
      fun _ ↦ Subsingleton.elim _ _, fun _ ↦ Subsingleton.elim _ _⟩⟩⟩
  · rw [not_nonempty_iff] at h
    have : IsEmpty ((tinyAge O).memberAt 0).domain :=
      ⟨fun a ↦ Nat.lt_irrefl 0 ((mem_domainAt_iff O).1 a.2).1⟩
    exact ⟨0, ⟨emptyEquiv (_root_.Equiv.equivOfIsEmpty _ _)⟩⟩

/-- **JEP**: every member embeds into the point. -/
theorem hasJEP : (tinyAge O).HasJEP := fun _ _ ↦
  ⟨1, ⟨emptyEmbedding (embOfSubsingleton (point O Nat.one_pos))⟩,
    ⟨emptyEmbedding (embOfSubsingleton (point O Nat.one_pos))⟩⟩

/-! ### The constant chain on the point, and its limit -/

/-- The constant chain on member `1` with identity steps. -/
noncomputable def chainData : (tinyAge O).EmbeddingChainData where
  d := fun _ ↦ 1
  step := fun _ ↦ (tinyAge O).idData 1
  step_domIdx := fun _ ↦ rfl
  step_codIdx := fun _ ↦ rfl
  step_isEmbedding := fun _ ↦ (tinyAge O).idData_partialIsEmbedding 1

theorem chainData_nonempty : ((tinyAge O).domainAt ((chainData O).d 0)).Nonempty :=
  ⟨0, zero_mem_domainAt_one O⟩

/-- The assembled chain, at the family's own oracle. -/
noncomputable def chain : CeStructureChainIn O Language.empty :=
  (chainData O).toChain (chainData_nonempty O) (le_refl O) (ComputableIn.const 1)
    (ComputableIn.const _)

/-- Its Level-1 limit, by Lemma 2.9. -/
noncomputable def limit : (chain O).LimitIn :=
  (chain O).toLimit ((chainData O).toChain_uniformEvaluators _ (le_refl O) _ _)

theorem chain_stage_domain (r : ℕ) : ((chain O).stageAt r).domain = (tinyAge O).domainAt 1 :=
  (chainData O).toChain_stage_domain _ (le_refl O) _ _ r

/-- Every stage carrier is the point's carrier, as a set; hence a subsingleton. -/
noncomputable def stageEquiv (r : ℕ) :
    ((chain O).stageAt r).domain ≃ ((tinyAge O).memberAt 1).domain :=
  _root_.Equiv.setCongr (chain_stage_domain O r)

instance (r : ℕ) : Subsingleton ((chain O).stageAt r).domain :=
  (stageEquiv O r).subsingleton

/-- The point of a stage. -/
noncomputable def stagePoint (r : ℕ) : ((chain O).stageAt r).domain :=
  (stageEquiv O r).symm (point O Nat.one_pos)

/-! ### The criterion's chain hypotheses -/

/-- **Stage membership**: every stage is the point. -/
theorem stage_iso (r : ℕ) :
    ∃ i, Nonempty
      (((chain O).stageAt r).domain ≃[Language.empty] ((tinyAge O).memberAt i).domain) :=
  ⟨1, ⟨emptyEquiv (stageEquiv O r)⟩⟩

/-- **The full extension property**: extend into the same stage by the constant map; the square
holds because the stage is a subsingleton. -/
theorem extension (r i j : ℕ)
    (f : ((tinyAge O).memberAt i).domain ↪[Language.empty] ((chain O).stageAt r).domain)
    (g : ((tinyAge O).memberAt i).domain ↪[Language.empty] ((tinyAge O).memberAt j).domain) :
    ∃ (s : ℕ) (h : ((tinyAge O).memberAt j).domain ↪[Language.empty] ((chain O).stageAt s).domain),
      r ≤ s ∧ ∀ a, (limit O).stageEmbedding s (h (g a)) = (limit O).stageEmbedding r (f a) :=
  ⟨r, emptyEmbedding (embOfSubsingleton (stagePoint O r)), le_rfl,
    fun _ ↦ congrArg _ (Subsingleton.elim _ _)⟩

/-- The chain hypotheses, packaged. -/
theorem fraisseChainData : CeStructureChainIn.LimitIn.FraisseChainData (tinyAge O) (limit O) :=
  ⟨stage_iso O, extension O⟩

/-- **The limit is a Fraïssé limit of the two-member class**, from the generic criterion with every
hypothesis discharged. -/
theorem limit_isFraisseLimit :
    Language.empty.IsFraisseLimit (tinyAge O).classSet (limit O).presentation.domain :=
  (fraisseChainData O).isFraisseLimit (hasHP O) (hasJEP O)

end tinyAge

end FirstOrder.Language
