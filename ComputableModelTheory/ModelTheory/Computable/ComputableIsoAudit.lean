/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ComputableIso
import ComputableModelTheory.ModelTheory.Computable.SuccExample
import ComputableModelTheory.ModelTheory.Computable.GraphExample
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for computable isomorphisms

Named acceptance tests, checked by `#assert_standard_axioms`. Outside the root import
spine; CI checks it via `scripts/run-audit-modules.sh`.

Abstract gates: the derived inverse-side laws, injectivity and surjectivity; the
groupoid operations; the semantic bridge; the decidable-domain inclusion; the three
sharply distinct canonicalization statements; and uniform family canonicalization
from explicit uniform rank data.

Concrete gates exercise inverse computability and non-identity recodings, per the
acceptance bar — identity or rank-enumeration-only tests would not:

* an **infinite nontrivial permutation** — the parity swap `2k ↔ 2k+1` — transports
  the (all-ℕ) successor presentation, with concrete forward/backward values and a
  concrete transported function value computed through both conjugations;
* a **finite-domain recoding** — the two-node path graph on `{0, 1}` recoded onto
  `{5, 7}` by `x ↦ 2x + 5` — as a `DecidableIsoIn` with total maps, checked in both
  directions and included into the c.e. level.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

section AbstractGates

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {P Q W : CePresentationIn O L}

/-- Gate: derived inverse-side laws, injectivity, and surjectivity. -/
theorem test_ceIso_derived (e : CeIsoIn P Q) {n : ℕ} (f : L.Functions n)
    (R : L.Relations n) (w v : Fin n → ℕ) (hv : ∀ k, v k ∈ e.invFun (w k))
    {x₁ x₂ y : ℕ} (h₁ : y ∈ e.toFun x₁) (h₂ : y ∈ e.toFun x₂) (hy : y ∈ Q.domain) :
    (@Structure.funMap L ℕ P.str n f v
        ∈ e.invFun (@Structure.funMap L ℕ Q.str n f w)) ∧
      (@Structure.RelMap L ℕ P.str n R v ↔ @Structure.RelMap L ℕ Q.str n R w) ∧
      x₁ = x₂ ∧ ∃ x ∈ P.domain, y ∈ e.toFun x :=
  ⟨e.invFun_funMap n f w v hv, e.invFun_relMap n R w v hv,
    e.toFun_injective h₁ h₂, e.toFun_surjective hy⟩

/-- Gate: the groupoid operations and the semantic bridge exist. -/
theorem test_ceIso_groupoid (e₁ : CeIsoIn P Q) (e₂ : CeIsoIn Q W) :
    Nonempty (CeIsoIn P P) ∧ Nonempty (CeIsoIn Q P) ∧ Nonempty (CeIsoIn P W) ∧
      Nonempty (P.domain ≃[L] Q.domain) :=
  ⟨⟨CeIsoIn.refl P⟩, ⟨e₁.symm⟩, ⟨e₁.trans e₂⟩, ⟨e₁.toEquiv⟩⟩

/-- Gate: the three canonicalization statements — relative to the supplied
enumeration, nonuniform initial-segment existence, and uniform families only from
explicit uniform rank data. -/
theorem test_canonicalization (P : CePresentationIn O L)
    (F : ℕ → CePresentationIn O L) (h : UniformRankDataIn F) :
    Nonempty (CeIsoIn P P.rankPresentation) ∧
      (∃ Q : ComputableInitialSegmentPresentationIn O L,
        Q.str = P.rankPresentation.str ∧ Q.domain = P.rankPresentation.domain ∧
          Nonempty (CeIsoIn P P.rankPresentation)) ∧
      Nonempty (UniformCeIsoFamilyIn F fun i ↦ (F i).rankPresentation) :=
  ⟨⟨P.rankIso⟩, P.exists_initialSegment_iso, ⟨uniformRankIsoFamily F h⟩⟩

/-- Gate: the decidable-domain inclusion into the c.e. isomorphism level. -/
theorem test_decidableIso_inclusion {P' Q' : DecidablePresentationIn O L}
    (d : DecidableIsoIn P' Q') :
    Nonempty (CeIsoIn P'.toCePresentation Q'.toCePresentation) :=
  ⟨d.toCeIsoIn⟩

end AbstractGates

section ParityPermutation

variable (O : Set (ℕ →. ℕ))

/-- The parity swap `2k ↔ 2k + 1`: an infinite nontrivial computable involution. -/
def paritySwapFun (x : ℕ) : ℕ :=
  if x % 2 = 0 then x + 1 else x - 1

theorem paritySwapFun_invol (x : ℕ) : paritySwapFun (paritySwapFun x) = x := by
  unfold paritySwapFun
  by_cases h : x % 2 = 0
  · rw [if_pos h, if_neg (by omega), Nat.add_sub_cancel]
  · rw [if_neg h, if_pos (by omega)]
    omega

theorem paritySwapFun_computableIn : ComputableIn O paritySwapFun :=
  ComputableIn.ite
    ((Primrec.eq.comp
      (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0)).decide.to_comp.computableIn)
    ((Primrec.succ.to_comp.computableIn))
    ((Primrec.nat_sub.comp Primrec.id (Primrec.const 1)).to_comp.computableIn)

/-- The parity swap as a computable permutation. -/
def paritySwap : ComputablePermIn O where
  toFun := paritySwapFun
  invFun := paritySwapFun
  toFun_computableIn := paritySwapFun_computableIn O
  invFun_computableIn := paritySwapFun_computableIn O
  left_inv := paritySwapFun_invol
  right_inv := paritySwapFun_invol

/-- The all-ℕ successor presentation. -/
noncomputable def succPres : CePresentationIn O succLang :=
  ComputableStructureIn.toCePresentation
    { inst := succStructure, isComputable := succ_isComputable }

/-- Concrete gate: the parity-swap transport of the successor presentation exists as
a computable isomorphism — an infinite nontrivial permutation, not an identity or
rank recoding. -/
noncomputable def paritySuccIso :
    CeIsoIn (succPres O) ((succPres O).permPresentation (paritySwap O)) :=
  (succPres O).permIso (paritySwap O)

/-- Concrete gate: forward and backward values of the transport maps — `5 ↦ 4` and
`4 ↦ 5` — exercising inverse computability on realized pairs. -/
theorem test_parity_values :
    (4 : ℕ) ∈ (paritySuccIso O).toFun 5 ∧ (5 : ℕ) ∈ (paritySuccIso O).invFun 4 := by
  constructor
  · refine (Part.mem_map_iff _).2 ⟨5, CeIsoIn.mem_domId_iff.2 ⟨⟨5, rfl⟩, rfl⟩, ?_⟩
    show paritySwapFun 5 = 4
    rfl
  · refine (Part.mem_map_iff _).2 ⟨4, CeIsoIn.mem_domId_iff.2
      ⟨⟨5, by
        show paritySwapFun ((succPres O).enum 5) = 4
        show paritySwapFun 5 = 4
        rfl⟩, rfl⟩, ?_⟩
    show paritySwapFun 4 = 5
    rfl

/-- Concrete gate: the transported successor computes through both conjugations —
in the pushforward structure, `S(4) = 7`, since `4` decodes to `5`, `S(5) = 6`, and
`6` re-encodes to `7`. -/
theorem test_parity_transported_funMap :
    @Structure.funMap succLang ℕ ((succPres O).permPresentation (paritySwap O)).str 1
      SuccFunctions.succ (fun _ ↦ 4) = 7 := by
  show paritySwapFun (@Structure.funMap succLang ℕ (succPres O).str 1
    SuccFunctions.succ fun _ ↦ paritySwapFun 4) = 7
  show paritySwapFun (paritySwapFun 4 + 1) = 7
  rfl

end ParityPermutation

section FiniteRecoding

variable (O : Set (ℕ →. ℕ))

/-- The two-node path graph on the decidable domain `{0, 1}`. -/
noncomputable def twoNodePres : DecidablePresentationIn O Language.graph where
  str := pathGraphStructure
  domainB x := decide (x ≤ 1)
  domainB_computableIn :=
    ((Primrec.nat_le.comp Primrec.id (Primrec.const 1)).decide.to_comp.computableIn)
  witness := 0
  witness_mem := by decide
  domain_closed := fun _ f _ _ ↦ isEmptyElim f
  funEvalTotal _ := 0
  funEvalTotal_computableIn := ComputableIn.const 0
  funEvalTotal_correct := fun d _ ↦ isEmptyElim d.symbol
  relEvalTotal d :=
    decide (d.argsList[0]! + 1 = d.argsList[1]! ∨ d.argsList[1]! + 1 = d.argsList[0]!)
  relEvalTotal_computableIn := by
    have hget : ∀ i : ℕ, Primrec fun l : List ℕ ↦ l[i]! := fun i ↦
      (Primrec.option_getD.comp
        (Primrec.list_getElem?.comp Primrec.id (Primrec.const i))
        (Primrec.const default)).of_eq fun _ ↦ List.getElem!_eq_getElem?_getD.symm
    have h0 : Primrec fun d : RelationApplicationData Language.graph ℕ ↦
        d.argsList[0]! := (hget 0).comp RelationApplicationData.primrec_argsList
    have h1 : Primrec fun d : RelationApplicationData Language.graph ℕ ↦
        d.argsList[1]! := (hget 1).comp RelationApplicationData.primrec_argsList
    exact (PrimrecPred.or (Primrec.eq.comp (Primrec.succ.comp h0) h1)
      (Primrec.eq.comp (Primrec.succ.comp h1) h0)).decide.to_comp.computableIn
  relEvalTotal_correct := fun d _ ↦ by
    rw [decide_eq_true_iff]
    exact match d with
    | ⟨0, r, _⟩ => isEmptyElim r
    | ⟨1, r, _⟩ => isEmptyElim r
    | ⟨2, .adj, v⟩ => by
        show (v 0 + 1 = v 1 ∨ v 1 + 1 = v 0) ↔ (v 0 + 1 = v 1 ∨ v 1 + 1 = v 0)
        exact Iff.rfl
    | ⟨n + 3, r, _⟩ => isEmptyElim r

/-- The recoded structure on `{5, 7}`: adjacency of the decoded nodes under
`y ↦ (y - 5) / 2`. -/
@[reducible]
def recodedStr : Language.graph.Structure ℕ where
  RelMap | .adj => fun v ↦
    (v 0 - 5) / 2 + 1 = (v 1 - 5) / 2 ∨ (v 1 - 5) / 2 + 1 = (v 0 - 5) / 2

/-- The two-node path graph recoded onto the decidable domain `{5, 7}`. -/
noncomputable def recodedPres : DecidablePresentationIn O Language.graph where
  str := recodedStr
  domainB y := decide (y = 5 ∨ y = 7)
  domainB_computableIn :=
    ((PrimrecPred.or (Primrec.eq.comp Primrec.id (Primrec.const 5))
      (Primrec.eq.comp Primrec.id (Primrec.const 7))).decide.to_comp.computableIn)
  witness := 5
  witness_mem := by decide
  domain_closed := fun _ f _ _ ↦ isEmptyElim f
  funEvalTotal _ := 0
  funEvalTotal_computableIn := ComputableIn.const 0
  funEvalTotal_correct := fun d _ ↦ isEmptyElim d.symbol
  relEvalTotal d :=
    decide ((d.argsList[0]! - 5) / 2 + 1 = (d.argsList[1]! - 5) / 2 ∨
      (d.argsList[1]! - 5) / 2 + 1 = (d.argsList[0]! - 5) / 2)
  relEvalTotal_computableIn := by
    have hget : ∀ i : ℕ, Primrec fun l : List ℕ ↦ l[i]! := fun i ↦
      (Primrec.option_getD.comp
        (Primrec.list_getElem?.comp Primrec.id (Primrec.const i))
        (Primrec.const default)).of_eq fun _ ↦ List.getElem!_eq_getElem?_getD.symm
    have hdec : ∀ i : ℕ, Primrec fun d : RelationApplicationData Language.graph ℕ ↦
        (d.argsList[i]! - 5) / 2 := fun i ↦
      Primrec.nat_div.comp
        (Primrec.nat_sub.comp
          ((hget i).comp RelationApplicationData.primrec_argsList)
          (Primrec.const 5))
        (Primrec.const 2)
    exact (PrimrecPred.or
      (Primrec.eq.comp (Primrec.succ.comp (hdec 0)) (hdec 1))
      (Primrec.eq.comp (Primrec.succ.comp (hdec 1)) (hdec 0))).decide.to_comp.computableIn
  relEvalTotal_correct := fun d _ ↦ by
    rw [decide_eq_true_iff]
    exact match d with
    | ⟨0, r, _⟩ => isEmptyElim r
    | ⟨1, r, _⟩ => isEmptyElim r
    | ⟨2, .adj, v⟩ => by
        show ((v 0 - 5) / 2 + 1 = (v 1 - 5) / 2 ∨ (v 1 - 5) / 2 + 1 = (v 0 - 5) / 2)
          ↔ _
        exact Iff.rfl
    | ⟨n + 3, r, _⟩ => isEmptyElim r

/-- The finite-domain recoding `x ↦ 2x + 5` as a decidable isomorphism with total
maps. -/
noncomputable def twoNodeRecodeIso :
    DecidableIsoIn (twoNodePres O) (recodedPres O) where
  toFunTotal x := 2 * x + 5
  invFunTotal y := (y - 5) / 2
  toFunTotal_computableIn :=
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
      (Primrec.const 5)).to_comp.computableIn
  invFunTotal_computableIn :=
    (Primrec.nat_div.comp
      (Primrec.nat_sub.comp Primrec.id (Primrec.const 5))
      (Primrec.const 2)).to_comp.computableIn
  toFunTotal_mem := fun {x} hx ↦ by
    have h : x ≤ 1 := by
      have := (twoNodePres O).mem_domain_iff.1 hx
      exact of_decide_eq_true this
    show decide (2 * x + 5 = 5 ∨ 2 * x + 5 = 7) = true
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with rfl | rfl <;> decide
  invFunTotal_mem := fun {y} hy ↦ by
    have h : y = 5 ∨ y = 7 := of_decide_eq_true ((recodedPres O).mem_domain_iff.1 hy)
    show decide ((y - 5) / 2 ≤ 1) = true
    rcases h with rfl | rfl <;> decide
  invFunTotal_toFunTotal := fun {x} hx ↦ by
    have h : x ≤ 1 := of_decide_eq_true ((twoNodePres O).mem_domain_iff.1 hx)
    omega
  toFunTotal_invFunTotal := fun {y} hy ↦ by
    have h : y = 5 ∨ y = 7 := of_decide_eq_true ((recodedPres O).mem_domain_iff.1 hy)
    rcases h with rfl | rfl <;> rfl
  toFunTotal_funMap := fun _ f _ _ ↦ isEmptyElim f
  toFunTotal_relMap := fun n R v hv ↦ by
    exact match n, R, v, hv with
    | 2, .adj, v, hv => by
        show ((2 * v 0 + 5 - 5) / 2 + 1 = (2 * v 1 + 5 - 5) / 2 ∨
            (2 * v 1 + 5 - 5) / 2 + 1 = (2 * v 0 + 5 - 5) / 2)
          ↔ (v 0 + 1 = v 1 ∨ v 1 + 1 = v 0)
        omega
    | 0, R, _, _ => isEmptyElim R
    | 1, R, _, _ => isEmptyElim R
    | _ + 3, R, _, _ => isEmptyElim R

/-- Concrete gate: both directions of the finite recoding on concrete elements —
`1 ↦ 7` and `7 ↦ 1` — and the c.e. inclusion of the recoding. -/
theorem test_twoNode_recode_values :
    (twoNodeRecodeIso O).toFunTotal 1 = 7 ∧ (twoNodeRecodeIso O).invFunTotal 7 = 1 ∧
      Nonempty (CeIsoIn (twoNodePres O).toCePresentation
        (recodedPres O).toCePresentation) :=
  ⟨rfl, rfl, ⟨(twoNodeRecodeIso O).toCeIsoIn⟩⟩

/-- Concrete gate: the recoding transfers the adjacency verdict — `5, 7` are adjacent
in the recoded structure exactly because `0, 1` are adjacent in the path graph. -/
theorem test_twoNode_recode_relMap :
    @Structure.RelMap Language.graph ℕ (recodedPres O).str 2
      (.adj : Language.graph.Relations 2) ![5, 7] := by
  show ((5 : ℕ) - 5) / 2 + 1 = (7 - 5) / 2 ∨ ((7 : ℕ) - 5) / 2 + 1 = (5 - 5) / 2
  decide

end FiniteRecoding

end FirstOrder.Language

open FirstOrder.Language

#assert_standard_axioms test_ceIso_derived
#assert_standard_axioms test_ceIso_groupoid
#assert_standard_axioms test_canonicalization
#assert_standard_axioms test_decidableIso_inclusion
#assert_standard_axioms paritySuccIso
#assert_standard_axioms test_parity_values
#assert_standard_axioms test_parity_transported_funMap
#assert_standard_axioms twoNodeRecodeIso
#assert_standard_axioms test_twoNode_recode_values
#assert_standard_axioms test_twoNode_recode_relMap
