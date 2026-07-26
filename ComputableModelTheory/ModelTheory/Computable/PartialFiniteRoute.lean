/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialMemberEmbedding

/-!
# The finite-search route: certificates and an effectively finite language

CHMM Observation 2.7's hypotheses, packaged as **supplied data**. Both interfaces here exist
to be assumed, never derived:

* `ExactFiniteCarriers` — for each index, an explicit list that is *exactly* that member's
  carrier, computable uniformly in the index. This is a genuine strengthening past Level 1
  and it is supplied, not recovered: a Definition 2.1 carrier is only c.e.
  (`domainAt_uniformly_ce`), so no cardinality, bound or exhaustive list may be read off an
  index. Assuming the list is the whole content of "the members are finite, effectively".

* `EffectivelyFiniteLanguage` — computable exhaustive lists of *all* function and all relation
  symbols. Note this is over the **packaged** symbol types `Σ n, L.Functions n` and
  `Σ n, L.Relations n`, which bundle the arity. Having `Fintype (L.Functions n)` for every `n`
  would **not** suffice: infinitely many arities could still be populated, and a candidate
  check quantifying over all symbols would not be a finite computation.

What these buy is decidability of the finite candidate checks, which then feeds
`exists_computableIn_selector` — the existing search engine. Nothing here builds another
search, and nothing here is a general finite-model library.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- **Uniform exact-finite carrier certificates.** An explicit list of each member's carrier,
computable uniformly in the index, together with the proof that it is exactly the carrier.

Supplied data, never derived: Definition 2.1 gives only uniformly c.e. carriers, so a list
like this cannot be recovered from an index. -/
structure ExactFiniteCarriers (B : PartialAgeIn O L) where
  /-- The claimed carrier of each member, as an explicit list. -/
  carrier : ℕ → List ℕ
  /-- The lists are computable uniformly in the index. -/
  carrier_computableIn : ComputableIn O carrier
  /-- The list is *exactly* the member's carrier — both inclusions. -/
  mem_carrier_iff : ∀ i x : ℕ, x ∈ carrier i ↔ x ∈ B.domainAt i

namespace ExactFiniteCarriers

variable {B : PartialAgeIn O L} (C : ExactFiniteCarriers B)

/-- List membership is decided by a fold, mirroring the guard pattern: no fused `Primrec`
chain, and the equality test crosses through the recorded `decide`-equality building block. -/
private theorem mem_list_computableIn :
    ComputableIn O fun p : ℕ × List ℕ ↦ decide (p.1 ∈ p.2) := by
  have hstep : ComputableIn₂ O fun (p : ℕ × List ℕ) (q : ℕ × Bool) ↦
      (decide (q.1 = p.1) || q.2) :=
    ((Primrec.or.comp
      ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst)).decide)
      (Primrec.snd.comp Primrec.snd)).to_comp.computableIn).to₂
  have h : ComputableIn O fun p : ℕ × List ℕ ↦
      p.2.foldr (fun b s ↦ decide (b = p.1) || s) false :=
    ComputableIn.list_foldr ComputableIn.snd (ComputableIn.const false) hstep
  refine h.of_eq fun p ↦ ?_
  obtain ⟨x, l⟩ := p
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.foldr_cons, ih]
    simp [List.mem_cons, eq_comm]

/-- Carrier membership becomes **decidable** — the Level-2 strengthening the certificates
supply. -/
def decidableMem (i x : ℕ) : Decidable (x ∈ B.domainAt i) :=
  decidable_of_iff _ (C.mem_carrier_iff i x)

/-- And uniformly decidable in the oracle: this is what makes the finite candidate checks
computations rather than merely finite. -/
theorem mem_domainAt_computablePredIn (C : ExactFiniteCarriers B) :
    ComputablePredIn O fun p : ℕ × ℕ ↦ p.2 ∈ B.domainAt p.1 := by
  refine ⟨fun p ↦ C.decidableMem p.1 p.2, ?_⟩
  have h : ComputableIn O fun p : ℕ × ℕ ↦ decide (p.2 ∈ C.carrier p.1) :=
    mem_list_computableIn.comp
      (ComputableIn.snd.pair (C.carrier_computableIn.comp ComputableIn.fst))
  exact h.of_eq fun p ↦ decide_eq_decide.2 (C.mem_carrier_iff p.1 p.2)

/-- Every entry of a carrier-valid range tuple is listed. -/
theorem carrierValid_iff (C : ExactFiniteCarriers B) (F : PotentialEmbeddingData) :
    B.CarrierValid F ↔ ∀ x ∈ F.rangeTuple, x ∈ C.carrier F.codIdx :=
  forall₂_congr fun x _ ↦ (C.mem_carrier_iff F.codIdx x).symm

end ExactFiniteCarriers

/-- **An effectively finite language.** Computable exhaustive lists of all function and all
relation symbols.

The lists range over the *packaged* symbol types, which bundle the arity. `Fintype
(L.Functions n)` for every `n` would not do: infinitely many arities could remain populated,
and then a check quantifying over all symbols is not a finite computation. -/
class EffectivelyFiniteLanguage (L : Language) [L.EffectiveLanguage] where
  /-- An exhaustive list of the packaged function symbols. -/
  functionSymbols : List L.FunctionSymbol
  /-- An exhaustive list of the packaged relation symbols. -/
  relationSymbols : List L.RelationSymbol
  /-- Exhaustive: every function symbol is listed. -/
  mem_functionSymbols : ∀ s : L.FunctionSymbol, s ∈ functionSymbols
  /-- Exhaustive: every relation symbol is listed. -/
  mem_relationSymbols : ∀ r : L.RelationSymbol, r ∈ relationSymbols

namespace EffectivelyFiniteLanguage

variable [EffectivelyFiniteLanguage L]

/-- A property of all function symbols is decided by scanning the exhaustive list. -/
def decidableForallFunctionSymbol (p : L.FunctionSymbol → Prop) [DecidablePred p] :
    Decidable (∀ s : L.FunctionSymbol, p s) :=
  decidable_of_iff (∀ s ∈ functionSymbols (L := L), p s)
    ⟨fun h s ↦ h s (mem_functionSymbols s), fun h s _ ↦ h s⟩

/-- A property of all relation symbols is decided by scanning the exhaustive list. -/
def decidableForallRelationSymbol (p : L.RelationSymbol → Prop) [DecidablePred p] :
    Decidable (∀ r : L.RelationSymbol, p r) :=
  decidable_of_iff (∀ r ∈ relationSymbols (L := L), p r)
    ⟨fun h r ↦ h r (mem_relationSymbols r), fun h r _ ↦ h r⟩

end EffectivelyFiniteLanguage

end FirstOrder.Language
