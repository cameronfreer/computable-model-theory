/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.ListSections
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

/-! ### The normalized support and the finite maps

The supplied list may repeat, so it is normalized once. Normalizing the **source** is what
makes `f.length = (support i).length ∧ f.Nodup` express injectivity — against a repeating
source it would not, since a repeated element forces a repeated image. -/

/-- The duplicate-free carrier. Derived here rather than demanded of `ExactFiniteCarriers`,
which stores no `Nodup`. (`List.dedup` is mathlib's `DecidableEq` version of `eraseDups`, and
the one carrying the membership and `Nodup` lemmas.) -/
def support (i : ℕ) : List ℕ := (C.carrier i).dedup

theorem support_nodup (i : ℕ) : (C.support i).Nodup :=
  List.nodup_dedup _

@[simp]
theorem mem_support_iff_domainAt (i x : ℕ) : x ∈ C.support i ↔ x ∈ B.domainAt i :=
  (List.mem_dedup).trans (C.mem_carrier_iff i x)

/-- All candidate finite maps from member `i` to member `j`: image lists indexed positionally
by the normalized source. -/
def finiteMaps (i j : ℕ) : List (List ℕ) :=
  (List.replicate (C.support i).length (C.support j)).sections

theorem mem_finiteMaps_iff (i j : ℕ) (f : List ℕ) :
    f ∈ C.finiteMaps i j ↔ f.length = (C.support i).length ∧ ∀ y ∈ f, y ∈ C.support j :=
  List.mem_sections_replicate

/-! ### Applying a coded map

`Option`-valued by construction: a source element that is not listed gets index
`(support i).length`, which is out of range for an image list of the same length, so the
lookup is `none`. The checker must therefore reject a missing lookup — it has no default to
fall back on. -/

/-- Apply a coded map to a value: locate it in the normalized source and read off the image. -/
def applyMap (i : ℕ) (f : List ℕ) (x : ℕ) : Option ℕ :=
  f[(C.support i).findIdx (fun y ↦ y == x)]?

/-- Off the source there is no image — structurally, not by convention. -/
theorem applyMap_eq_none (i : ℕ) {f : List ℕ} {x : ℕ}
    (hlen : f.length = (C.support i).length) (hx : x ∉ C.support i) :
    C.applyMap i f x = Option.none := by
  rw [applyMap, List.getElem?_eq_none_iff, hlen]
  exact Nat.le_of_eq
    (List.findIdx_eq_length.2 fun y hy ↦ by
      have hne : y ≠ x := fun hyx ↦ hx (hyx ▸ hy)
      simpa using hne).symm

/-- On the source the lookup succeeds, and its value lies in the target's carrier. -/
theorem exists_applyMap_eq_some {i j : ℕ} {f : List ℕ} (hf : f ∈ C.finiteMaps i j)
    {x : ℕ} (hx : x ∈ B.domainAt i) :
    ∃ y, C.applyMap i f x = Option.some y ∧ y ∈ B.domainAt j := by
  obtain ⟨hlen, hmem⟩ := (C.mem_finiteMaps_iff i j f).1 hf
  have hxs : x ∈ C.support i := (C.mem_support_iff_domainAt i x).2 hx
  have hlt : (C.support i).findIdx (fun y ↦ y == x) < f.length := by
    rw [hlen]
    exact List.findIdx_lt_length.2 ⟨x, hxs, by simp⟩
  refine ⟨f[(C.support i).findIdx (fun y ↦ y == x)], List.getElem?_eq_getElem hlt, ?_⟩
  exact (C.mem_support_iff_domainAt j _).1 (hmem _ (List.getElem_mem hlt))

/-! ### Completeness of the enumeration

Every genuine map between the carriers is enumerated, and `Nodup` of its image list is exactly
injectivity on the support. This is what keeps the reverse direction of the checker's `iff` a
lookup argument rather than an enumeration argument. -/

/-- The image list of a genuine map, indexed by the normalized source. -/
def imageList (i : ℕ) (g : ℕ → ℕ) : List ℕ := (C.support i).map g

theorem imageList_length (i : ℕ) (g : ℕ → ℕ) :
    (C.imageList i g).length = (C.support i).length :=
  List.length_map _

/-- Every carrier-respecting map is enumerated. -/
theorem imageList_mem_finiteMaps {i j : ℕ} {g : ℕ → ℕ}
    (hg : ∀ x ∈ B.domainAt i, g x ∈ B.domainAt j) : C.imageList i g ∈ C.finiteMaps i j := by
  refine (C.mem_finiteMaps_iff i j _).2 ⟨C.imageList_length i g, fun y hy ↦ ?_⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  exact (C.mem_support_iff_domainAt j _).2 (hg x ((C.mem_support_iff_domainAt i x).1 hx))

/-- **Codes read back genuine maps.** The code of a genuine map applies to exactly that map on
the carrier — the bridge making the embedding-to-code direction immediate. -/
theorem applyMap_imageList {i : ℕ} {g : ℕ → ℕ} {x : ℕ} (hx : x ∈ B.domainAt i) :
    C.applyMap i (C.imageList i g) x = Option.some (g x) := by
  have hxs : x ∈ C.support i := (C.mem_support_iff_domainAt i x).2 hx
  have hlt : (C.support i).findIdx (fun y ↦ y == x) < (C.support i).length :=
    List.findIdx_lt_length.2 ⟨x, hxs, by simp⟩
  have hval : (C.support i)[(C.support i).findIdx (fun y ↦ y == x)] = x := by
    have := List.findIdx_getElem (p := fun y ↦ y == x) (xs := C.support i) (w := hlt)
    simpa using this
  rw [applyMap]
  show ((C.support i).map g)[(C.support i).findIdx (fun y ↦ y == x)]? = Option.some (g x)
  rw [List.getElem?_map, List.getElem?_eq_getElem hlt, hval]
  rfl

/-- **A duplicate-free code is injective.** Successful lookups agreeing on carrier elements
force the inputs equal — the main ingredient for turning a successful code back into an actual
embedding. -/
theorem applyMap_injective_of_nodup {i j : ℕ} {f : List ℕ} (hf : f ∈ C.finiteMaps i j)
    (hn : f.Nodup) {x y : ℕ} (hx : x ∈ B.domainAt i) (hy : y ∈ B.domainAt i)
    (hxy : C.applyMap i f x = C.applyMap i f y) : x = y := by
  obtain ⟨hlen, -⟩ := (C.mem_finiteMaps_iff i j f).1 hf
  have hxs : x ∈ C.support i := (C.mem_support_iff_domainAt i x).2 hx
  have hys : y ∈ C.support i := (C.mem_support_iff_domainAt i y).2 hy
  have hltx : (C.support i).findIdx (fun z ↦ z == x) < (C.support i).length :=
    List.findIdx_lt_length.2 ⟨x, hxs, by simp⟩
  have hlty : (C.support i).findIdx (fun z ↦ z == y) < (C.support i).length :=
    List.findIdx_lt_length.2 ⟨y, hys, by simp⟩
  have hltx' : (C.support i).findIdx (fun z ↦ z == x) < f.length := by rw [hlen]; exact hltx
  have hlty' : (C.support i).findIdx (fun z ↦ z == y) < f.length := by rw [hlen]; exact hlty
  rw [applyMap, applyMap, List.getElem?_eq_getElem hltx', List.getElem?_eq_getElem hlty',
    Option.some_inj] at hxy
  have hidx := (hn.getElem_inj_iff (hi := hltx') (hj := hlty')).1 hxy
  have hvx : (C.support i)[(C.support i).findIdx (fun z ↦ z == x)] = x := by
    have := List.findIdx_getElem (p := fun z ↦ z == x) (xs := C.support i) (w := hltx)
    simpa using this
  have hvy : (C.support i)[(C.support i).findIdx (fun z ↦ z == y)] = y := by
    have := List.findIdx_getElem (p := fun z ↦ z == y) (xs := C.support i) (w := hlty)
    simpa using this
  rw [← hvx, ← hvy]
  simp [hidx]

/-- Arity zero survives: there is exactly one nullary tuple, so constants and nullary relations
are checked **once** rather than accidentally skipped. -/
@[simp]
theorem finiteMaps_zero_arity_tuples (l : List ℕ) :
    (List.replicate 0 l).sections = [([] : List ℕ)] :=
  rfl

/-- The image list is duplicate-free exactly when the map is injective on the carrier. -/
theorem imageList_nodup_iff (i : ℕ) (g : ℕ → ℕ) :
    (C.imageList i g).Nodup ↔
      ∀ x ∈ B.domainAt i, ∀ y ∈ B.domainAt i, g x = g y → x = y := by
  rw [imageList, List.nodup_map_iff_inj_on (C.support_nodup i)]
  constructor
  · intro h x hx y hy hxy
    exact h x ((C.mem_support_iff_domainAt i x).2 hx) y
      ((C.mem_support_iff_domainAt i y).2 hy) hxy
  · intro h x hx y hy hxy
    exact h x ((C.mem_support_iff_domainAt i x).1 hx) y
      ((C.mem_support_iff_domainAt i y).1 hy) hxy

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
