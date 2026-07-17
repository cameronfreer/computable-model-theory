/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.Structure

/-!
# C.e.-domain presentations (Level 1)

The Level-1 carrier notion for representations whose members need not have carrier all
of `ℕ` (issue #16): a **c.e. presentation** carries total-on-codes structure data, a
domain *enumeration*, domain-closure laws, and computability claimed **only on the
domain**, through partial evaluators. The type is deliberately distinct from
`ComputableStructureIn` and never claims a decidable domain: there is no computable
totalization *uniformly, or in general, from the c.e.-presentation data* — a particular
presentation's evaluators may well admit computable total extensions, but nothing
produces one from the data, for the same reason the uniform Pullback cannot produce
decidable initial segments. `ComputableStructureIn` is exactly the all-ℕ special case
(`ComputableStructureIn.toCePresentation`, with `enum = id`).

The enumeration-rank machinery for the Level-1 Pullback lives here: `freshAt` marks the
positions where the enumeration produces a new element; `rankIdx` is the partial
`O`-recursive map sending a rank to the position of its fresh element (total below the
number of distinct elements, undefined beyond — its domain is a **downward-closed** set
of ranks, the c.e. initial segment); `rankEnum` enumerates the domain by rank without
repetition; `rankOf` inverts it on the domain. Certificate-upgraded (Level-2)
presentations and the transported rank presentation build on these in follow-up work;
certificates are always supplied inputs, never recovered from the enumeration.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- A c.e.-domain presentation: total-on-codes structure data, a domain enumeration
(the domain is its range, nonempty by construction), domain-closure, and partial
evaluators for the symbol interpretations that are `O`-recursive and correct **on the
domain**. Off-domain, the structure data is unconstrained and the evaluators may
diverge or disagree — no theorem may rely on either. Deliberately distinct from
`ComputableStructureIn`: a c.e. presentation never claims a decidable domain or
total-code computability. -/
structure CePresentationIn (O : Set (ℕ →. ℕ)) (L : Language) [L.EffectiveLanguage] where
  /-- The structure data, total on codes; only its on-domain behavior is meaningful. -/
  str : L.Structure ℕ
  /-- The domain enumeration; the domain is `Set.range enum`. -/
  enum : ℕ → ℕ
  /-- The enumeration is computable in the oracle. -/
  enum_computableIn : ComputableIn O enum
  /-- The domain is closed under the interpretations of function symbols. -/
  domain_closed : ∀ (n : ℕ) (f : L.Functions n) (v : Fin n → ℕ),
    (∀ k, v k ∈ Set.range enum) → @Structure.funMap L ℕ str n f v ∈ Set.range enum
  /-- The partial function evaluator. -/
  funEval : FunctionApplicationData L ℕ →. ℕ
  /-- The function evaluator is partial recursive in the oracle. -/
  funEval_recursiveIn : RecursiveIn O funEval
  /-- On domain-valued arguments, the evaluator halts with the interpretation. -/
  funEval_correct : ∀ d : FunctionApplicationData L ℕ,
    (∀ k, d.args k ∈ Set.range enum) →
      @FunctionApplicationData.funMap L ℕ str d ∈ funEval d
  /-- The partial relation decider. -/
  relEval : RelationApplicationData L ℕ →. Bool
  /-- The relation decider is partial recursive in the oracle. -/
  relEval_recursiveIn : RecursiveIn O relEval
  /-- On domain-valued arguments, the decider halts, and its verdict is the truth
  value. Stated existentially to avoid a `Decidable` obligation on arbitrary structure
  data. -/
  relEval_correct : ∀ d : RelationApplicationData L ℕ,
    (∀ k, d.args k ∈ Set.range enum) →
      ∃ b ∈ relEval d, (b = true ↔ @RelationApplicationData.relMap L ℕ str d)

namespace CePresentationIn

variable (P : CePresentationIn O L)

/-- The domain of a c.e. presentation: the range of its enumeration. -/
def domain : Set ℕ :=
  Set.range P.enum

theorem enum_mem_domain (n : ℕ) : P.enum n ∈ P.domain :=
  ⟨n, rfl⟩

theorem domain_nonempty : P.domain.Nonempty :=
  ⟨P.enum 0, P.enum_mem_domain 0⟩

/-- Domain membership is r.e. in the oracle. -/
theorem mem_domain_rePredIn : REPredIn O fun x ↦ x ∈ P.domain :=
  (REPredIn.exists_nat_of_computablePredIn
    (p := fun x n ↦ P.enum n = x)
    ⟨fun _ ↦ instDecidableEqNat _ _,
      ((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂.comp
        (P.enum_computableIn.comp ComputableIn.snd) ComputableIn.fst)⟩).of_eq
    fun _ ↦ ⟨fun ⟨n, h⟩ ↦ ⟨n, h⟩, fun ⟨n, h⟩ ↦ ⟨n, h⟩⟩

end CePresentationIn

open Classical in
/-- The all-ℕ adapter: an ω-presented computable structure is a c.e. presentation with
the identity enumeration. The stable inclusion of the landed layer into the Level-1
notion; `toCePresentation_domain` is its first preservation theorem. (Noncomputable
only through the classical `decide` packaging of the relation verdict; the
computability content is the `relEval_recursiveIn` field.) -/
noncomputable def ComputableStructureIn.toCePresentation (S : ComputableStructureIn O L) :
    CePresentationIn O L where
  str := S.inst
  enum := id
  enum_computableIn := ComputableIn.id
  domain_closed := fun _ _ _ _ ↦ ⟨_, rfl⟩
  funEval := fun d ↦ Part.some (@FunctionApplicationData.funMap L ℕ S.inst d)
  funEval_recursiveIn :=
    (@IsComputableStructureIn.funMap_computableIn O L _ S.inst S.isComputable)
  funEval_correct := fun _ _ ↦ Part.mem_some _
  relEval := fun d ↦ Part.some (decide (@RelationApplicationData.relMap L ℕ S.inst d))
  relEval_recursiveIn :=
    ((@IsComputableStructureIn.relMap_computablePredIn O L _ S.inst
      S.isComputable).choose_spec.of_eq fun _ ↦ decide_eq_decide.2 Iff.rfl :
      ComputableIn O fun d : RelationApplicationData L ℕ ↦
        decide (@RelationApplicationData.relMap L ℕ S.inst d))
  relEval_correct := fun _ _ ↦
    ⟨_, Part.mem_some _, decide_eq_true_iff⟩

/-- Preservation: the all-ℕ adapter has full domain. -/
@[simp]
theorem ComputableStructureIn.toCePresentation_domain (S : ComputableStructureIn O L) :
    S.toCePresentation.domain = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ ⟨x, rfl⟩

namespace CePresentationIn

variable (P : CePresentationIn O L)

/-! ### Enumeration-rank machinery

`freshAt k` holds when position `k` enumerates an element not seen at any earlier
position. `rankIdx r` is the position of the `r`-th fresh element — partial, with
downward-closed domain: defined exactly for `r` below the number of distinct elements.
`rankEnum` and `rankOf` are the two directions of the enumeration-rank correspondence.
No cardinality is ever computed: on a finite domain `rankIdx` simply diverges past the
last rank, and nothing here can detect that divergence. -/

/-- Position `k` is fresh: it enumerates an element not enumerated earlier. -/
def freshAt (k : ℕ) : Bool :=
  ((List.range k).map P.enum).all fun y ↦ decide (y ≠ P.enum k)

theorem freshAt_iff (k : ℕ) : P.freshAt k = true ↔ ∀ j < k, P.enum j ≠ P.enum k := by
  simp only [freshAt, List.all_eq_true, List.mem_map, List.mem_range,
    decide_eq_true_eq]
  exact ⟨fun h j hj ↦ h _ ⟨j, hj, rfl⟩, fun h y ⟨j, hj, hy⟩ ↦ hy ▸ h j hj⟩

/-- Position `0` is always fresh. -/
@[simp]
theorem freshAt_zero : P.freshAt 0 = true := by
  simp [freshAt]

/-- Freshness is computable in the oracle. -/
theorem freshAt_computableIn : ComputableIn O P.freshAt := by
  have hmap : ComputableIn O fun k ↦ (List.range k).map P.enum :=
    ComputableIn.list_map (Primrec.list_range.to_comp.computableIn)
      ((P.enum_computableIn.comp ComputableIn.snd).to₂)
  have hne : ComputableIn O fun q : ℕ × (ℕ × Bool) ↦
      decide (q.2.1 ≠ P.enum q.1) :=
    ((Primrec.not.to_comp.computableIn (O := O)).comp
      (((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
        (ComputableIn.fst.comp ComputableIn.snd)
        (P.enum_computableIn.comp ComputableIn.fst))).of_eq
      fun _ ↦ decide_not.symm
  have hall : ComputableIn O fun k ↦
      ((List.range k).map P.enum).foldr
        (fun y b ↦ decide (y ≠ P.enum k) && b) true :=
    ComputableIn.list_foldr hmap (ComputableIn.const true)
      (((Primrec.and.to_comp.computableIn₂ (O := O)).comp hne
        (ComputableIn.snd.comp ComputableIn.snd)).to₂)
  have hbridge : ∀ (l : List ℕ) (x : ℕ),
      l.foldr (fun y b ↦ decide (y ≠ x) && b) true = l.all fun y ↦ decide (y ≠ x) := by
    intro l x
    induction l with
    | nil => rfl
    | cons a t ih => simp only [List.foldr_cons, List.all_cons, ih]
  exact hall.of_eq fun k ↦ hbridge _ _

/-- The position of the `r`-th fresh element: `0` at rank `0` (position `0` is always
fresh), and at rank `r + 1` the least fresh position beyond the rank-`r` position.
Partial: undefined exactly beyond the number of distinct enumerated elements — nothing
here can detect that divergence, matching the Pullback obstruction. -/
noncomputable def rankIdx : ℕ →. ℕ :=
  fun r ↦ Nat.rec (motive := fun _ ↦ Part ℕ)
    (Part.some 0)
    (fun _ ih ↦ ih.bind fun i ↦
      Nat.rfind fun k ↦ Part.some (decide (i < k) && P.freshAt k))
    r

@[simp]
theorem rankIdx_zero : P.rankIdx 0 = Part.some 0 :=
  rfl

theorem rankIdx_succ (r : ℕ) :
    P.rankIdx (r + 1) = (P.rankIdx r).bind fun i ↦
      Nat.rfind fun k ↦ Part.some (decide (i < k) && P.freshAt k) :=
  rfl

/-- The rank positions are partial recursive in the oracle. -/
theorem rankIdx_recursiveIn : RecursiveIn O P.rankIdx := by
  have hstep : ComputableIn₂ O fun (q : ℕ × (ℕ × ℕ)) (k : ℕ) ↦
      decide (q.2.2 < k) && P.freshAt k :=
    (Primrec.and.to_comp.computableIn₂ (O := O)).comp
      (((Primrec.nat_lt.decide.to_comp.computableIn₂ (O := O)).comp
        (ComputableIn.snd.comp (ComputableIn.snd.comp ComputableIn.fst))
        ComputableIn.snd))
      (P.freshAt_computableIn.comp ComputableIn.snd)
  have hrec : RecursiveIn O fun r : ℕ ↦
      Nat.rec (motive := fun _ ↦ Part ℕ) (Part.some 0)
        (fun _ ih ↦ ih.bind fun i ↦
          Nat.rfind fun k ↦ Part.some (decide (i < k) && P.freshAt k)) r :=
    (RecursiveIn.nat_rec (f := fun r : ℕ ↦ r)
      (g := fun _ : ℕ ↦ (Part.some 0 : Part ℕ))
      (h := fun _ p ↦ Nat.rfind fun k ↦ Part.some (decide (p.2 < k) && P.freshAt k))
      ComputableIn.id (ComputableIn.const 0)
      (RecursiveIn.rfind_total hstep).to₂).of_eq fun r ↦ by
        induction r with
        | zero => rfl
        | succ n ih => simp only [ih]
  exact hrec

/-- The rank domain is downward closed: rank `r + 1` defined forces rank `r` defined.
This is the initial-segment shape of the Level-1 Pullback domain. -/
theorem rankIdx_dom_of_succ (r : ℕ) (h : (P.rankIdx (r + 1)).Dom) :
    (P.rankIdx r).Dom := by
  rw [rankIdx_succ] at h
  exact h.1

/-- The rank domain is a downward-closed set of ranks. -/
theorem rankIdx_dom_mono {r s : ℕ} (hrs : r ≤ s) (h : (P.rankIdx s).Dom) :
    (P.rankIdx r).Dom := by
  induction s with
  | zero => exact (Nat.le_zero.1 hrs) ▸ h
  | succ n ih =>
    rcases Nat.lt_or_ge r (n + 1) with hlt | hge
    · exact ih (Nat.lt_succ_iff.1 hlt) (P.rankIdx_dom_of_succ n h)
    · exact (Nat.le_antisymm hrs hge) ▸ h

/-- A defined rank position is fresh. -/
theorem freshAt_of_mem_rankIdx {r i : ℕ} (h : i ∈ P.rankIdx r) :
    P.freshAt i = true := by
  cases r with
  | zero => simp_all [rankIdx_zero, Part.mem_some_iff]
  | succ n =>
    rw [rankIdx_succ] at h
    obtain ⟨j, -, hfind⟩ := Part.mem_bind_iff.1 h
    have hand : (decide (j < i) && P.freshAt i) = true :=
      (Part.mem_some_iff.1 (Nat.rfind_spec hfind)).symm
    exact ((Bool.and_eq_true _ _).mp hand).2

/-- Rank positions are strictly increasing where defined. -/
theorem rankIdx_lt_of_mem {r i j : ℕ} (hi : i ∈ P.rankIdx r)
    (hj : j ∈ P.rankIdx (r + 1)) : i < j := by
  rw [rankIdx_succ] at hj
  obtain ⟨i', hi', hfind⟩ := Part.mem_bind_iff.1 hj
  obtain rfl : i = i' := Part.mem_unique hi hi'
  have hand : (decide (i < j) && P.freshAt j) = true :=
    (Part.mem_some_iff.1 (Nat.rfind_spec hfind)).symm
  exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hand).1

/-- The enumeration of the domain by rank, without repetition. -/
noncomputable def rankEnum : ℕ →. ℕ :=
  fun r ↦ (P.rankIdx r).map P.enum

/-- The rank enumeration is partial recursive in the oracle. -/
theorem rankEnum_recursiveIn : RecursiveIn O P.rankEnum :=
  RecursiveIn.map P.rankIdx_recursiveIn
    ((P.enum_computableIn.comp ComputableIn.snd).to₂)

/-- Rank-enumerated values lie in the domain. -/
theorem mem_domain_of_mem_rankEnum {r x : ℕ} (h : x ∈ P.rankEnum r) :
    x ∈ P.domain := by
  obtain ⟨i, -, rfl⟩ := (Part.mem_map_iff _).1 h
  exact P.enum_mem_domain i

/-- The first enumeration position producing an element: partial, diverging off the
domain, halting on it. The position it returns is fresh; composing with the fresh count
gives the element's rank (`rankOf`). -/
noncomputable def firstIdxOf : ℕ →. ℕ :=
  fun x ↦ Nat.rfind fun k ↦ Part.some (decide (P.enum k = x))

/-- The first-position search is partial recursive in the oracle. -/
theorem firstIdxOf_recursiveIn : RecursiveIn O P.firstIdxOf :=
  RecursiveIn.rfind_total
    (((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
      (P.enum_computableIn.comp ComputableIn.snd) ComputableIn.fst)

/-- The first-position search halts exactly on the domain. -/
theorem firstIdxOf_dom_iff (x : ℕ) : (P.firstIdxOf x).Dom ↔ x ∈ P.domain := by
  have h := Nat.rfind_some_dom_iff (f := fun (y : ℕ) k ↦ decide (P.enum k = y)) (a := x)
  rw [firstIdxOf]
  exact h.trans
    ⟨fun ⟨n, hn⟩ ↦ ⟨n, of_decide_eq_true hn⟩, fun ⟨n, hn⟩ ↦ ⟨n, decide_eq_true hn⟩⟩

/-- Membership specification of the first-position search. -/
theorem mem_firstIdxOf_iff {x i : ℕ} :
    i ∈ P.firstIdxOf x ↔ P.enum i = x ∧ ∀ j < i, P.enum j ≠ x := by
  rw [firstIdxOf, Nat.mem_rfind]
  constructor
  · rintro ⟨hspec, hmin⟩
    rw [Part.mem_some_iff] at hspec
    refine ⟨of_decide_eq_true hspec.symm, fun j hj he ↦ ?_⟩
    have := hmin hj
    rw [Part.mem_some_iff] at this
    exact absurd (decide_eq_true he) (by rw [← this]; exact fun h ↦ Bool.noConfusion h)
  · rintro ⟨he, hmin⟩
    exact ⟨Part.mem_some_iff.2 (decide_eq_true he).symm,
      fun {m} hm ↦ Part.mem_some_iff.2 (decide_eq_false (hmin m hm)).symm⟩

/-- First positions are fresh. -/
theorem freshAt_of_mem_firstIdxOf {x i : ℕ} (h : i ∈ P.firstIdxOf x) :
    P.freshAt i = true := by
  obtain ⟨he, hmin⟩ := P.mem_firstIdxOf_iff.1 h
  exact (P.freshAt_iff i).2 fun j hj hej ↦ hmin j hj (hej.trans he)

/-! ### First occurrences and rank counting

`firstOcc k` is the first position enumerating the same element as position `k` — total,
by bounded least search, the least-representative device of effective union
constructions. `countFreshBelow k` counts the fresh positions below `k`; the
characterization `mem_rankIdx_iff` identifies `rankIdx r` as the fresh position with
exactly `r` fresh predecessors, from which the enumeration-rank inverse laws follow. -/

/-- The first position enumerating the same element as position `k`. Total: bounded by
`k` itself. -/
def firstOcc (k : ℕ) : ℕ :=
  Nat.find (⟨k, rfl⟩ : ∃ j, P.enum j = P.enum k)

theorem enum_firstOcc (k : ℕ) : P.enum (P.firstOcc k) = P.enum k :=
  Nat.find_spec (⟨k, rfl⟩ : ∃ j, P.enum j = P.enum k)

theorem firstOcc_le (k : ℕ) : P.firstOcc k ≤ k :=
  Nat.find_le rfl

theorem enum_ne_of_lt_firstOcc {k j : ℕ} (hj : j < P.firstOcc k) :
    P.enum j ≠ P.enum k :=
  Nat.find_min (⟨k, rfl⟩ : ∃ j, P.enum j = P.enum k) hj

/-- First occurrences are fresh. -/
theorem freshAt_firstOcc (k : ℕ) : P.freshAt (P.firstOcc k) = true :=
  (P.freshAt_iff _).2 fun _ hj he ↦
    P.enum_ne_of_lt_firstOcc hj (he.trans (P.enum_firstOcc k))

/-- Fresh positions are their own first occurrence. -/
theorem firstOcc_eq_self_of_fresh {k : ℕ} (h : P.freshAt k = true) :
    P.firstOcc k = k := by
  rcases Nat.lt_or_ge (P.firstOcc k) k with hlt | hge
  · exact absurd (P.enum_firstOcc k) ((P.freshAt_iff k).1 h _ hlt)
  · exact Nat.le_antisymm (P.firstOcc_le k) hge

/-- First occurrence is computable in the oracle. -/
theorem firstOcc_computableIn : ComputableIn O P.firstOcc := by
  have hB : ∀ k, ∃ j, (fun j ↦ decide (P.enum j = P.enum k)) j = true :=
    fun k ↦ ⟨k, decide_eq_true rfl⟩
  have hfind : ComputableIn O fun k ↦ Nat.find (hB k) :=
    ComputableIn.find
      ((((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
        (P.enum_computableIn.comp ComputableIn.snd)
        (P.enum_computableIn.comp ComputableIn.fst)).to₂)
      hB
  refine hfind.of_eq fun k ↦ Nat.le_antisymm ?_ ?_
  · exact Nat.find_le (decide_eq_true (P.enum_firstOcc k))
  · exact Nat.find_le (of_decide_eq_true (Nat.find_spec (hB k)))

/-- The number of fresh positions below `k`. -/
def countFreshBelow (k : ℕ) : ℕ :=
  (List.range k).foldr (fun j acc ↦ bif P.freshAt j then acc + 1 else acc) 0

@[simp]
theorem countFreshBelow_zero : P.countFreshBelow 0 = 0 :=
  rfl

private theorem foldr_count_shift (g : ℕ → Bool) (l : List ℕ) (c : ℕ) :
    l.foldr (fun j acc ↦ bif g j then acc + 1 else acc) c =
      l.foldr (fun j acc ↦ bif g j then acc + 1 else acc) 0 + c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases h : g a
    · simpa [h] using ih
    · simp only [List.foldr_cons, h, cond_true, ih]
      omega

theorem countFreshBelow_succ (k : ℕ) :
    P.countFreshBelow (k + 1) =
      P.countFreshBelow k + (bif P.freshAt k then 1 else 0) := by
  rw [countFreshBelow, List.range_succ, List.foldr_append]
  rw [show List.foldr (fun j acc ↦ bif P.freshAt j then acc + 1 else acc) 0 [k]
      = (bif P.freshAt k then 1 else 0) from by cases h : P.freshAt k <;> simp [h]]
  exact foldr_count_shift P.freshAt (List.range k) _

theorem countFreshBelow_mono {j k : ℕ} (h : j ≤ k) :
    P.countFreshBelow j ≤ P.countFreshBelow k := by
  induction k with
  | zero => exact (Nat.le_zero.1 h) ▸ le_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge j (n + 1) with hlt | hge
    · exact le_trans (ih (Nat.lt_succ_iff.1 hlt))
        (by rw [P.countFreshBelow_succ n]; omega)
    · exact (Nat.le_antisymm h hge) ▸ le_rfl

/-- Counting is constant across a fresh-free interval. -/
theorem countFreshBelow_eq_of_no_fresh {j k : ℕ} (hjk : j ≤ k)
    (hno : ∀ m, j ≤ m → m < k → P.freshAt m = false) :
    P.countFreshBelow k = P.countFreshBelow j := by
  induction k with
  | zero => rw [Nat.le_zero.1 hjk]
  | succ n ih =>
    rcases Nat.lt_or_ge j (n + 1) with hlt | hge
    · have hj := Nat.lt_succ_iff.1 hlt
      rw [P.countFreshBelow_succ n, hno n hj (Nat.lt_succ_self n),
        ih hj fun m hm hmn ↦ hno m hm (Nat.lt_succ_of_lt hmn)]
      rfl
    · rw [Nat.le_antisymm hjk hge]

/-- Counting is computable in the oracle. -/
theorem countFreshBelow_computableIn : ComputableIn O P.countFreshBelow := by
  have hstep : ComputableIn O fun q : ℕ × (ℕ × ℕ) ↦
      bif P.freshAt q.2.1 then q.2.2 + 1 else q.2.2 :=
    ComputableIn.cond
      (P.freshAt_computableIn.comp (ComputableIn.fst.comp ComputableIn.snd))
      ((Primrec.succ.to_comp.computableIn (O := O)).comp
        (ComputableIn.snd.comp ComputableIn.snd))
      (ComputableIn.snd.comp ComputableIn.snd)
  exact ComputableIn.list_foldr
    (Primrec.list_range.to_comp.computableIn)
    (ComputableIn.const 0) hstep.to₂

/-- The characterization of rank positions: `rankIdx r` is exactly the fresh position
with `r` fresh predecessors. -/
theorem mem_rankIdx_iff {r i : ℕ} :
    i ∈ P.rankIdx r ↔ P.freshAt i = true ∧ P.countFreshBelow i = r := by
  induction r generalizing i with
  | zero =>
    rw [rankIdx_zero, Part.mem_some_iff]
    constructor
    · rintro rfl
      exact ⟨P.freshAt_zero, rfl⟩
    · rintro ⟨hf, hc⟩
      by_contra hne
      have h0 : 0 < i := Nat.pos_of_ne_zero hne
      have : 1 ≤ P.countFreshBelow i := by
        calc 1 = P.countFreshBelow 1 := by
              rw [P.countFreshBelow_succ 0, P.freshAt_zero]; rfl
          _ ≤ P.countFreshBelow i := P.countFreshBelow_mono h0
      omega
  | succ n ih =>
    rw [rankIdx_succ]
    constructor
    · intro h
      obtain ⟨j, hj, hfind⟩ := Part.mem_bind_iff.1 h
      obtain ⟨hjf, hjc⟩ := ih.1 hj
      have hand : (decide (j < i) && P.freshAt i) = true :=
        (Part.mem_some_iff.1 (Nat.rfind_spec hfind)).symm
      have hji : j < i := of_decide_eq_true ((Bool.and_eq_true _ _).mp hand).1
      have hif : P.freshAt i = true := ((Bool.and_eq_true _ _).mp hand).2
      have hno : ∀ m, j + 1 ≤ m → m < i → P.freshAt m = false := by
        intro m hm hmi
        have hmin := Nat.rfind_min hfind hmi
        rw [Part.mem_some_iff] at hmin
        have hfalse : (decide (j < m) && P.freshAt m) = false := hmin.symm
        rcases Bool.and_eq_false_iff.1 hfalse with hlt | hfr
        · exact absurd hlt (by simp [Nat.lt_of_succ_le hm])
        · exact hfr
      refine ⟨hif, ?_⟩
      rw [P.countFreshBelow_eq_of_no_fresh (Nat.succ_le_of_lt hji) hno,
        P.countFreshBelow_succ j, hjf, hjc]
      rfl
    · rintro ⟨hif, hic⟩
      -- The greatest fresh position below `i` has count `n`; it is `rankIdx n` by the
      -- inductive hypothesis, and `i` is then the least fresh position beyond it.
      have hi0 : 0 < i := by
        rcases Nat.eq_zero_or_pos i with h0 | h
        · rw [h0] at hic
          simp at hic
        · exact h
      set j := Nat.findGreatest (fun j ↦ P.freshAt j = true) (i - 1) with hjdef
      have hji : j < i :=
        Nat.lt_of_le_of_lt (Nat.findGreatest_le _) (by omega)
      have hjf : P.freshAt j = true :=
        Nat.findGreatest_spec (P := fun m ↦ P.freshAt m = true)
          (Nat.zero_le (i - 1)) P.freshAt_zero
      have hjno : ∀ m, j < m → m < i → P.freshAt m = false := by
        intro m hjm hmi
        have hng : ¬ P.freshAt m = true :=
          Nat.findGreatest_is_greatest hjm (by omega)
        cases h : P.freshAt m
        · rfl
        · exact absurd h hng
      have hjc : P.countFreshBelow j = n := by
        have hstep : P.countFreshBelow i = P.countFreshBelow j + 1 := by
          rw [P.countFreshBelow_eq_of_no_fresh (Nat.succ_le_of_lt hji)
              (fun m hm hmi ↦ hjno m (Nat.lt_of_succ_le hm) hmi),
            P.countFreshBelow_succ j, hjf]
          rfl
        omega
      have hjmem : j ∈ P.rankIdx n := ih.2 ⟨hjf, hjc⟩
      refine Part.mem_bind_iff.2 ⟨j, hjmem, ?_⟩
      rw [Nat.mem_rfind]
      constructor
      · rw [Part.mem_some_iff]
        simp [hji, hif]
      · intro m hmi
        rw [Part.mem_some_iff]
        rcases Nat.lt_or_ge j m with hjm | hmj
        · simp [hjno m hjm hmi]
        · simp [Nat.not_lt_of_ge hmj]

/-! ### The enumeration-rank correspondence -/

/-- The rank of the element at position `k`: the fresh count below its first
occurrence. Total and computable — the least-representative coding of effective union
constructions. Its range is exactly the rank domain. -/
def posRank (k : ℕ) : ℕ :=
  P.countFreshBelow (P.firstOcc k)

theorem posRank_computableIn : ComputableIn O P.posRank :=
  P.countFreshBelow_computableIn.comp P.firstOcc_computableIn

/-- The first occurrence of any position realizes its rank. -/
theorem firstOcc_mem_rankIdx_posRank (k : ℕ) :
    P.firstOcc k ∈ P.rankIdx (P.posRank k) :=
  P.mem_rankIdx_iff.2 ⟨P.freshAt_firstOcc k, rfl⟩

/-- `posRank` recovers the rank of any defined rank position. -/
theorem posRank_of_mem_rankIdx {r i : ℕ} (h : i ∈ P.rankIdx r) :
    P.posRank i = r := by
  obtain ⟨hf, hc⟩ := P.mem_rankIdx_iff.1 h
  rw [posRank, P.firstOcc_eq_self_of_fresh hf, hc]

/-- Gate: the rank domain is exactly the range of the total computable `posRank` —
in particular c.e. (and downward closed, by `rankIdx_dom_mono`). -/
theorem rankIdx_dom_iff_mem_range_posRank (r : ℕ) :
    (P.rankIdx r).Dom ↔ r ∈ Set.range P.posRank := by
  constructor
  · intro h
    exact ⟨(P.rankIdx r).get h, P.posRank_of_mem_rankIdx (Part.get_mem h)⟩
  · rintro ⟨k, rfl⟩
    exact Part.dom_iff_mem.2 ⟨P.firstOcc k, P.firstOcc_mem_rankIdx_posRank k⟩

/-- The rank of an element: the fresh count below its first enumeration position.
Partial: halts exactly on the domain. The inverse of `rankEnum` on their respective
domains. -/
noncomputable def rankOf : ℕ →. ℕ :=
  fun x ↦ (P.firstIdxOf x).map P.countFreshBelow

theorem rankOf_recursiveIn : RecursiveIn O P.rankOf :=
  RecursiveIn.map P.firstIdxOf_recursiveIn
    ((P.countFreshBelow_computableIn.comp ComputableIn.snd).to₂)

/-- The rank search halts exactly on the domain. -/
theorem rankOf_dom_iff (x : ℕ) : (P.rankOf x).Dom ↔ x ∈ P.domain := by
  rw [rankOf]
  exact Part.dom_iff_mem.trans
    ⟨fun ⟨r, hr⟩ ↦ by
      obtain ⟨i, hi, -⟩ := (Part.mem_map_iff _).1 hr
      exact (P.firstIdxOf_dom_iff x).1 (Part.dom_iff_mem.2 ⟨i, hi⟩),
      fun hx ↦ by
        obtain ⟨i, hi⟩ := Part.dom_iff_mem.1 ((P.firstIdxOf_dom_iff x).2 hx)
        exact ⟨P.countFreshBelow i, (Part.mem_map_iff _).2 ⟨i, hi, rfl⟩⟩⟩

/-- Gate (inverse, one direction): `rankOf` inverts `rankEnum` on the rank domain. -/
theorem rankOf_rankEnum {r x : ℕ} (h : x ∈ P.rankEnum r) : r ∈ P.rankOf x := by
  obtain ⟨i, hi, rfl⟩ := (Part.mem_map_iff _).1 h
  obtain ⟨hf, hc⟩ := P.mem_rankIdx_iff.1 hi
  have hfirst : i ∈ P.firstIdxOf (P.enum i) :=
    P.mem_firstIdxOf_iff.2 ⟨rfl, fun j hj ↦ (P.freshAt_iff i).1 hf j hj⟩
  exact (Part.mem_map_iff _).2 ⟨i, hfirst, hc⟩

/-- Gate (inverse, other direction): `rankEnum` inverts `rankOf` on the domain. -/
theorem rankEnum_rankOf {x : ℕ} (hx : x ∈ P.domain) :
    ∃ r ∈ P.rankOf x, x ∈ P.rankEnum r := by
  obtain ⟨i, hi⟩ := Part.dom_iff_mem.1 ((P.firstIdxOf_dom_iff x).2 hx)
  obtain ⟨he, -⟩ := P.mem_firstIdxOf_iff.1 hi
  refine ⟨P.countFreshBelow i, (Part.mem_map_iff _).2 ⟨i, hi, rfl⟩, ?_⟩
  have hmem : i ∈ P.rankIdx (P.countFreshBelow i) :=
    P.mem_rankIdx_iff.2 ⟨P.freshAt_of_mem_firstIdxOf hi, rfl⟩
  exact (Part.mem_map_iff _).2 ⟨i, hmem, he⟩

end CePresentationIn

end FirstOrder.Language
