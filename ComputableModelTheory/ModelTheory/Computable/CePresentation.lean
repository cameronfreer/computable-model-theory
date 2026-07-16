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
`ComputableStructureIn` and never claims a decidable domain: from a c.e. domain one
cannot computably totalize the operations, for the same reason the uniform Pullback
cannot produce decidable initial segments. `ComputableStructureIn` is exactly the all-ℕ
special case (`ComputableStructureIn.toCePresentation`, with `enum = id`).

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

/-- The rank of an element: the least enumeration position producing it, mapped through
nothing — `rankOf` diverges off the domain, halts on it. Composition with `rankIdx`
data is deferred to the rank-presentation construction. -/
noncomputable def rankOf : ℕ →. ℕ :=
  fun x ↦ Nat.rfind fun k ↦ Part.some (decide (P.enum k = x))

/-- The element rank search is partial recursive in the oracle. -/
theorem rankOf_recursiveIn : RecursiveIn O P.rankOf :=
  RecursiveIn.rfind_total
    (((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
      (P.enum_computableIn.comp ComputableIn.snd) ComputableIn.fst)

/-- The rank search halts exactly on the domain. -/
theorem rankOf_dom_iff (x : ℕ) : (P.rankOf x).Dom ↔ x ∈ P.domain := by
  have h := Nat.rfind_some_dom_iff (f := fun (y : ℕ) k ↦ decide (P.enum k = y)) (a := x)
  rw [rankOf]
  exact h.trans
    ⟨fun ⟨n, hn⟩ ↦ ⟨n, of_decide_eq_true hn⟩, fun ⟨n, hn⟩ ↦ ⟨n, decide_eq_true hn⟩⟩

end CePresentationIn

end FirstOrder.Language
