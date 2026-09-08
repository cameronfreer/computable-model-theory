/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Data.Sum.Order
import ComputableModelTheory.Computability.OracleCode
import ComputableModelTheory.Computability.OraclePred
import ComputableModelTheory.Computability.Reduction

/-!
# Ordinals recursive in one oracle, and the least one that is not

For a fixed partial oracle `X : ℕ →. ℕ`, a **recursive well-order presentation** (`RecWellOrder X`)
is an `{X}`-computable subset of `ℕ` together with an `{X}`-computable strict relation on `ℕ` that
well-orders that subset. Its order type lives in `Ordinal.{0}`; `RecOrdinals X` is the set of order
types so presented, and `omegaOneOf X` is the least ordinal **not** presented — the oracle-relative
`ω₁^X`.

## What is proved

In the dependency order the theorems actually follow:

* **A** `RecWellOrder.type_lt_omega_one`: every presented ordinal is below `ω₁`, because the domain
  is a subtype of `ℕ`.
* **B** `natOrder`, `finOrder`, `emptyOrder`: `ω`, every finite ordinal, and `0` are presented, by
  actual computable domains and relations.
* **C** `RecWellOrder.restrict`, `mem_recOrdinals_of_lt`: presented ordinals are downward closed —
  restrict a presentation to the initial segment below an element chosen **classically** by the
  order-type theorem. No ordinal comparison is decided and no element is computed from an ordinal.
* **D** `RecWellOrder.succ`, `succ_mem_recOrdinals`: presented ordinals are successor closed — shift
  the old domain to `n + 1` and reserve `0` for a new greatest element, so nothing assumes an unused
  natural number exists.
* **E** `countable_recOrdinals`: the presented ordinals form a countable set. Each presentation's
  domain and relation are the interpretations of program codes (`OracleCode`, by completeness), so
  `RecOrdinals X` lies in the range of `codeType X` over the countable type of code pairs. This
  counts *code presentations*; no effective injection of order types into codes is claimed.
* **F** `compl_recOrdinals_nonempty`, `omegaOneOf_notMem`: the complement is nonempty (it contains
  `ω₁`, by A), so the infimum defining `omegaOneOf X` is attained and is not presented.
* **G** `lt_omegaOneOf_iff`: `α < omegaOneOf X ↔ α ∈ RecOrdinals X` — leastness plus downward
  closure, with nonmembership at the endpoint.
* **H** `omegaOneOf_lt_omega_one`: `omegaOneOf X < ω₁`. Countably many code types, each below the
  regular cardinal `ℵ₁`, have supremum below `ω₁`; the successor of that supremum is not presented,
  so it bounds the infimum.
* **I** `omega0_lt_omegaOneOf`, `succ_lt_omegaOneOf`: `ω < omegaOneOf X`, and no presented ordinal
  is greatest.
* **J** `RecWellOrder.transport`, `recOrdinals_mono`: Turing monotonicity, by relabelling the two
  computability proofs along `RecursiveIn.subst`; the domain, relation, and type are unchanged.
* **K** `omegaOneOf_mono`, `omegaOneOf_eq_of_equiv`: monotonicity and Turing-equivalence invariance.

## What is not proved

`omegaOneOf X` is defined by an infimum over a complement, and every statement about it is
classical. There is no `X`-computable enumeration of the presented order types, no procedure
deciding whether a code pair presents a well-order, and no claim about admissibility, effective
boundedness, or Kripke–Platek. The oracle is a single partial function; nothing is asserted for an
arbitrary set of oracles. The bound `max (omegaOneOf X) (omegaOneOf Y) ≤ omegaOneOf (X ⊕ Y)` for
joins is not stated here; a join is a separate prerequisite when needed.
-/

open Encodable Ordinal Cardinal

/-! ### Recursive well-order presentations -/

/-- A recursive well-order presentation relative to the oracle `X`: an `{X}`-computable domain in
`ℕ` and an `{X}`-computable strict relation on `ℕ` that well-orders the domain. The relation's
values off the domain are irrelevant to the order type. -/
structure RecWellOrder (X : ℕ →. ℕ) where
  /-- The field of the order, an arbitrary `{X}`-computable subset of `ℕ`. -/
  domain : Set ℕ
  /-- Membership in the domain is decidable relative to `X`. -/
  domain_computable : ComputablePredIn {X} (· ∈ domain)
  /-- The strict order relation, on ambient naturals. -/
  rel : ℕ → ℕ → Prop
  /-- The relation is decidable relative to `X`, on ambient pairs. -/
  rel_computable : ComputableRelIn {X} rel
  /-- The relation well-orders the domain. -/
  isWellOrder : IsWellOrder domain (Subrel rel (· ∈ domain))

namespace RecWellOrder

variable {X : ℕ →. ℕ} (W : RecWellOrder X)

instance : IsWellOrder W.domain (Subrel W.rel (· ∈ W.domain)) := W.isWellOrder

/-- The order type of the presentation. -/
noncomputable def type : Ordinal.{0} :=
  Ordinal.type (Subrel W.rel (· ∈ W.domain))

/-- **Any well-order on a subset of `ℕ` has type below `ω₁`**: its domain is countable. -/
theorem type_subtype_lt_omega_one {s : Set ℕ} (r : s → s → Prop) [IsWellOrder s r] :
    Ordinal.type r < ω_ 1 := by
  rw [← Cardinal.ord_aleph, Cardinal.lt_ord, Ordinal.card_type, Cardinal.lt_aleph_one_iff]
  exact Cardinal.mk_le_aleph0

/-- **(A)** Every presented ordinal is below `ω₁`. -/
theorem type_lt_omega_one : W.type < ω_ 1 :=
  type_subtype_lt_omega_one _

/-! ### Restriction to an initial segment -/

/-- A subrelation of the presentation's order on a subset of its domain is a well-order. -/
theorem isWellOrder_subrel_of_subset {p : ℕ → Prop} (hp : ∀ n, p n → n ∈ W.domain) :
    IsWellOrder (Subtype p) (Subrel W.rel p) :=
  RelEmbedding.isWellOrder
    (⟨⟨fun x ↦ ⟨x.1, hp x.1 x.2⟩, fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h)⟩, Iff.rfl⟩ :
      Subrel W.rel p ↪r Subrel W.rel (· ∈ W.domain))

/-- The presentation restricted to the elements strictly below `a`. The restricted domain is
computable because both conjuncts are; the relation is unchanged. -/
def restrict (a : ℕ) : RecWellOrder X where
  domain := {n | n ∈ W.domain ∧ W.rel n a}
  domain_computable :=
    (W.domain_computable.and
      (W.rel_computable.comp (ComputableIn.id.pair (ComputableIn.const a)))).of_eq
      fun _ ↦ Iff.rfl
  rel := W.rel
  rel_computable := W.rel_computable
  isWellOrder := W.isWellOrder_subrel_of_subset fun _ h ↦ h.1

/-- The restriction's order is the order-type theorem's initial segment below `a`. -/
theorem type_restrict {a : ℕ} (ha : a ∈ W.domain) :
    (W.restrict a).type = typein (Subrel W.rel (· ∈ W.domain)) ⟨a, ha⟩ := by
  rw [← type_subrel]
  exact RelIso.ordinalType_congr
    ⟨{ toFun := fun x ↦ ⟨⟨x.1, x.2.1⟩, x.2.2⟩
       invFun := fun y ↦ ⟨y.1.1, y.1.2, y.2⟩
       left_inv := fun _ ↦ rfl
       right_inv := fun _ ↦ rfl }, Iff.rfl⟩

/-- **(C)** Every ordinal below a presented one is the type of a restriction. The element `a` is
obtained classically from the order-type theorem, not computed. -/
theorem exists_type_restrict_eq {β : Ordinal.{0}} (h : β < W.type) :
    ∃ a ∈ W.domain, (W.restrict a).type = β := by
  let x := enum (Subrel W.rel (· ∈ W.domain)) ⟨β, h⟩
  refine ⟨x.1, x.2, ?_⟩
  rw [W.type_restrict x.2]
  exact typein_enum _ h

/-! ### Successor -/

/-- The successor domain: `0`, and `n + 1` for `n` in the old domain. -/
def succDomain : Set ℕ := {m | m = 0 ∨ (0 < m ∧ m - 1 ∈ W.domain)}

/-- The successor relation: old elements shifted by one and compared as before, all of them below
the new element `0`. -/
def succRel (a b : ℕ) : Prop :=
  (0 < a ∧ 0 < b ∧ W.rel (a - 1) (b - 1)) ∨ (0 < a ∧ b = 0)

/-- The successor domain, as `W.domain ⊕ Unit`. -/
def succEquiv : W.domain ⊕ Unit ≃ W.succDomain where
  toFun
    | Sum.inl x => ⟨x.1 + 1, Or.inr ⟨Nat.succ_pos _, by simp [x.2]⟩⟩
    | Sum.inr _ => ⟨0, Or.inl rfl⟩
  invFun y :=
    if h : y.1 = 0 then Sum.inr () else Sum.inl ⟨y.1 - 1, (y.2.resolve_left h).2⟩
  left_inv
    | Sum.inl x => by simp
    | Sum.inr _ => by simp
  right_inv y := by
    obtain ⟨m, hm⟩ := y
    by_cases h : m = 0
    · subst h; simp
    · simp only [h, ↓reduceDIte]
      exact Subtype.ext (by simp only; omega)

/-- The successor order is the lexicographic sum of the old order and one point. -/
def succRelIso :
    Sum.Lex (Subrel W.rel (· ∈ W.domain)) (@emptyRelation Unit) ≃r
      Subrel W.succRel (· ∈ W.succDomain) where
  toEquiv := W.succEquiv
  map_rel_iff' := by
    rintro (x | ⟨⟩) (y | ⟨⟩)
    · simp [succEquiv, Subrel, succRel]
    · simp [succEquiv, Subrel, succRel, Sum.Lex.sep]
    · simp [succEquiv, Subrel, succRel]
    · simp [succEquiv, Subrel, succRel, emptyRelation]

instance isWellOrder_succ : IsWellOrder W.succDomain (Subrel W.succRel (· ∈ W.succDomain)) :=
  W.succRelIso.symm.toRelEmbedding.isWellOrder

/-- The successor domain is computable: `m = 0`, or `0 < m` and `m - 1` in the old domain. -/
private theorem succDomain_computable : ComputablePredIn {X} (· ∈ W.succDomain) := by
  have hz : ComputablePredIn {X} fun m : ℕ ↦ m = 0 :=
    ComputableIn.computablePredIn
      (((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := {X})).comp ComputableIn.id
        (ComputableIn.const 0))
  have hpos : ComputablePredIn {X} fun m : ℕ ↦ 0 < m :=
    ComputableIn.computablePredIn
      ((Primrec.nat_lt.decide.to_comp.computableIn₂ (O := {X})).comp (ComputableIn.const 0)
        ComputableIn.id)
  have hpred : ComputablePredIn {X} fun m : ℕ ↦ m - 1 ∈ W.domain :=
    W.domain_computable.comp
      ((Primrec.nat_sub.to_comp.computableIn₂ (O := {X})).comp ComputableIn.id
        (ComputableIn.const 1))
  exact (hz.or (hpos.and hpred)).of_eq fun _ ↦ Iff.rfl

/-- The successor relation is computable, by Boolean closure over the old relation. -/
private theorem succRel_computable : ComputableRelIn {X} W.succRel := by
  have hpos : ComputablePredIn {X} fun m : ℕ ↦ 0 < m :=
    ComputableIn.computablePredIn
      ((Primrec.nat_lt.decide.to_comp.computableIn₂ (O := {X})).comp (ComputableIn.const 0)
        ComputableIn.id)
  have hz : ComputablePredIn {X} fun m : ℕ ↦ m = 0 :=
    ComputableIn.computablePredIn
      (((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := {X})).comp ComputableIn.id
        (ComputableIn.const 0))
  have hpred : ComputableIn {X} fun m : ℕ ↦ m - 1 :=
    (Primrec.nat_sub.to_comp.computableIn₂ (O := {X})).comp ComputableIn.id (ComputableIn.const 1)
  have hrel : ComputablePredIn {X} fun x : ℕ × ℕ ↦ W.rel (x.1 - 1) (x.2 - 1) :=
    W.rel_computable.comp ((hpred.comp ComputableIn.fst).pair (hpred.comp ComputableIn.snd))
  exact (((hpos.comp ComputableIn.fst).and ((hpos.comp ComputableIn.snd).and hrel)).or
    ((hpos.comp ComputableIn.fst).and (hz.comp ComputableIn.snd))).of_eq fun _ ↦ Iff.rfl

/-- **(D)** The successor presentation: the old domain shifted to `n + 1`, with `0` as the new
greatest element. The shift is what makes this work when the old domain is all of `ℕ`. -/
def succ : RecWellOrder X where
  domain := W.succDomain
  domain_computable := W.succDomain_computable
  rel := W.succRel
  rel_computable := W.succRel_computable
  isWellOrder := W.isWellOrder_succ

/-- The successor presentation has type one more than the original. -/
theorem type_succ : W.succ.type = W.type + 1 := by
  change Ordinal.type (Subrel W.succRel (· ∈ W.succDomain)) = _
  rw [← W.succRelIso.ordinalType_congr, type_sum_lex, type_unit]
  rfl

/-! ### The basic presentations -/

/-- **(B)** `ℕ` under `<`: type `ω`. -/
def natOrder (X : ℕ →. ℕ) : RecWellOrder X where
  domain := Set.univ
  domain_computable := (ComputablePredIn.const True).of_eq fun _ ↦ by simp
  rel := (· < ·)
  rel_computable := ComputableIn.computablePredIn (Primrec.nat_lt.decide.to_comp.computableIn)
  isWellOrder := inferInstance

theorem type_natOrder (X : ℕ →. ℕ) : (natOrder X).type = ω := by
  rw [← type_nat_lt]
  exact RelIso.ordinalType_congr ⟨Equiv.Set.univ ℕ, Iff.rfl⟩

/-- **(B)** `{n | n < k}` under `<`: type `k`. -/
def finOrder (X : ℕ →. ℕ) (k : ℕ) : RecWellOrder X where
  domain := {n | n < k}
  domain_computable :=
    ComputableIn.computablePredIn
      ((Primrec.nat_lt.decide.to_comp.computableIn₂ (O := {X})).comp ComputableIn.id
        (ComputableIn.const k))
  rel := (· < ·)
  rel_computable := ComputableIn.computablePredIn (Primrec.nat_lt.decide.to_comp.computableIn)
  isWellOrder := inferInstance

theorem type_finOrder (X : ℕ →. ℕ) (k : ℕ) : (finOrder X k).type = k := by
  rw [← type_fin]
  exact RelIso.ordinalType_congr ⟨Fin.equivSubtype.symm, Iff.rfl⟩

/-- **(B)** The empty presentation: type `0`. -/
def emptyOrder (X : ℕ →. ℕ) : RecWellOrder X := finOrder X 0

theorem type_emptyOrder (X : ℕ →. ℕ) : (emptyOrder X).type = 0 := by
  rw [emptyOrder, type_finOrder]; rfl

/-! ### Transport along an oracle reduction -/

/-- **(J)** Relabel the two computability proofs along an oracle that computes `X`; the domain, the
relation, and hence the type are untouched. -/
def transport {Y : ℕ →. ℕ} (h : RecursiveIn {Y} X) : RecWellOrder Y where
  domain := W.domain
  domain_computable :=
    computablePredIn_of_oracle_transport (fun g hg ↦ by
      rw [Set.mem_singleton_iff] at hg; subst hg; exact h) W.domain_computable
  rel := W.rel
  rel_computable :=
    computablePredIn_of_oracle_transport (fun g hg ↦ by
      rw [Set.mem_singleton_iff] at hg; subst hg; exact h) W.rel_computable
  isWellOrder := W.isWellOrder

@[simp] theorem transport_domain {Y : ℕ →. ℕ} (h : RecursiveIn {Y} X) :
    (W.transport h).domain = W.domain := rfl

@[simp] theorem transport_rel {Y : ℕ →. ℕ} (h : RecursiveIn {Y} X) :
    (W.transport h).rel = W.rel := rfl

@[simp] theorem transport_type {Y : ℕ →. ℕ} (h : RecursiveIn {Y} X) :
    (W.transport h).type = W.type := rfl

end RecWellOrder

/-! ### The presented ordinals -/

/-- The ordinals presented by some recursive well-order relative to `X`. -/
def RecOrdinals (X : ℕ →. ℕ) : Set Ordinal.{0} :=
  {α | ∃ W : RecWellOrder X, W.type = α}

namespace RecOrdinals

variable {X : ℕ →. ℕ}

theorem type_mem (W : RecWellOrder X) : W.type ∈ RecOrdinals X := ⟨W, rfl⟩

/-- **(A)** -/
theorem lt_omega_one {α : Ordinal.{0}} (h : α ∈ RecOrdinals X) : α < ω_ 1 := by
  obtain ⟨W, rfl⟩ := h
  exact W.type_lt_omega_one

/-- **(B)** -/
theorem omega0_mem : ω ∈ RecOrdinals X := ⟨_, RecWellOrder.type_natOrder X⟩

theorem natCast_mem (k : ℕ) : (k : Ordinal.{0}) ∈ RecOrdinals X :=
  ⟨_, RecWellOrder.type_finOrder X k⟩

theorem zero_mem : (0 : Ordinal.{0}) ∈ RecOrdinals X := ⟨_, RecWellOrder.type_emptyOrder X⟩

/-- **(C)** Downward closure. -/
theorem mem_of_lt {α β : Ordinal.{0}} (hβ : β < α) (hα : α ∈ RecOrdinals X) :
    β ∈ RecOrdinals X := by
  obtain ⟨W, rfl⟩ := hα
  obtain ⟨a, -, h⟩ := W.exists_type_restrict_eq hβ
  exact ⟨_, h⟩

/-- **(D)** Successor closure. -/
theorem succ_mem {α : Ordinal.{0}} (hα : α ∈ RecOrdinals X) : α + 1 ∈ RecOrdinals X := by
  obtain ⟨W, rfl⟩ := hα
  exact ⟨W.succ, W.type_succ⟩

/-- **(J)** Turing monotonicity. -/
theorem mono {Y : ℕ →. ℕ} (h : RecursiveIn {Y} X) : RecOrdinals X ⊆ RecOrdinals Y := by
  rintro α ⟨W, rfl⟩
  exact ⟨W.transport h, rfl⟩

/-! #### Countability, through code presentations -/

/-- The set a code presents: the inputs on which it returns `1 = encode true`. -/
def codeSet (X : ℕ →. ℕ) (c : OracleCode) : Set ℕ :=
  {n | 1 ∈ OracleCode.evalIn X c n}

/-- The relation a code presents, on paired inputs. -/
def codeRel (X : ℕ →. ℕ) (c : OracleCode) (a b : ℕ) : Prop :=
  1 ∈ OracleCode.evalIn X c (Nat.pair a b)

open Classical in
/-- The order type a code pair presents, when its relation well-orders its set; `0` otherwise.
Classical: the case split is not a validity decision procedure. -/
noncomputable def codeType (X : ℕ →. ℕ) (p : OracleCode × OracleCode) : Ordinal.{0} :=
  if h : IsWellOrder (codeSet X p.1) (Subrel (codeRel X p.2) (· ∈ codeSet X p.1)) then
    @Ordinal.type _ _ h
  else 0

theorem codeType_lt_omega_one (p : OracleCode × OracleCode) : codeType X p < ω_ 1 := by
  unfold codeType
  split_ifs
  · exact RecWellOrder.type_subtype_lt_omega_one _
  · exact omega_pos 1

private theorem one_mem_some_encode_iff (b : Bool) : (1 : ℕ) ∈ Part.some (encode b) ↔ b = true := by
  cases b <;> simp [Part.mem_some_iff]

/-- A computable set is presented by the code of its indicator. -/
private theorem exists_codeSet_eq {s : Set ℕ} (hs : ComputablePredIn {X} (· ∈ s)) :
    ∃ c : OracleCode, codeSet X c = s := by
  obtain ⟨D, h⟩ := hs
  obtain ⟨c, hc⟩ := OracleCode.exists_code X h
  refine ⟨c, Set.ext fun n ↦ ?_⟩
  change 1 ∈ OracleCode.evalIn X c n ↔ n ∈ s
  rw [hc]
  simp only [Encodable.decode_nat, Part.coe_some, Part.bind_some, Part.map_some]
  rw [one_mem_some_encode_iff]
  exact decide_eq_true_iff

/-- A computable relation is presented by the code of its indicator on pairs. -/
private theorem exists_codeRel_eq {r : ℕ → ℕ → Prop} (hr : ComputableRelIn {X} r) :
    ∃ c : OracleCode, codeRel X c = r := by
  obtain ⟨D, h⟩ := hr
  obtain ⟨c, hc⟩ := OracleCode.exists_code X h
  refine ⟨c, funext fun a ↦ funext fun b ↦ propext ?_⟩
  change 1 ∈ OracleCode.evalIn X c (Nat.pair a b) ↔ r a b
  rw [hc, show Nat.pair a b = encode (a, b) from rfl]
  simp only [encodek, Part.coe_some, Part.bind_some, Part.map_some]
  rw [one_mem_some_encode_iff]
  letI := D (a, b)
  exact decide_eq_true_iff

private theorem codeType_eq_of_eq {cd cr : OracleCode} {s : Set ℕ} {r : ℕ → ℕ → Prop}
    (hs : codeSet X cd = s) (hr : codeRel X cr = r) [inst : IsWellOrder s (Subrel r (· ∈ s))] :
    codeType X (cd, cr) = @Ordinal.type _ _ inst := by
  subst hs hr
  exact dif_pos inst

/-- **Every presented ordinal is the type of a code pair.** -/
theorem type_mem_range_codeType (W : RecWellOrder X) : W.type ∈ Set.range (codeType X) := by
  obtain ⟨cd, hd⟩ := exists_codeSet_eq W.domain_computable
  obtain ⟨cr, hr⟩ := exists_codeRel_eq W.rel_computable
  exact ⟨(cd, cr), codeType_eq_of_eq hd hr⟩

theorem subset_range_codeType : RecOrdinals X ⊆ Set.range (codeType X) := by
  rintro α ⟨W, rfl⟩
  exact type_mem_range_codeType W

/-- **(E)** The presented ordinals form a countable set: they lie in the range of `codeType X` over
the countable type of code pairs. -/
theorem countable : (RecOrdinals X).Countable :=
  (Set.countable_range (codeType X)).mono subset_range_codeType

end RecOrdinals

/-! ### The least non-presented ordinal -/

/-- **`ω₁^X`**: the least ordinal not presented by a recursive well-order relative to `X`. -/
noncomputable def omegaOneOf (X : ℕ →. ℕ) : Ordinal.{0} :=
  sInf (RecOrdinals X)ᶜ

namespace omegaOneOf

variable {X : ℕ →. ℕ}

/-- `ω₁` itself is not presented, by (A). -/
theorem omega_one_notMem_recOrdinals : ω_ 1 ∉ RecOrdinals X :=
  fun h ↦ lt_irrefl _ (RecOrdinals.lt_omega_one h)

/-- **(F)** The complement is nonempty, so the infimum is attained. -/
theorem compl_recOrdinals_nonempty : (RecOrdinals X)ᶜ.Nonempty :=
  ⟨_, omega_one_notMem_recOrdinals⟩

/-- **(F)** The boundary is not presented. -/
theorem notMem_recOrdinals : omegaOneOf X ∉ RecOrdinals X :=
  csInf_mem compl_recOrdinals_nonempty

/-- **(G)** The strict-cut characterization. -/
theorem lt_iff {α : Ordinal.{0}} : α < omegaOneOf X ↔ α ∈ RecOrdinals X := by
  constructor
  · intro h
    by_contra hα
    exact absurd (csInf_le' (show α ∈ (RecOrdinals X)ᶜ from hα)) (not_le.2 h)
  · intro hα
    by_contra h
    rcases (not_lt.1 h).lt_or_eq with hlt | heq
    · exact notMem_recOrdinals (RecOrdinals.mem_of_lt hlt hα)
    · exact notMem_recOrdinals (heq ▸ hα)

/-- Every presented ordinal is below the boundary. -/
theorem lt_of_mem {α : Ordinal.{0}} (h : α ∈ RecOrdinals X) : α < omegaOneOf X :=
  lt_iff.2 h

/-- **(H)** The boundary is below `ω₁`: countably many code types, each below the regular `ℵ₁`,
have supremum below `ω₁`, and the successor of that supremum is not presented. -/
theorem lt_omega_one : omegaOneOf X < ω_ 1 := by
  have hsup : (⨆ p, RecOrdinals.codeType X p) < ω_ 1 := by
    rw [← Cardinal.ord_aleph]
    refine Ordinal.iSup_lt_of_lt_cof ?_ fun p ↦ ?_
    · rw [Cardinal.isRegular_aleph_one.cof_ord]
      exact Cardinal.mk_le_aleph0.trans_lt Cardinal.aleph0_lt_aleph_one
    · rw [Cardinal.ord_aleph]
      exact RecOrdinals.codeType_lt_omega_one p
  have hnot : Order.succ (⨆ p, RecOrdinals.codeType X p) ∉ RecOrdinals X := by
    rintro ⟨W, hW⟩
    obtain ⟨p, hp⟩ := RecOrdinals.type_mem_range_codeType W
    have hle := Ordinal.le_iSup (RecOrdinals.codeType X) p
    rw [hp, hW] at hle
    exact absurd hle (not_le.2 (Order.lt_succ _))
  exact (csInf_le' hnot).trans_lt ((isSuccLimit_omega 1).succ_lt hsup)

/-- **(I)** `ω` is below the boundary. -/
theorem omega0_lt : ω < omegaOneOf X :=
  lt_of_mem RecOrdinals.omega0_mem

theorem pos : 0 < omegaOneOf X :=
  lt_of_mem RecOrdinals.zero_mem

/-- **(I)** No presented ordinal is greatest: the boundary is closed under successor from below. -/
theorem succ_lt {α : Ordinal.{0}} (h : α < omegaOneOf X) : α + 1 < omegaOneOf X :=
  lt_of_mem (RecOrdinals.succ_mem (lt_iff.1 h))

/-- **(K)** Turing monotonicity. -/
theorem mono {Y : ℕ →. ℕ} (h : RecursiveIn {Y} X) : omegaOneOf X ≤ omegaOneOf Y :=
  csInf_le_csInf' compl_recOrdinals_nonempty (Set.compl_subset_compl.2 (RecOrdinals.mono h))

/-- **(K)** Turing-equivalence invariance. -/
theorem eq_of_equiv {Y : ℕ →. ℕ} (hXY : RecursiveIn {Y} X) (hYX : RecursiveIn {X} Y) :
    omegaOneOf X = omegaOneOf Y :=
  le_antisymm (mono hXY) (mono hYX)

end omegaOneOf
