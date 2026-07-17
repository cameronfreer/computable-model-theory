/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.RankPresentation

/-!
# Level-2: computable initial-segment presentations and certified upgrades

The single explicit target type for both certificate branches:
`ComputableInitialSegmentPresentationIn` carries a **shape** — `finite n` or `omega` —
and its domain, domain decider, and total-code evaluators are all *derived* from the
shape and the stored partial evaluators, never stored independently:

* the domain is `shape.toSet` (`{m | m < n}` or `Set.univ`);
* the domain decider is `DomainShape.decMem`, computed from the shape;
* total-code evaluators (`totalFunMap`, with its named correctness theorem
  `totalFunMap_correct`) guard on the derived decider and read off the partial
  evaluator, defaulting off-domain.

The certified upgrades are visibly separate constructors on a c.e. presentation, each
taking its explicit certificate — `ExactFiniteCertificate → finite card`,
`InfinitudeCertificate → omega` — and both land in the one type, through the rank
presentation (so the upgraded domain is literally the rank domain, with the shape's
set equal to `Set.range posRank` by the certificate). No coercion or instance performs
an upgrade silently. The `omega` case additionally converts to the all-ℕ
`ComputableStructureIn` (`toComputableStructure`). The nonuniform corollary
(`exists_initialSegment`) then has one clean existential target: classically, every
c.e. presentation has an initial-segment presentation with the same rank structure —
uniformity is impossible here, per the recorded Pullback obstruction.

Per the nonemptiness boundary documented at `CePresentationIn`, upgrades never produce
`finite 0`.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

/-- The shape of an initial-segment domain: a finite initial segment or all of ω. -/
inductive DomainShape where
  /-- The finite initial segment `{0, …, n - 1}`. -/
  | finite (n : ℕ)
  /-- All of ω. -/
  | omega
deriving DecidableEq

namespace DomainShape

/-- The domain a shape denotes. -/
def toSet : DomainShape → Set ℕ
  | finite n => {m | m < n}
  | omega => Set.univ

/-- The domain decider, derived from the shape. -/
@[reducible]
def decMem : (s : DomainShape) → DecidablePred (· ∈ s.toSet)
  | finite _ => fun m ↦ Nat.decLt m _
  | omega => fun _ ↦ .isTrue trivial

@[simp]
theorem toSet_finite (n : ℕ) : (finite n).toSet = {m | m < n} :=
  rfl

@[simp]
theorem toSet_omega : omega.toSet = Set.univ :=
  rfl

end DomainShape

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- A computable initial-segment presentation: structure data with a domain of known
shape (`finite n` or `omega`), domain-closure, and partial evaluators correct on the
shape's set. The domain and its decider are derived from the shape — no independent
predicate is stored. The Level-2 target of both certified upgrades. -/
structure ComputableInitialSegmentPresentationIn (O : Set (ℕ →. ℕ)) (L : Language)
    [L.EffectiveLanguage] where
  /-- The structure data, total on codes; only its on-domain behavior is meaningful. -/
  str : L.Structure ℕ
  /-- The domain shape. -/
  shape : DomainShape
  /-- The domain is closed under the interpretations of function symbols. -/
  domain_closed : ∀ (n : ℕ) (f : L.Functions n) (v : Fin n → ℕ),
    (∀ k, v k ∈ shape.toSet) → @Structure.funMap L ℕ str n f v ∈ shape.toSet
  /-- The partial function evaluator. -/
  funEval : FunctionApplicationData L ℕ →. ℕ
  /-- The function evaluator is partial recursive in the oracle. -/
  funEval_recursiveIn : RecursiveIn O funEval
  /-- On domain-valued arguments, the evaluator halts with the interpretation. -/
  funEval_correct : ∀ d : FunctionApplicationData L ℕ,
    (∀ k, d.args k ∈ shape.toSet) →
      @FunctionApplicationData.funMap L ℕ str d ∈ funEval d
  /-- The partial relation decider. -/
  relEval : RelationApplicationData L ℕ →. Bool
  /-- The relation decider is partial recursive in the oracle. -/
  relEval_recursiveIn : RecursiveIn O relEval
  /-- On domain-valued arguments, the decider halts with the truth value. -/
  relEval_correct : ∀ d : RelationApplicationData L ℕ,
    (∀ k, d.args k ∈ shape.toSet) →
      ∃ b ∈ relEval d, (b = true ↔ @RelationApplicationData.relMap L ℕ str d)

namespace ComputableInitialSegmentPresentationIn

variable (Q : ComputableInitialSegmentPresentationIn O L)

/-- The derived domain. -/
def domain : Set ℕ :=
  Q.shape.toSet

/-- The derived domain decider. -/
@[reducible]
def decMem : DecidablePred (· ∈ Q.domain) :=
  Q.shape.decMem

/-- The Boolean argument guard for function application data, derived from the
shape. -/
def funArgGuard (d : FunctionApplicationData L ℕ) : Bool :=
  d.argsList.all fun m ↦ @decide (m ∈ Q.domain) (Q.decMem m)

theorem funArgGuard_iff (d : FunctionApplicationData L ℕ) :
    Q.funArgGuard d = true ↔ ∀ k, d.args k ∈ Q.domain := by
  simp only [funArgGuard, List.all_eq_true, decide_eq_true_eq,
    FunctionApplicationData.argsList, List.mem_ofFn]
  exact ⟨fun h k ↦ h _ ⟨k, rfl⟩, fun h m ⟨k, hk⟩ ↦ hk ▸ h k⟩

/-- The derived total-code function evaluator: guard on the derived decider, read off
the partial evaluator, default `0` off-guard. -/
noncomputable def totalFunMap (d : FunctionApplicationData L ℕ) : ℕ :=
  if h : Q.funArgGuard d = true then
    (Q.funEval d).get
      (Part.dom_iff_mem.2
        ⟨_, Q.funEval_correct d ((Q.funArgGuard_iff d).1 h)⟩)
  else 0

/-- Named correctness of the derived total evaluator: on the domain it is the
interpretation. -/
theorem totalFunMap_correct (d : FunctionApplicationData L ℕ)
    (hd : ∀ k, d.args k ∈ Q.domain) :
    Q.totalFunMap d = @FunctionApplicationData.funMap L ℕ Q.str d := by
  rw [totalFunMap, dif_pos ((Q.funArgGuard_iff d).2 hd)]
  exact Part.get_eq_of_mem (Q.funEval_correct d hd) _

/-- The derived total-code relation predicate: the decider's verdict where the guard
holds, `False` off-guard. -/
def totalRelMap (d : RelationApplicationData L ℕ) : Prop :=
  (∀ k, d.args k ∈ Q.domain) ∧ true ∈ Q.relEval d

/-- Named correctness of the derived total relation predicate: on the domain it is the
interpretation. -/
theorem totalRelMap_iff (d : RelationApplicationData L ℕ)
    (hd : ∀ k, d.args k ∈ Q.domain) :
    Q.totalRelMap d ↔ @RelationApplicationData.relMap L ℕ Q.str d := by
  obtain ⟨b, hb, hbiff⟩ := Q.relEval_correct d hd
  constructor
  · rintro ⟨-, htrue⟩
    exact hbiff.1 (Part.mem_unique hb htrue)
  · intro hR
    exact ⟨hd, hbiff.2 hR ▸ hb⟩

/-- On shape `omega` the evaluators are total, so the presentation converts to the
all-ℕ `ComputableStructureIn`: an explicit conversion, not a coercion. -/
noncomputable def toComputableStructure (h : Q.shape = .omega) :
    ComputableStructureIn O L :=
  letI : L.Structure ℕ := Q.str
  have huniv : ∀ m : ℕ, m ∈ Q.domain := fun m ↦ by
    show m ∈ Q.shape.toSet
    rw [h]
    trivial
  { inst := Q.str
    isComputable :=
      { funMap_computableIn :=
          Q.funEval_recursiveIn.of_eq fun d ↦
            Part.eq_some_iff.2 (Q.funEval_correct d fun _ ↦ huniv _)
        relMap_computablePredIn := by
          refine ⟨fun d ↦ Classical.propDecidable _, ?_⟩
          have hB : ComputableIn O fun d : RelationApplicationData L ℕ ↦
              (Q.relEval d).get (Part.dom_iff_mem.2
                ⟨_, (Q.relEval_correct d fun _ ↦ huniv _).choose_spec.1⟩) :=
            Q.relEval_recursiveIn.of_eq fun d ↦
              Part.eq_some_iff.2 (Part.get_mem _)
          refine hB.of_eq fun d ↦ ?_
          obtain ⟨b, hb, hbiff⟩ := Q.relEval_correct d fun _ ↦ huniv _
          rw [Part.get_eq_of_mem hb]
          haveI : Decidable (@RelationApplicationData.relMap L ℕ Q.str d) :=
            Classical.propDecidable _
          by_cases hR : @RelationApplicationData.relMap L ℕ Q.str d
          · cases hbv : b with
            | true => exact (decide_eq_true hR).symm.trans (decide_eq_decide.2 Iff.rfl)
            | false => exact absurd hR fun h ↦ Bool.noConfusion (hbv ▸ hbiff.2 h)
          · cases hbv : b with
            | false => exact (decide_eq_false hR).symm.trans (decide_eq_decide.2 Iff.rfl)
            | true => exact absurd (hbiff.1 hbv) hR } }

end ComputableInitialSegmentPresentationIn

namespace CePresentationIn

variable (P : CePresentationIn O L)

/-! ### The certificates and the certified upgrades

The certificates are explicit, supplied inputs — never recovered from the enumeration —
and each upgrade is a visibly separate constructor landing in the single Level-2 type
through the rank presentation. -/

/-- An infinitude certificate: every rank position is defined. Supplied input; nothing
recovers this from the c.e. data. -/
structure InfinitudeCertificate (P : CePresentationIn O L) : Prop where
  /-- Every rank is realized. -/
  rankIdx_dom : ∀ r, (P.rankIdx r).Dom

/-- An exact-finite certificate: the exact number of distinct elements. Supplied
input; nothing recovers the cardinality from the c.e. data. -/
structure ExactFiniteCertificate (P : CePresentationIn O L) where
  /-- The exact number of distinct enumerated elements. -/
  card : ℕ
  /-- Every rank below the cardinality is realized. -/
  rankIdx_dom : ∀ r < card, (P.rankIdx r).Dom
  /-- No rank at or beyond the cardinality is realized. -/
  rankIdx_not_dom : ∀ r, card ≤ r → ¬(P.rankIdx r).Dom

/-- Under an infinitude certificate, the rank domain is all of ω. -/
theorem range_posRank_eq_univ (cert : P.InfinitudeCertificate) :
    Set.range P.posRank = Set.univ :=
  Set.eq_univ_of_forall fun r ↦
    (P.rankIdx_dom_iff_mem_range_posRank r).1 (cert.rankIdx_dom r)

/-- Under an exact-finite certificate, the rank domain is the initial segment of the
cardinality. -/
theorem range_posRank_eq_lt (cert : P.ExactFiniteCertificate) :
    Set.range P.posRank = {r | r < cert.card} := by
  ext r
  rw [Set.mem_setOf_eq, ← P.rankIdx_dom_iff_mem_range_posRank]
  constructor
  · intro h
    by_contra hge
    exact cert.rankIdx_not_dom r (Nat.le_of_not_lt hge) h
  · exact cert.rankIdx_dom r

/-- The certified-infinite upgrade: the rank presentation with shape `omega`. A
visibly separate constructor taking its explicit certificate. -/
noncomputable def upgradeOmega (cert : P.InfinitudeCertificate) :
    ComputableInitialSegmentPresentationIn O L where
  str := P.rankStr
  shape := .omega
  domain_closed := fun _ _ _ _ ↦ trivial
  funEval := P.rankFunEval
  funEval_recursiveIn := P.rankFunEval_recursiveIn
  funEval_correct := fun d _ ↦
    P.rankPresentation.funEval_correct d fun _ ↦ by
      show _ ∈ Set.range P.posRank
      rw [P.range_posRank_eq_univ cert]; trivial
  relEval := P.rankRelEval
  relEval_recursiveIn := P.rankRelEval_recursiveIn
  relEval_correct := fun d _ ↦
    P.rankPresentation.relEval_correct d fun _ ↦ by
      show _ ∈ Set.range P.posRank
      rw [P.range_posRank_eq_univ cert]; trivial

/-- The certified-exact-finite upgrade: the rank presentation with shape
`finite card`. A visibly separate constructor taking its explicit certificate. -/
noncomputable def upgradeFinite (cert : P.ExactFiniteCertificate) :
    ComputableInitialSegmentPresentationIn O L where
  str := P.rankStr
  shape := .finite cert.card
  domain_closed := fun n f v hv ↦ by
    have heq := P.range_posRank_eq_lt cert
    show _ ∈ {r | r < cert.card}
    rw [← heq]
    exact P.rankPresentation.domain_closed n f v fun k ↦ by
      show _ ∈ Set.range P.posRank
      rw [heq]; exact hv k
  funEval := P.rankFunEval
  funEval_recursiveIn := P.rankFunEval_recursiveIn
  funEval_correct := fun d hd ↦
    P.rankPresentation.funEval_correct d fun k ↦ by
      show _ ∈ Set.range P.posRank
      rw [P.range_posRank_eq_lt cert]; exact hd k
  relEval := P.rankRelEval
  relEval_recursiveIn := P.rankRelEval_recursiveIn
  relEval_correct := fun d hd ↦
    P.rankPresentation.relEval_correct d fun k ↦ by
      show _ ∈ Set.range P.posRank
      rw [P.range_posRank_eq_lt cert]; exact hd k

@[simp]
theorem upgradeOmega_domain (cert : P.InfinitudeCertificate) :
    (P.upgradeOmega cert).domain = Set.range P.posRank :=
  (P.range_posRank_eq_univ cert).symm

@[simp]
theorem upgradeFinite_domain (cert : P.ExactFiniteCertificate) :
    (P.upgradeFinite cert).domain = Set.range P.posRank :=
  (P.range_posRank_eq_lt cert).symm

/-- The nonuniform corollary: classically, every c.e. presentation admits an
initial-segment presentation carrying its rank structure, with the shape's set equal to
the rank domain. One clean existential target; uniformity is impossible, per the
recorded Pullback obstruction. -/
theorem exists_initialSegment (P : CePresentationIn O L) :
    ∃ Q : ComputableInitialSegmentPresentationIn O L,
      Q.str = P.rankStr ∧ Q.domain = Set.range P.posRank := by
  classical
  by_cases hinf : ∀ r, (P.rankIdx r).Dom
  · exact ⟨P.upgradeOmega ⟨hinf⟩, rfl, P.upgradeOmega_domain ⟨hinf⟩⟩
  · rw [not_forall] at hinf
    obtain ⟨r₀, hr₀⟩ := hinf
    have hex : ∃ c, ¬(P.rankIdx c).Dom := ⟨r₀, hr₀⟩
    set c := Nat.find hex with hc
    refine ⟨P.upgradeFinite ⟨c, ?_, ?_⟩, rfl, P.upgradeFinite_domain _⟩
    · intro r hr
      by_contra hnd
      exact Nat.find_min hex hr hnd
    · intro r hcr hd
      exact Nat.find_spec hex (P.rankIdx_dom_mono hcr hd)

end CePresentationIn

end FirstOrder.Language
