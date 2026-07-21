/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureLimit
import ComputableModelTheory.ModelTheory.Computable.DecidablePresentation

/-!
# The coded presentation of a c.e. structure chain, under certificates

The certified layer of effective direct limits: under a decidable-stages certificate,
the canonical representatives — normalization-fixed valid pairs — form a computably
decidable subset of ℕ via `Nat.pair` coding, and the limit operations descend to
**normalized** total-code operations on those codes: a function value is computed by
realizing the arguments at their maximal stage, applying that stage's interpretation,
and normalizing the output back to its canonical representative.

Per the carrier contract, none of this exists for bare Level-1 stages: the certificate
is an explicit argument everywhere. The semantic laws (`codedFunMap_isCanonical`,
`codedFunMap_limFunGraph`, `codedRelMap_iff`) tie the coded operations to the raw
limit operations of `CeStructureChain`, whose invariance theorems make the values
representative-independent.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace CeStructureChainIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (D : CeStructureChainIn O L)

/-- Uniform stage-evaluator computability: the stage presentations' partial evaluators
are partial recursive **uniformly in the stage**. Per-stage recursiveness does not
imply this, so it is explicit input data, like the certificate itself. -/
structure UniformEvaluatorsIn (D : CeStructureChainIn O L) : Prop where
  funEval_uniform : RecursiveIn O
    fun q : ℕ × FunctionApplicationData L ℕ ↦ (D.stageAt q.1).funEval q.2
  relEval_uniform : RecursiveIn O
    fun q : ℕ × RelationApplicationData L ℕ ↦ (D.stageAt q.1).relEval q.2

variable (cert : D.toDomainChain.DecidableStagesCertificate)

/-! ### Canonical pairs and canonical codes -/

/-- A canonical pair: stage-valid and normalization-fixed. This is the
representative-space image of the certified canonical domain. -/
def IsCanonicalPair (p : ℕ × ℕ) : Prop :=
  cert.memB p.1 p.2 = true ∧ CeDomainChainIn.normalize cert p = p

theorem IsCanonicalPair.limMem {p : ℕ × ℕ} (h : IsCanonicalPair D cert p) :
    D.toDomainChain.limMem p :=
  (cert.memB_iff p.1 p.2).1 h.1

theorem isCanonicalPair_normalize {p : ℕ × ℕ} (hp : D.toDomainChain.limMem p) :
    IsCanonicalPair D cert (CeDomainChainIn.normalize cert p) :=
  ⟨(cert.memB_iff _ _).2 (CeDomainChainIn.normalize_spec cert hp).1,
    CeDomainChainIn.normalize_normalize cert hp⟩

/-- A canonical code: a `Nat.pair`-code of a canonical pair. The coded carrier is cut
out of ℕ by this predicate — a decidable set, in general neither an initial segment
nor all of ℕ. -/
def IsCanonicalCode (c : ℕ) : Prop :=
  IsCanonicalPair D cert (Nat.unpair c)

theorem isCanonicalCode_pair {p : ℕ × ℕ} (h : IsCanonicalPair D cert p) :
    IsCanonicalCode D cert (Nat.pair p.1 p.2) := by
  rw [IsCanonicalCode, Nat.unpair_pair]
  exact h

/-! ### Stage bounds and canonical realizations -/

/-- The maximal stage occurring in a list of pair codes. -/
def stageBound (l : List ℕ) : ℕ :=
  l.foldr (fun c m ↦ max c.unpair.1 m) 0

theorem le_stageBound {l : List ℕ} {c : ℕ} (hc : c ∈ l) :
    c.unpair.1 ≤ stageBound l := by
  induction l with
  | nil => cases hc
  | cons a t ih =>
    rcases List.mem_cons.1 hc with rfl | h
    · exact Nat.le_max_left _ _
    · exact le_trans (ih h) (Nat.le_max_right _ _)

theorem le_stageBound_ofFn {n : ℕ} (v : Fin n → ℕ) (k : Fin n) :
    (v k).unpair.1 ≤ stageBound (List.ofFn v) :=
  le_stageBound (List.mem_ofFn.2 ⟨k, rfl⟩)

/-- The canonical realization of a tuple of canonical codes at its maximal stage:
transport each decoded pair up and read the value. Total on the canonicity
hypothesis because on-domain transport halts. -/
noncomputable def canonicalSrc {n : ℕ} (v : Fin n → ℕ)
    (h : ∀ k, IsCanonicalCode D cert (v k)) (k : Fin n) : ℕ :=
  (D.transportTo (v k).unpair.1 (stageBound (List.ofFn v)) (v k).unpair.2).get
    (by
      obtain ⟨y, hy, -⟩ := D.toDomainChain.transportTo_dom _
        (le_stageBound_ofFn v k) (h k).limMem
      exact Part.dom_iff_mem.2 ⟨y, hy⟩)

theorem canonicalSrc_mem {n : ℕ} (v : Fin n → ℕ)
    (h : ∀ k, IsCanonicalCode D cert (v k)) (k : Fin n) :
    D.canonicalSrc cert v h k
      ∈ D.transportTo (v k).unpair.1 (stageBound (List.ofFn v)) (v k).unpair.2 :=
  Part.get_mem _

theorem canonicalSrc_domain {n : ℕ} (v : Fin n → ℕ)
    (h : ∀ k, IsCanonicalCode D cert (v k)) (k : Fin n) :
    D.canonicalSrc cert v h k ∈ (D.stageAt (stageBound (List.ofFn v))).domain :=
  D.mem_domain_of_transport (h k).limMem (le_stageBound_ofFn v k)
    (D.canonicalSrc_mem cert v h k)

/-! ### The coded operations -/

open Classical in
/-- The coded function value: realize the arguments at their maximal stage, apply the
stage interpretation, **normalize the output**, and code the canonical pair. Total on
codes; junk off the canonical domain. -/
noncomputable def codedFunMap {n : ℕ} (f : L.Functions n) (v : Fin n → ℕ) : ℕ :=
  if h : ∀ k, IsCanonicalCode D cert (v k) then
    Nat.pair
      (CeDomainChainIn.normalize cert (stageBound (List.ofFn v),
        @Structure.funMap L ℕ (D.stageAt (stageBound (List.ofFn v))).str n f
          (D.canonicalSrc cert v h))).1
      (CeDomainChainIn.normalize cert (stageBound (List.ofFn v),
        @Structure.funMap L ℕ (D.stageAt (stageBound (List.ofFn v))).str n f
          (D.canonicalSrc cert v h))).2
  else 0

/-- The coded relation: the raw limit relation on the decoded pairs, cut down to
canonical codes. Total on codes as a proposition. -/
def codedRelMap {n : ℕ} (R : L.Relations n) (v : Fin n → ℕ) : Prop :=
  (∀ k, IsCanonicalCode D cert (v k)) ∧
    D.LimRelHolds R fun k ↦ Nat.unpair (v k)

/-- The coded structure on ℕ. -/
@[reducible]
noncomputable def codedStr : L.Structure ℕ where
  funMap f v := D.codedFunMap cert f v
  RelMap R v := D.codedRelMap cert R v

/-- The stage value the coded function normalizes. -/
theorem codedFunMap_eq_normalize {n : ℕ} (f : L.Functions n) (v : Fin n → ℕ)
    (h : ∀ k, IsCanonicalCode D cert (v k)) :
    D.codedFunMap cert f v =
      Nat.pair
        (CeDomainChainIn.normalize cert (stageBound (List.ofFn v),
          @Structure.funMap L ℕ (D.stageAt (stageBound (List.ofFn v))).str n f
            (D.canonicalSrc cert v h))).1
        (CeDomainChainIn.normalize cert (stageBound (List.ofFn v),
          @Structure.funMap L ℕ (D.stageAt (stageBound (List.ofFn v))).str n f
            (D.canonicalSrc cert v h))).2 := by
  rw [codedFunMap, dif_pos h]

/-- The realized stage value is a valid pair. -/
theorem stageValue_limMem {n : ℕ} (f : L.Functions n) (v : Fin n → ℕ)
    (h : ∀ k, IsCanonicalCode D cert (v k)) :
    D.toDomainChain.limMem (stageBound (List.ofFn v),
      @Structure.funMap L ℕ (D.stageAt (stageBound (List.ofFn v))).str n f
        (D.canonicalSrc cert v h)) :=
  (D.stageAt (stageBound (List.ofFn v))).domain_closed n f _
    fun k ↦ D.canonicalSrc_domain cert v h k

/-- On canonical arguments, the coded function value is itself a canonical code —
the closure law of the coded carrier. -/
theorem codedFunMap_isCanonical {n : ℕ} (f : L.Functions n) (v : Fin n → ℕ)
    (h : ∀ k, IsCanonicalCode D cert (v k)) :
    IsCanonicalCode D cert (D.codedFunMap cert f v) := by
  rw [D.codedFunMap_eq_normalize cert f v h]
  exact D.isCanonicalCode_pair cert
    (D.isCanonicalPair_normalize cert (D.stageValue_limMem cert f v h))

/-- On canonical arguments, the decoded coded function value is a limit value of the
decoded arguments: the coded operation computes the limit function, normalized. -/
theorem codedFunMap_limFunGraph {n : ℕ} (f : L.Functions n) (v : Fin n → ℕ)
    (h : ∀ k, IsCanonicalCode D cert (v k)) :
    D.LimFunGraph f (fun k ↦ Nat.unpair (v k))
      (Nat.unpair (D.codedFunMap cert f v)) := by
  rw [D.codedFunMap_eq_normalize cert f v h, Nat.unpair_pair]
  exact ⟨stageBound (List.ofFn v), D.canonicalSrc cert v h,
    fun k ↦ le_stageBound_ofFn v k, fun k ↦ D.canonicalSrc_mem cert v h k,
    (CeDomainChainIn.normalize_spec cert (D.stageValue_limMem cert f v h)).2⟩

/-- The coded relation on canonical arguments is exactly the raw limit relation of
the decoded pairs. -/
theorem codedRelMap_iff {n : ℕ} (R : L.Relations n) (v : Fin n → ℕ)
    (h : ∀ k, IsCanonicalCode D cert (v k)) :
    D.codedRelMap cert R v ↔ D.LimRelHolds R fun k ↦ Nat.unpair (v k) :=
  ⟨fun hc ↦ hc.2, fun hr ↦ ⟨h, hr⟩⟩

end CeStructureChainIn

end FirstOrder.Language
