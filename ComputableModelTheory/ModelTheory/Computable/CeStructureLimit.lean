/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureChain
import Mathlib.Data.Fintype.Quotient

/-!
# The semantic direct limit of a c.e. structure chain

The quotient descent of the raw limit operations of `CeStructureChainIn`. Per the
carrier contract's terminology guard, the extensional limit carrier exists at Level 1
**only** as this semantic quotient: valid representatives (`Rep`) up to `limEquiv`.
Nothing here is computable, and nothing needs to be — the computable content lives in
the certified coded presentation, gated on a decidable-stages certificate.

The limit structure interprets a function symbol by realizing the arguments at a
common stage and applying that stage's interpretation (`limFunRep`, a choice from
`limFunGraph_total`), and a relation symbol by `LimRelHolds`; the invariance theorems
of `CeStructureChain` are exactly the soundness obligations of the two quotient lifts.
The computation laws recover both through representatives (`limitStructure_funMap_eq`,
`limitStructure_relMap_iff`), and the graph characterization
(`limitStructure_funMap_eq_iff`) identifies quotient-level equality of a function
value with the raw limit graph.

Stage elements inject into the limit (`stageIntoLimit`): injectively on each stage's
domain, compatibly with the chain steps, and as a homomorphism-and-embedding —
functions commute and relations transfer exactly. Every limit element is a stage
image (`exists_stageIntoLimit`), so the limit is the union of its stages.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace CeStructureChainIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (D : CeStructureChainIn O L)

/-! ### The setoid of valid representatives -/

/-- A valid representative: a stage-tagged code in the limit domain. -/
def Rep : Type :=
  {p : ℕ × ℕ // D.toDomainChain.limMem p}

/-- Valid representatives under the limit equivalence. -/
instance repSetoid : Setoid D.Rep where
  r p q := D.toDomainChain.limEquiv p.1 q.1
  iseqv :=
    ⟨fun p ↦ D.toDomainChain.limEquiv_refl p.1,
      fun h ↦ D.toDomainChain.limEquiv_symm h,
      fun {p q r} h₁ h₂ ↦ D.toDomainChain.limEquiv_trans p.2 q.2 r.2 h₁ h₂⟩

theorem rep_equiv_def {p q : D.Rep} :
    p ≈ q ↔ D.toDomainChain.limEquiv p.1 q.1 :=
  Iff.rfl

/-- The semantic direct-limit carrier: valid representatives up to `limEquiv`. This
quotient is all the extensional carrier Level 1 receives. -/
def Limit : Type :=
  Quotient D.repSetoid

/-! ### Quotient descent of the limit operations -/

/-- A representative of the limit value of a function: realize the arguments at a
common stage and take that stage's value. Noncomputable by design — this is the
semantic layer. -/
noncomputable def limFunRep {n : ℕ} (f : L.Functions n) (v : Fin n → D.Rep) : D.Rep :=
  ⟨(D.limFunGraph_total f (fun k ↦ (v k).2)).choose,
    (D.limFunGraph_total f (fun k ↦ (v k).2)).choose_spec.2⟩

theorem limFunRep_graph {n : ℕ} (f : L.Functions n) (v : Fin n → D.Rep) :
    D.LimFunGraph f (fun k ↦ (v k).1) (D.limFunRep f v).1 :=
  (D.limFunGraph_total f (fun k ↦ (v k).2)).choose_spec.1

/-- Soundness of the function lift: pointwise-equivalent argument tuples give
equivalent values. -/
theorem limFunRep_sound {n : ℕ} (f : L.Functions n) {v v' : Fin n → D.Rep}
    (h : ∀ k, v k ≈ v' k) : D.limFunRep f v ≈ D.limFunRep f v' :=
  D.limFunGraph_functional f (fun k ↦ (v' k).2)
    (D.limFunGraph_of_limEquiv f (fun k ↦ (v k).2) (fun k ↦ (v' k).2) h
      (D.limFunRep f v).2 (D.limFunRep f v).2
      (D.toDomainChain.limEquiv_refl _) (D.limFunRep_graph f v))
    (D.limFunRep_graph f v') (D.limFunRep f v).2 (D.limFunRep f v').2

/-- Soundness of the relation lift. -/
theorem limRelHolds_sound {n : ℕ} (R : L.Relations n) {v v' : Fin n → D.Rep}
    (h : ∀ k, v k ≈ v' k) :
    D.LimRelHolds R (fun k ↦ (v k).1) ↔ D.LimRelHolds R (fun k ↦ (v' k).1) :=
  D.limRelHolds_iff_of_limEquiv R (fun k ↦ (v k).2) (fun k ↦ (v' k).2) h

/-- The limit structure: functions realize their arguments at a common stage, and
relations are the raw limit relation — both descended to the quotient. -/
noncomputable instance limitStructure : L.Structure D.Limit where
  funMap f v :=
    (Quotient.finChoice v).liftOn (fun w ↦ ⟦D.limFunRep f w⟧)
      fun _ _ hww' ↦ Quotient.sound (D.limFunRep_sound f fun k ↦ hww' k)
  RelMap R v :=
    (Quotient.finChoice v).liftOn (fun w ↦ D.LimRelHolds R fun k ↦ (w k).1)
      fun _ _ hww' ↦ propext (D.limRelHolds_sound R fun k ↦ hww' k)

/-- Computation law for functions: on representatives, the limit function is the
class of the chosen realization. -/
theorem limitStructure_funMap_eq {n : ℕ} (f : L.Functions n) (v : Fin n → D.Rep) :
    @Structure.funMap L D.Limit D.limitStructure n f (fun k ↦ ⟦v k⟧)
      = ⟦D.limFunRep f v⟧ := by
  show ((Quotient.finChoice fun k ↦ ⟦v k⟧).liftOn _ _ : D.Limit) = _
  rw [Quotient.finChoice_eq]
  rfl

/-- Computation law for relations: on representatives, the limit relation is the raw
limit relation. -/
theorem limitStructure_relMap_iff {n : ℕ} (R : L.Relations n) (v : Fin n → D.Rep) :
    @Structure.RelMap L D.Limit D.limitStructure n R (fun k ↦ ⟦v k⟧)
      ↔ D.LimRelHolds R (fun k ↦ (v k).1) := by
  show ((Quotient.finChoice fun k ↦ ⟦v k⟧).liftOn _ _ : Prop) ↔ _
  rw [Quotient.finChoice_eq]
  exact Iff.rfl

/-- The graph characterization: a function value on representatives is a given class
exactly when the raw limit graph relates the underlying representatives. -/
theorem limitStructure_funMap_eq_iff {n : ℕ} (f : L.Functions n) (v : Fin n → D.Rep)
    (out : D.Rep) :
    @Structure.funMap L D.Limit D.limitStructure n f (fun k ↦ ⟦v k⟧) = ⟦out⟧ ↔
      D.LimFunGraph f (fun k ↦ (v k).1) out.1 := by
  rw [D.limitStructure_funMap_eq f v]
  constructor
  · intro h
    exact D.limFunGraph_of_limEquiv f (fun k ↦ (v k).2) (fun k ↦ (v k).2)
      (fun k ↦ D.toDomainChain.limEquiv_refl _) (D.limFunRep f v).2 out.2
      (Quotient.exact h) (D.limFunRep_graph f v)
  · intro h
    exact Quotient.sound (D.limFunGraph_functional f (fun k ↦ (v k).2)
      (D.limFunRep_graph f v) h (D.limFunRep f v).2 out.2)

/-! ### Stage injections into the limit -/

/-- The injection of a stage element into the semantic limit. -/
def stageIntoLimit (i x : ℕ) (hx : x ∈ (D.stageAt i).domain) : D.Limit :=
  ⟦⟨(i, x), hx⟩⟧

/-- Stage injections are injective on each stage's domain. -/
theorem stageIntoLimit_injective {i x₁ x₂ : ℕ} (hx₁ : x₁ ∈ (D.stageAt i).domain)
    (hx₂ : x₂ ∈ (D.stageAt i).domain)
    (h : D.stageIntoLimit i x₁ hx₁ = D.stageIntoLimit i x₂ hx₂) : x₁ = x₂ := by
  obtain ⟨z, hz₁, hz₂⟩ := Quotient.exact h
  rw [Nat.max_self i, CeDomainChainIn.transportTo_self] at hz₁ hz₂
  exact (Part.mem_some_iff.1 hz₁).symm.trans (Part.mem_some_iff.1 hz₂)

/-- Stage injections are compatible with the chain steps: an element and its step
image denote the same limit element. -/
theorem stageIntoLimit_step {i x y : ℕ} (hx : x ∈ (D.stageAt i).domain)
    (hy : y ∈ (D.stageAt (i + 1)).domain) (hstep : y ∈ D.step i x) :
    D.stageIntoLimit i x hx = D.stageIntoLimit (i + 1) y hy := by
  refine Quotient.sound ⟨y, ?_, ?_⟩
  · show y ∈ D.toDomainChain.transportTo i (max i (i + 1)) x
    rw [show max i (i + 1) = i + 1 from by omega]
    exact D.toDomainChain.step_mem_transportTo_succ hstep
  · show y ∈ D.toDomainChain.transportTo (i + 1) (max i (i + 1)) y
    rw [show max i (i + 1) = i + 1 from by omega,
      CeDomainChainIn.transportTo_self]
    exact Part.mem_some _

/-- More generally, transport identifies limit elements across stages. -/
theorem stageIntoLimit_transport {i j x y : ℕ} (hij : i ≤ j)
    (hx : x ∈ (D.stageAt i).domain) (hy : y ∈ (D.stageAt j).domain)
    (htrans : y ∈ D.transportTo i j x) :
    D.stageIntoLimit i x hx = D.stageIntoLimit j y hy := by
  refine Quotient.sound ⟨y, ?_, ?_⟩
  · show y ∈ D.toDomainChain.transportTo i (max i j) x
    rw [Nat.max_eq_right hij]
    exact htrans
  · show y ∈ D.toDomainChain.transportTo j (max i j) y
    rw [Nat.max_eq_right hij, CeDomainChainIn.transportTo_self]
    exact Part.mem_some _

/-- Stage injections commute with function interpretations: the stage maps are
homomorphisms into the limit. -/
theorem stageIntoLimit_funMap {i n : ℕ} (f : L.Functions n) (v : Fin n → ℕ)
    (hv : ∀ k, v k ∈ (D.stageAt i).domain) :
    @Structure.funMap L D.Limit D.limitStructure n f
        (fun k ↦ D.stageIntoLimit i (v k) (hv k))
      = D.stageIntoLimit i (@Structure.funMap L ℕ (D.stageAt i).str n f v)
          ((D.stageAt i).domain_closed n f v hv) := by
  refine (D.limitStructure_funMap_eq_iff f (fun k ↦ ⟨(i, v k), hv k⟩) _).2 ?_
  refine ⟨i, v, fun _ ↦ le_refl i, ?_, D.toDomainChain.limEquiv_refl _⟩
  intro k
  rw [transportTo, CeDomainChainIn.transportTo_self]
  exact Part.mem_some _

/-- Stage injections transfer relations exactly: the stage maps are embeddings with
respect to the relational structure. -/
theorem stageIntoLimit_relMap {i n : ℕ} (R : L.Relations n) (v : Fin n → ℕ)
    (hv : ∀ k, v k ∈ (D.stageAt i).domain) :
    @Structure.RelMap L D.Limit D.limitStructure n R
        (fun k ↦ D.stageIntoLimit i (v k) (hv k))
      ↔ @Structure.RelMap L ℕ (D.stageAt i).str n R v :=
  (D.limitStructure_relMap_iff R (fun k ↦ ⟨(i, v k), hv k⟩)).trans
    (D.limRelHolds_iff_realization (v := fun k ↦ (i, v k)) R (fun k ↦ hv k)
      (fun _ ↦ le_refl i)
      fun k ↦ by
        rw [transportTo, CeDomainChainIn.transportTo_self]
        exact Part.mem_some _)

/-- The limit is the union of its stages: every limit element is a stage image. -/
theorem exists_stageIntoLimit (q : D.Limit) :
    ∃ (i x : ℕ) (hx : x ∈ (D.stageAt i).domain), q = D.stageIntoLimit i x hx := by
  induction q using Quotient.ind with
  | _ p => exact ⟨p.1.1, p.1.2, p.2, rfl⟩

end CeStructureChainIn

end FirstOrder.Language
