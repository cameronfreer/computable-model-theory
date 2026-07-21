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

/-! ### The decision procedure of the coded carrier -/

/-- The canonical-code decider: decode and check stage validity plus normalization
fixedness, through the certified decidability of the canonical domain. -/
noncomputable def canonCodeB : ℕ → Bool := fun c ↦
  @decide (IsCanonicalPair D cert (Nat.unpair c))
    ((CeDomainChainIn.isCanonical_computablePredIn cert).choose (Nat.unpair c))

theorem canonCodeB_computableIn : ComputableIn O (D.canonCodeB cert) :=
  ((CeDomainChainIn.isCanonical_computablePredIn cert).choose_spec.comp
    (Primrec.unpair.to_comp.computableIn)).of_eq fun _ ↦ rfl

theorem canonCodeB_eq_true_iff {c : ℕ} :
    D.canonCodeB cert c = true ↔ IsCanonicalCode D cert c :=
  @decide_eq_true_iff _
    ((CeDomainChainIn.isCanonical_computablePredIn cert).choose (Nat.unpair c))

theorem argsList_all_eq_true_iff {n : ℕ} (v : Fin n → ℕ) :
    (List.ofFn v).all (D.canonCodeB cert) = true ↔
      ∀ k, IsCanonicalCode D cert (v k) := by
  rw [List.all_eq_true]
  constructor
  · intro h k
    exact (D.canonCodeB_eq_true_iff cert).1 (h _ (List.mem_ofFn.2 ⟨k, rfl⟩))
  · rintro h x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    exact (D.canonCodeB_eq_true_iff cert).2 (h k)

/-- The coded witness: the canonical representative of stage 0's first enumerated
element. -/
noncomputable def codedWitness : ℕ :=
  Nat.pair (CeDomainChainIn.normalize cert (0, (D.stageAt 0).enum 0)).1
    (CeDomainChainIn.normalize cert (0, (D.stageAt 0).enum 0)).2

theorem codedWitness_isCanonical : IsCanonicalCode D cert (D.codedWitness cert) :=
  D.isCanonicalCode_pair cert (D.isCanonicalPair_normalize cert ⟨0, rfl⟩)

/-! ### The evaluator computations

Each evaluator is a guarded composite: decide canonicity of every argument, traverse
the transports to the maximal stage, reassemble, run the uniform stage evaluator, and
(for functions) normalize and re-code the output. On canonical arguments the
composite halts with the coded operation's value; off them the guard returns junk
immediately — so the composite is an everywhere-halting computation of the total
evaluator. -/

/-- The function-evaluator core, run only when every argument is canonical. -/
noncomputable def codedFunEvalCore : FunctionApplicationData L ℕ →. ℕ :=
  fun d ↦ (listMapPart
      (fun c : ℕ ↦ D.transportTo c.unpair.1 (stageBound d.argsList) c.unpair.2)
      d.argsList).bind fun src ↦
    ((FunctionApplicationData.ofSymbolArgs? (d.toSymbol, src) :
        Option (FunctionApplicationData L ℕ)) :
        Part (FunctionApplicationData L ℕ)).bind fun d' ↦
      ((D.stageAt (stageBound d.argsList)).funEval d').bind fun y ↦
        Part.some (Nat.pair
          (CeDomainChainIn.normalize cert (stageBound d.argsList, y)).1
          (CeDomainChainIn.normalize cert (stageBound d.argsList, y)).2)

/-- The guarded function evaluator. -/
noncomputable def codedFunEvalAux : FunctionApplicationData L ℕ →. ℕ :=
  fun d ↦ (encode (d.argsList.all (D.canonCodeB cert))).casesOn
    (motive := fun _ ↦ Part ℕ) (Part.some 0) fun _ ↦ D.codedFunEvalCore cert d

/-- The relation-evaluator core. -/
noncomputable def codedRelEvalCore : RelationApplicationData L ℕ →. Bool :=
  fun d ↦ (listMapPart
      (fun c : ℕ ↦ D.transportTo c.unpair.1 (stageBound d.argsList) c.unpair.2)
      d.argsList).bind fun src ↦
    ((RelationApplicationData.ofSymbolArgs? (d.toSymbol, src) :
        Option (RelationApplicationData L ℕ)) :
        Part (RelationApplicationData L ℕ)).bind fun d' ↦
      (D.stageAt (stageBound d.argsList)).relEval d'

/-- The guarded relation evaluator. -/
noncomputable def codedRelEvalAux : RelationApplicationData L ℕ →. Bool :=
  fun d ↦ (encode (d.argsList.all (D.canonCodeB cert))).casesOn
    (motive := fun _ ↦ Part Bool) (Part.some false) fun _ ↦ D.codedRelEvalCore d

open Classical in
/-- The total relation decider of the coded presentation. -/
noncomputable def codedRelEval (d : RelationApplicationData L ℕ) : Bool :=
  decide (@RelationApplicationData.relMap L ℕ (D.codedStr cert) d)

/-! #### Recursiveness of the composites -/

/-- Elementwise traversal: when every argument's transport is realized, the traversal
produces the source list in order. -/
private theorem traversal_mem {arity : ℕ} (g : ℕ →. ℕ) (args src : Fin arity → ℕ)
    (hsrc : ∀ k, src k ∈ g (args k)) :
    List.ofFn src ∈ listMapPart g (List.ofFn args) := by
  rw [mem_listMapPart_iff, List.forall₂_iff_get]
  refine ⟨by simp, ?_⟩
  intro i h₁ h₂
  simpa using hsrc ⟨i, by simpa using h₁⟩

section Recursiveness

variable {D} {cert}

private theorem stageBound_computableIn_fun :
    ComputableIn O fun d : FunctionApplicationData L ℕ ↦ stageBound d.argsList :=
  (ComputableIn.list_foldr
    (FunctionApplicationData.primrec_argsList.to_comp.computableIn)
    (ComputableIn.const 0)
    (((Primrec.nat_max.to_comp.computableIn₂ (O := O)).comp
      (((Primrec.fst.comp Primrec.unpair).to_comp.computableIn).comp
        (ComputableIn.fst.comp ComputableIn.snd))
      (ComputableIn.snd.comp ComputableIn.snd)).to₂ :
        ComputableIn₂ O fun (_ : FunctionApplicationData L ℕ) (p : ℕ × ℕ) ↦
          max p.1.unpair.1 p.2)).of_eq fun _ ↦ rfl

private theorem stageBound_computableIn_rel :
    ComputableIn O fun d : RelationApplicationData L ℕ ↦ stageBound d.argsList :=
  (ComputableIn.list_foldr
    (RelationApplicationData.primrec_argsList.to_comp.computableIn)
    (ComputableIn.const 0)
    (((Primrec.nat_max.to_comp.computableIn₂ (O := O)).comp
      (((Primrec.fst.comp Primrec.unpair).to_comp.computableIn).comp
        (ComputableIn.fst.comp ComputableIn.snd))
      (ComputableIn.snd.comp ComputableIn.snd)).to₂ :
        ComputableIn₂ O fun (_ : RelationApplicationData L ℕ) (p : ℕ × ℕ) ↦
          max p.1.unpair.1 p.2)).of_eq fun _ ↦ rfl

/-- The stage-parameterized decoded transport. -/
private theorem transport_decoded_recursiveIn :
    RecursiveIn₂ O fun (M : ℕ) (c : ℕ) ↦
      D.transportTo c.unpair.1 M c.unpair.2 :=
  D.toDomainChain.transportTo_recursiveIn.comp
    (((((Primrec.fst.comp Primrec.unpair).to_comp.computableIn (O := O)).comp
        ComputableIn.snd).pair ComputableIn.fst).pair
      (((Primrec.snd.comp Primrec.unpair).to_comp.computableIn).comp
        ComputableIn.snd))

attribute [local irreducible] CeDomainChainIn.transportTo CeDomainChainIn.normalize in
theorem codedFunEvalCore_recursiveIn (U : D.UniformEvaluatorsIn) :
    RecursiveIn O (D.codedFunEvalCore cert) := by
  have hbound := stageBound_computableIn_fun (O := O) (L := L)
  have hA : RecursiveIn O fun d : FunctionApplicationData L ℕ ↦
      listMapPart
        (fun c : ℕ ↦ D.transportTo c.unpair.1 (stageBound d.argsList) c.unpair.2)
        d.argsList :=
    RecursiveIn₂.comp
      (f := fun (M : ℕ) (l : List ℕ) ↦
        listMapPart (fun c : ℕ ↦ D.transportTo c.unpair.1 M c.unpair.2) l)
      (RecursiveIn.listMapPart₂
        (g := fun (M : ℕ) (c : ℕ) ↦ D.transportTo c.unpair.1 M c.unpair.2)
        transport_decoded_recursiveIn)
      hbound (FunctionApplicationData.primrec_argsList.to_comp.computableIn)
  have hAsm : RecursiveIn O fun p : FunctionApplicationData L ℕ × List ℕ ↦
      ((FunctionApplicationData.ofSymbolArgs? (p.1.toSymbol, p.2) :
        Option (FunctionApplicationData L ℕ)) : Part (FunctionApplicationData L ℕ)) :=
    ComputableIn.ofOption
      ((FunctionApplicationData.primrec_ofSymbolArgs?.to_comp.computableIn).comp
        (((FunctionApplicationData.primrec_toSymbol.to_comp.computableIn).comp
          ComputableIn.fst).pair ComputableIn.snd))
  have hEval : RecursiveIn O
      fun p : (FunctionApplicationData L ℕ × List ℕ) × FunctionApplicationData L ℕ ↦
        (D.stageAt (stageBound p.1.1.argsList)).funEval p.2 :=
    RecursiveIn.comp
      (f := fun q : ℕ × FunctionApplicationData L ℕ ↦ (D.stageAt q.1).funEval q.2)
      (g := fun p : (FunctionApplicationData L ℕ × List ℕ) ×
          FunctionApplicationData L ℕ ↦ (stageBound p.1.1.argsList, p.2))
      U.funEval_uniform
      (ComputableIn.pair
        (f := fun p : (FunctionApplicationData L ℕ × List ℕ) ×
          FunctionApplicationData L ℕ ↦ stageBound p.1.1.argsList)
        (g := fun p : (FunctionApplicationData L ℕ × List ℕ) ×
          FunctionApplicationData L ℕ ↦ p.2)
        (ComputableIn.comp
          (f := fun d : FunctionApplicationData L ℕ ↦ stageBound d.argsList)
          (g := fun p : (FunctionApplicationData L ℕ × List ℕ) ×
            FunctionApplicationData L ℕ ↦ p.1.1)
          hbound (ComputableIn.comp ComputableIn.fst ComputableIn.fst))
        ComputableIn.snd)
  have hnorm := CeDomainChainIn.normalize_computableIn cert
  have hOut : ComputableIn O
      fun q : ((FunctionApplicationData L ℕ × List ℕ) × FunctionApplicationData L ℕ)
          × ℕ ↦
        Nat.pair
          (CeDomainChainIn.normalize cert
            (stageBound q.1.1.1.argsList, q.2)).1
          (CeDomainChainIn.normalize cert
            (stageBound q.1.1.1.argsList, q.2)).2 := by
    have hpairIn : ComputableIn O
        fun q : ((FunctionApplicationData L ℕ × List ℕ) × FunctionApplicationData L ℕ)
            × ℕ ↦
          CeDomainChainIn.normalize cert (stageBound q.1.1.1.argsList, q.2) :=
      hnorm.comp
        ((hbound.comp
          (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst))).pair
          ComputableIn.snd)
    exact (Primrec₂.natPair.to_comp.computableIn₂ (O := O)).comp
      (ComputableIn.fst.comp hpairIn) (ComputableIn.snd.comp hpairIn)
  have hinner : RecursiveIn O
      fun q : (FunctionApplicationData L ℕ × List ℕ) × FunctionApplicationData L ℕ ↦
        ((D.stageAt (stageBound q.1.1.argsList)).funEval q.2).bind fun y ↦
          Part.some (Nat.pair
            (CeDomainChainIn.normalize cert (stageBound q.1.1.argsList, y)).1
            (CeDomainChainIn.normalize cert (stageBound q.1.1.argsList, y)).2) :=
    RecursiveIn.bind hEval hOut.to₂
  have hmid : RecursiveIn O fun p : FunctionApplicationData L ℕ × List ℕ ↦
      ((FunctionApplicationData.ofSymbolArgs? (p.1.toSymbol, p.2) :
        Option (FunctionApplicationData L ℕ)) :
        Part (FunctionApplicationData L ℕ)).bind fun d' ↦
        ((D.stageAt (stageBound p.1.argsList)).funEval d').bind fun y ↦
          Part.some (Nat.pair
            (CeDomainChainIn.normalize cert (stageBound p.1.argsList, y)).1
            (CeDomainChainIn.normalize cert (stageBound p.1.argsList, y)).2) :=
    RecursiveIn.bind hAsm hinner.to₂
  have houter : RecursiveIn O fun d : FunctionApplicationData L ℕ ↦
      (listMapPart
        (fun c : ℕ ↦ D.transportTo c.unpair.1 (stageBound d.argsList) c.unpair.2)
        d.argsList).bind fun src ↦
        ((FunctionApplicationData.ofSymbolArgs? (d.toSymbol, src) :
          Option (FunctionApplicationData L ℕ)) :
          Part (FunctionApplicationData L ℕ)).bind fun d' ↦
          ((D.stageAt (stageBound d.argsList)).funEval d').bind fun y ↦
            Part.some (Nat.pair
              (CeDomainChainIn.normalize cert (stageBound d.argsList, y)).1
              (CeDomainChainIn.normalize cert (stageBound d.argsList, y)).2) :=
    RecursiveIn.bind hA hmid.to₂
  exact houter.of_eq fun d ↦ rfl

attribute [local irreducible] CeDomainChainIn.transportTo in
theorem codedRelEvalCore_recursiveIn (U : D.UniformEvaluatorsIn) :
    RecursiveIn O (D.codedRelEvalCore) := by
  have hbound := stageBound_computableIn_rel (O := O) (L := L)
  have hA : RecursiveIn O fun d : RelationApplicationData L ℕ ↦
      listMapPart
        (fun c : ℕ ↦ D.transportTo c.unpair.1 (stageBound d.argsList) c.unpair.2)
        d.argsList :=
    RecursiveIn₂.comp
      (f := fun (M : ℕ) (l : List ℕ) ↦
        listMapPart (fun c : ℕ ↦ D.transportTo c.unpair.1 M c.unpair.2) l)
      (RecursiveIn.listMapPart₂
        (g := fun (M : ℕ) (c : ℕ) ↦ D.transportTo c.unpair.1 M c.unpair.2)
        transport_decoded_recursiveIn)
      hbound (RelationApplicationData.primrec_argsList.to_comp.computableIn)
  have hAsm : RecursiveIn O fun p : RelationApplicationData L ℕ × List ℕ ↦
      ((RelationApplicationData.ofSymbolArgs? (p.1.toSymbol, p.2) :
        Option (RelationApplicationData L ℕ)) : Part (RelationApplicationData L ℕ)) :=
    ComputableIn.ofOption
      ((RelationApplicationData.primrec_ofSymbolArgs?.to_comp.computableIn).comp
        (((RelationApplicationData.primrec_toSymbol.to_comp.computableIn).comp
          ComputableIn.fst).pair ComputableIn.snd))
  have hEval : RecursiveIn O
      fun p : (RelationApplicationData L ℕ × List ℕ) × RelationApplicationData L ℕ ↦
        (D.stageAt (stageBound p.1.1.argsList)).relEval p.2 :=
    RecursiveIn.comp
      (f := fun q : ℕ × RelationApplicationData L ℕ ↦ (D.stageAt q.1).relEval q.2)
      (g := fun p : (RelationApplicationData L ℕ × List ℕ) ×
          RelationApplicationData L ℕ ↦ (stageBound p.1.1.argsList, p.2))
      U.relEval_uniform
      (ComputableIn.pair
        (f := fun p : (RelationApplicationData L ℕ × List ℕ) ×
          RelationApplicationData L ℕ ↦ stageBound p.1.1.argsList)
        (g := fun p : (RelationApplicationData L ℕ × List ℕ) ×
          RelationApplicationData L ℕ ↦ p.2)
        (ComputableIn.comp
          (f := fun d : RelationApplicationData L ℕ ↦ stageBound d.argsList)
          (g := fun p : (RelationApplicationData L ℕ × List ℕ) ×
            RelationApplicationData L ℕ ↦ p.1.1)
          hbound (ComputableIn.comp ComputableIn.fst ComputableIn.fst))
        ComputableIn.snd)
  exact RecursiveIn.bind hA ((RecursiveIn.bind hAsm hEval.to₂).to₂)

/-- The canonicity guard is computable. -/
private theorem allCanon_computableIn_fun :
    ComputableIn O fun d : FunctionApplicationData L ℕ ↦
      d.argsList.all (D.canonCodeB cert) := by
  refine (ComputableIn.list_foldr
    (FunctionApplicationData.primrec_argsList.to_comp.computableIn)
    (ComputableIn.const true)
    ((ComputableIn.cond
      ((D.canonCodeB_computableIn cert).comp (ComputableIn.fst.comp ComputableIn.snd))
      (ComputableIn.snd.comp ComputableIn.snd) (ComputableIn.const false)).to₂ :
        ComputableIn₂ O fun (_ : FunctionApplicationData L ℕ) (p : ℕ × Bool) ↦
          bif D.canonCodeB cert p.1 then p.2 else false)).of_eq fun d ↦ ?_
  induction d.argsList with
  | nil => rfl
  | cons a t ih =>
    rw [List.foldr_cons, ih, List.all_cons]
    cases D.canonCodeB cert a <;> rfl

private theorem allCanon_computableIn_rel :
    ComputableIn O fun d : RelationApplicationData L ℕ ↦
      d.argsList.all (D.canonCodeB cert) := by
  refine (ComputableIn.list_foldr
    (RelationApplicationData.primrec_argsList.to_comp.computableIn)
    (ComputableIn.const true)
    ((ComputableIn.cond
      ((D.canonCodeB_computableIn cert).comp (ComputableIn.fst.comp ComputableIn.snd))
      (ComputableIn.snd.comp ComputableIn.snd) (ComputableIn.const false)).to₂ :
        ComputableIn₂ O fun (_ : RelationApplicationData L ℕ) (p : ℕ × Bool) ↦
          bif D.canonCodeB cert p.1 then p.2 else false)).of_eq fun d ↦ ?_
  induction d.argsList with
  | nil => rfl
  | cons a t ih =>
    rw [List.foldr_cons, ih, List.all_cons]
    cases D.canonCodeB cert a <;> rfl

theorem codedFunEvalAux_recursiveIn (U : D.UniformEvaluatorsIn) :
    RecursiveIn O (D.codedFunEvalAux cert) :=
  RecursiveIn.nat_casesOn_right
    (ComputableIn.encode.comp allCanon_computableIn_fun)
    (ComputableIn.const 0)
    (((codedFunEvalCore_recursiveIn U).comp ComputableIn.fst).to₂)

theorem codedRelEvalAux_recursiveIn (U : D.UniformEvaluatorsIn) :
    RecursiveIn O (D.codedRelEvalAux cert) :=
  RecursiveIn.nat_casesOn_right
    (ComputableIn.encode.comp allCanon_computableIn_rel)
    (ComputableIn.const false)
    (((codedRelEvalCore_recursiveIn U).comp ComputableIn.fst).to₂)

end Recursiveness

/-! #### The composites compute the coded operations -/

/-- On canonical arguments, the function core halts with the coded function value. -/
theorem codedFunMap_mem_codedFunEvalCore (d : FunctionApplicationData L ℕ)
    (h : ∀ k, IsCanonicalCode D cert (d.args k)) :
    D.codedFunMap cert d.symbol d.args ∈ D.codedFunEvalCore cert d := by
  set M := stageBound d.argsList with hM
  set src := D.canonicalSrc cert d.args h with hsrcdef
  have hsrc : ∀ k, src k ∈ D.transportTo (d.args k).unpair.1 M (d.args k).unpair.2 :=
    fun k ↦ D.canonicalSrc_mem cert d.args h k
  have hdom : ∀ k, src k ∈ (D.stageAt M).domain :=
    fun k ↦ D.canonicalSrc_domain cert d.args h k
  have hlen : (List.ofFn src).length = d.toSymbol.arity := by
    simp [FunctionApplicationData.toSymbol, FunctionSymbol.arity]
  set d' : FunctionApplicationData L ℕ :=
    FunctionApplicationData.equivSubtype.symm ⟨(d.toSymbol, List.ofFn src), hlen⟩
    with hd'
  have hargs : d'.args = src := by
    funext i
    show (List.ofFn src).get (Fin.cast hlen.symm i) = src i
    simp
  have hd'args : ∀ k, d'.args k ∈ (D.stageAt M).domain := fun k ↦ hargs ▸ hdom k
  have hfunMap : @FunctionApplicationData.funMap L ℕ (D.stageAt M).str d' =
      @Structure.funMap L ℕ (D.stageAt M).str d.arity d.symbol src := by
    show @Structure.funMap L ℕ (D.stageAt M).str _ d'.symbol d'.args = _
    rw [hargs]
    exact rfl
  have hvalue := (D.stageAt M).funEval_correct d' hd'args
  rw [hfunMap] at hvalue
  rw [codedFunEvalCore]
  refine Part.mem_bind_iff.2 ⟨List.ofFn src,
    traversal_mem (fun c ↦ D.transportTo c.unpair.1 M c.unpair.2) d.args src hsrc, ?_⟩
  refine Part.mem_bind_iff.2 ⟨d', ?_, ?_⟩
  · rw [FunctionApplicationData.ofSymbolArgs?_of_length_eq _ hlen]
    exact Part.mem_some _
  · refine Part.mem_bind_iff.2
      ⟨@Structure.funMap L ℕ (D.stageAt M).str d.arity d.symbol src, hvalue, ?_⟩
    rw [D.codedFunMap_eq_normalize cert d.symbol d.args h]
    exact Part.mem_some _

/-- The guarded function evaluator is exactly the constant lift of the coded function
interpretation: an everywhere-halting computation of the total evaluator. -/
theorem codedFunEvalAux_eq (d : FunctionApplicationData L ℕ) :
    D.codedFunEvalAux cert d =
      Part.some (@FunctionApplicationData.funMap L ℕ (D.codedStr cert) d) := by
  by_cases h : ∀ k, IsCanonicalCode D cert (d.args k)
  · have hall : d.argsList.all (D.canonCodeB cert) = true :=
      (D.argsList_all_eq_true_iff cert d.args).2 h
    rw [codedFunEvalAux, hall]
    exact (Part.eq_some_iff.2 (D.codedFunMap_mem_codedFunEvalCore cert d h)).trans
      (congrArg _ rfl)
  · have hall : d.argsList.all (D.canonCodeB cert) = false := by
      rcases hb : d.argsList.all (D.canonCodeB cert) with - | -
      · rfl
      · exact absurd ((D.argsList_all_eq_true_iff cert d.args).1 hb) h
    rw [codedFunEvalAux, hall]
    show Part.some 0 = _
    rw [show @FunctionApplicationData.funMap L ℕ (D.codedStr cert) d
      = D.codedFunMap cert d.symbol d.args from rfl, codedFunMap, dif_neg h]

/-- On canonical arguments, the relation core halts with the truth value of the coded
relation. -/
theorem codedRelEval_mem_codedRelEvalCore (d : RelationApplicationData L ℕ)
    (h : ∀ k, IsCanonicalCode D cert (d.args k)) :
    D.codedRelEval cert d ∈ D.codedRelEvalCore d := by
  set M := stageBound d.argsList with hM
  set src := fun k ↦ (D.transportTo (d.args k).unpair.1 M (d.args k).unpair.2).get
    (by
      obtain ⟨y, hy, -⟩ := D.toDomainChain.transportTo_dom _
        (le_stageBound (List.mem_ofFn.2 ⟨k, rfl⟩)) (h k).limMem
      exact Part.dom_iff_mem.2 ⟨y, hy⟩) with hsrcdef
  have hsrc : ∀ k, src k ∈ D.transportTo (d.args k).unpair.1 M (d.args k).unpair.2 :=
    fun k ↦ Part.get_mem _
  have hdom : ∀ k, src k ∈ (D.stageAt M).domain := fun k ↦
    D.mem_domain_of_transport (h k).limMem
      (le_stageBound (List.mem_ofFn.2 ⟨k, rfl⟩)) (hsrc k)
  have hlen : (List.ofFn src).length = d.toSymbol.arity := by
    simp [RelationApplicationData.toSymbol, RelationSymbol.arity]
  set d' : RelationApplicationData L ℕ :=
    RelationApplicationData.equivSubtype.symm ⟨(d.toSymbol, List.ofFn src), hlen⟩
    with hd'
  have hargs : d'.args = src := by
    funext i
    show (List.ofFn src).get (Fin.cast hlen.symm i) = src i
    simp
  have hd'args : ∀ k, d'.args k ∈ (D.stageAt M).domain := fun k ↦ hargs ▸ hdom k
  have hrelMap : @RelationApplicationData.relMap L ℕ (D.stageAt M).str d' ↔
      @Structure.RelMap L ℕ (D.stageAt M).str d.arity d.symbol src := by
    show @Structure.RelMap L ℕ (D.stageAt M).str _ d'.symbol d'.args ↔ _
    rw [hargs]
    exact Iff.rfl
  obtain ⟨b, hb, hbiff⟩ := (D.stageAt M).relEval_correct d' hd'args
  have hlim : D.LimRelHolds d.symbol (fun k ↦ Nat.unpair (d.args k)) ↔
      @Structure.RelMap L ℕ (D.stageAt M).str d.arity d.symbol src :=
    D.limRelHolds_iff_realization (v := fun k ↦ Nat.unpair (d.args k)) d.symbol
      (fun k ↦ (h k).limMem)
      (fun k ↦ le_stageBound (List.mem_ofFn.2 ⟨k, rfl⟩)) hsrc
  have hbval : b = D.codedRelEval cert d :=
    Bool.eq_iff_iff.2 (((hbiff.trans hrelMap).trans
      (hlim.symm.trans (D.codedRelMap_iff cert d.symbol d.args h).symm)).trans
      (@decide_eq_true_iff _ (Classical.propDecidable _)).symm)
  rw [codedRelEvalCore]
  refine Part.mem_bind_iff.2 ⟨List.ofFn src,
    traversal_mem (fun c ↦ D.transportTo c.unpair.1 M c.unpair.2) d.args src hsrc, ?_⟩
  refine Part.mem_bind_iff.2 ⟨d', ?_, hbval ▸ hb⟩
  rw [RelationApplicationData.ofSymbolArgs?_of_length_eq _ hlen]
  exact Part.mem_some _

/-- The guarded relation evaluator is exactly the constant lift of the total relation
decider. -/
theorem codedRelEvalAux_eq (d : RelationApplicationData L ℕ) :
    D.codedRelEvalAux cert d = Part.some (D.codedRelEval cert d) := by
  by_cases h : ∀ k, IsCanonicalCode D cert (d.args k)
  · have hall : d.argsList.all (D.canonCodeB cert) = true :=
      (D.argsList_all_eq_true_iff cert d.args).2 h
    rw [codedRelEvalAux, hall]
    exact Part.eq_some_iff.2 (D.codedRelEval_mem_codedRelEvalCore cert d h)
  · have hall : d.argsList.all (D.canonCodeB cert) = false := by
      rcases hb : d.argsList.all (D.canonCodeB cert) with - | -
      · rfl
      · exact absurd ((D.argsList_all_eq_true_iff cert d.args).1 hb) h
    rw [codedRelEvalAux, hall]
    show Part.some false = _
    rw [codedRelEval, @decide_eq_false _ (Classical.propDecidable _) fun hc ↦ h hc.1]

/-! ### The coded presentation -/

/-- The coded presentation of a c.e. structure chain: under a decidable-stages
certificate and uniform stage evaluators, the canonical codes carry a
decidable-domain presentation whose operations are the normalized limit
operations. -/
noncomputable def codedPresentation (U : D.UniformEvaluatorsIn) :
    DecidablePresentationIn O L where
  str := D.codedStr cert
  domainB := D.canonCodeB cert
  domainB_computableIn := D.canonCodeB_computableIn cert
  witness := D.codedWitness cert
  witness_mem := (D.canonCodeB_eq_true_iff cert).2 (D.codedWitness_isCanonical cert)
  domain_closed := fun _ f v hv ↦ (D.canonCodeB_eq_true_iff cert).2
    (D.codedFunMap_isCanonical cert f v
      fun k ↦ (D.canonCodeB_eq_true_iff cert).1 (hv k))
  funEvalTotal := fun d ↦ @FunctionApplicationData.funMap L ℕ (D.codedStr cert) d
  funEvalTotal_computableIn :=
    (codedFunEvalAux_recursiveIn U).of_eq fun d ↦ D.codedFunEvalAux_eq cert d
  funEvalTotal_correct := fun _ _ ↦ rfl
  relEvalTotal := D.codedRelEval cert
  relEvalTotal_computableIn :=
    (codedRelEvalAux_recursiveIn U).of_eq fun d ↦ D.codedRelEvalAux_eq cert d
  relEvalTotal_correct := fun _ _ ↦
    @decide_eq_true_iff _ (Classical.propDecidable _)

/-- The coded presentation's domain is exactly the canonical codes. -/
theorem codedPresentation_domain (U : D.UniformEvaluatorsIn) :
    (D.codedPresentation cert U).domain = {c | IsCanonicalCode D cert c} :=
  Set.ext fun _ ↦ D.canonCodeB_eq_true_iff cert

/-! ### Normalized stage embeddings and the union of stages -/

/-- Canonical codes are equal exactly when their decoded pairs are limit
equivalent — the coded carrier separates limit elements. -/
theorem canonicalCode_eq_of_limEquiv {c₁ c₂ : ℕ}
    (h₁ : IsCanonicalCode D cert c₁) (h₂ : IsCanonicalCode D cert c₂)
    (h : D.toDomainChain.limEquiv (Nat.unpair c₁) (Nat.unpair c₂)) : c₁ = c₂ := by
  have heq := CeDomainChainIn.normalize_eq_of_limEquiv cert h₁.limMem h₂.limMem h
  rw [h₁.2, h₂.2] at heq
  calc c₁ = Nat.pair (Nat.unpair c₁).1 (Nat.unpair c₁).2 := (Nat.pair_unpair c₁).symm
    _ = Nat.pair (Nat.unpair c₂).1 (Nat.unpair c₂).2 := by rw [heq]
    _ = c₂ := Nat.pair_unpair c₂

/-- The normalized stage embedding into the coded carrier: a stage element goes to
the code of its canonical representative. -/
noncomputable def stageIntoCoded (i x : ℕ) : ℕ :=
  Nat.pair (CeDomainChainIn.normalize cert (i, x)).1
    (CeDomainChainIn.normalize cert (i, x)).2

theorem stageIntoCoded_isCanonical {i x : ℕ} (hx : x ∈ (D.stageAt i).domain) :
    IsCanonicalCode D cert (D.stageIntoCoded cert i x) :=
  D.isCanonicalCode_pair cert (D.isCanonicalPair_normalize cert hx)

theorem stageIntoCoded_unpair_equiv {i x : ℕ} (hx : x ∈ (D.stageAt i).domain) :
    D.toDomainChain.limEquiv ((i, x) : ℕ × ℕ)
      (Nat.unpair (D.stageIntoCoded cert i x)) := by
  rw [stageIntoCoded, Nat.unpair_pair]
  exact (CeDomainChainIn.normalize_spec cert (p := (i, x)) hx).2

/-- Normalized stage embeddings are injective on each stage's domain. -/
theorem stageIntoCoded_injective {i x₁ x₂ : ℕ} (hx₁ : x₁ ∈ (D.stageAt i).domain)
    (hx₂ : x₂ ∈ (D.stageAt i).domain)
    (h : D.stageIntoCoded cert i x₁ = D.stageIntoCoded cert i x₂) : x₁ = x₂ := by
  refine CeDomainChainIn.normalize_stageInto_injOn cert hx₁ hx₂ ?_
  have h₁ := congrArg (fun c ↦ (Nat.unpair c).1) h
  have h₂ := congrArg (fun c ↦ (Nat.unpair c).2) h
  simp only [stageIntoCoded, Nat.unpair_pair] at h₁ h₂
  exact Prod.ext h₁ h₂

/-- Normalized stage embeddings commute with transport: an element and any transport
image share their canonical code. -/
theorem stageIntoCoded_transport {i j x y : ℕ} (hij : i ≤ j)
    (hx : x ∈ (D.stageAt i).domain) (hy : y ∈ D.transportTo i j x) :
    D.stageIntoCoded cert i x = D.stageIntoCoded cert j y := by
  have h := CeDomainChainIn.normalize_stageInto_transport cert hij hx hy
  rw [show CeDomainChainIn.stageInto i x = ((i : ℕ), x) from rfl,
    show CeDomainChainIn.stageInto j y = ((j : ℕ), y) from rfl] at h
  rw [stageIntoCoded, stageIntoCoded, h]

/-- The union of stages: every canonical code is a normalized stage image — the coded
carrier is exhausted by (indeed, equal to) the images of the stage domains. -/
theorem stageIntoCoded_surjective {c : ℕ} (hc : IsCanonicalCode D cert c) :
    ∃ i x, x ∈ (D.stageAt i).domain ∧ c = D.stageIntoCoded cert i x := by
  refine ⟨(Nat.unpair c).1, (Nat.unpair c).2, hc.limMem, ?_⟩
  rw [stageIntoCoded, hc.2, Nat.pair_unpair]

/-- Normalized stage embeddings are homomorphisms: the coded function of stage images
is the stage image of the stage function value. -/
theorem stageIntoCoded_funMap {i n : ℕ} (f : L.Functions n) (v : Fin n → ℕ)
    (hv : ∀ k, v k ∈ (D.stageAt i).domain) :
    D.codedFunMap cert f (fun k ↦ D.stageIntoCoded cert i (v k))
      = D.stageIntoCoded cert i (@Structure.funMap L ℕ (D.stageAt i).str n f v) := by
  have hcanon : ∀ k, IsCanonicalCode D cert (D.stageIntoCoded cert i (v k)) :=
    fun k ↦ D.stageIntoCoded_isCanonical cert (hv k)
  have hout : (@Structure.funMap L ℕ (D.stageAt i).str n f v) ∈ (D.stageAt i).domain :=
    (D.stageAt i).domain_closed n f v hv
  refine D.canonicalCode_eq_of_limEquiv cert
    (D.codedFunMap_isCanonical cert f _ hcanon)
    (D.stageIntoCoded_isCanonical cert hout) ?_
  -- The stage-`i` computation is itself a limit value of the image tuple.
  have hbase : D.LimFunGraph f (fun k ↦ ((i, v k) : ℕ × ℕ))
      (i, @Structure.funMap L ℕ (D.stageAt i).str n f v) := by
    refine ⟨i, v, fun _ ↦ le_refl i, ?_, D.toDomainChain.limEquiv_refl _⟩
    intro k
    rw [transportTo, CeDomainChainIn.transportTo_self]
    exact Part.mem_some _
  have hbase' : D.LimFunGraph f
      (fun k ↦ Nat.unpair (D.stageIntoCoded cert i (v k)))
      (i, @Structure.funMap L ℕ (D.stageAt i).str n f v) :=
    D.limFunGraph_of_limEquiv (v := fun k ↦ ((i, v k) : ℕ × ℕ))
      (v' := fun k ↦ Nat.unpair (D.stageIntoCoded cert i (v k)))
      (out := (i, @Structure.funMap L ℕ (D.stageAt i).str n f v))
      (out' := (i, @Structure.funMap L ℕ (D.stageAt i).str n f v)) f
      (fun k ↦ hv k) (fun k ↦ (hcanon k).limMem)
      (fun k ↦ D.stageIntoCoded_unpair_equiv cert (hv k)) hout hout
      (D.toDomainChain.limEquiv_refl _) hbase
  have h₁ := D.limFunGraph_functional
    (out₁ := Nat.unpair (D.codedFunMap cert f
      (fun k ↦ D.stageIntoCoded cert i (v k))))
    (out₂ := (i, @Structure.funMap L ℕ (D.stageAt i).str n f v)) f
    (fun k ↦ (hcanon k).limMem)
    (D.codedFunMap_limFunGraph cert f _ hcanon) hbase'
    (D.codedFunMap_isCanonical cert f _ hcanon).limMem hout
  exact D.toDomainChain.limEquiv_trans
    (p := Nat.unpair (D.codedFunMap cert f
      (fun k ↦ D.stageIntoCoded cert i (v k))))
    (q := (i, @Structure.funMap L ℕ (D.stageAt i).str n f v))
    (r := Nat.unpair (D.stageIntoCoded cert i
      (@Structure.funMap L ℕ (D.stageAt i).str n f v)))
    (D.codedFunMap_isCanonical cert f _ hcanon).limMem hout
    (D.stageIntoCoded_isCanonical cert hout).limMem h₁
    (D.stageIntoCoded_unpair_equiv cert hout)

/-- Normalized stage embeddings transfer relations exactly. -/
theorem stageIntoCoded_relMap {i n : ℕ} (R : L.Relations n) (v : Fin n → ℕ)
    (hv : ∀ k, v k ∈ (D.stageAt i).domain) :
    D.codedRelMap cert R (fun k ↦ D.stageIntoCoded cert i (v k))
      ↔ @Structure.RelMap L ℕ (D.stageAt i).str n R v := by
  have hcanon : ∀ k, IsCanonicalCode D cert (D.stageIntoCoded cert i (v k)) :=
    fun k ↦ D.stageIntoCoded_isCanonical cert (hv k)
  rw [D.codedRelMap_iff cert R _ hcanon]
  refine Iff.trans (D.limRelHolds_iff_of_limEquiv
    (v := fun k ↦ Nat.unpair (D.stageIntoCoded cert i (v k)))
    (v' := fun k ↦ ((i, v k) : ℕ × ℕ)) R
    (fun k ↦ (hcanon k).limMem) (fun k ↦ hv k)
    fun k ↦ D.toDomainChain.limEquiv_symm
      (D.stageIntoCoded_unpair_equiv cert (hv k))) ?_
  refine D.limRelHolds_iff_realization (v := fun k ↦ ((i, v k) : ℕ × ℕ)) R
    (fun k ↦ hv k) (fun _ ↦ le_refl i) fun k ↦ ?_
  rw [transportTo, CeDomainChainIn.transportTo_self]
  exact Part.mem_some _

end CeStructureChainIn

end FirstOrder.Language
