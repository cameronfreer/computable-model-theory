/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.CeDomainChain
import ComputableModelTheory.ModelTheory.Computable.CePresentation

/-!
# C.e. structure chains: lifted limit operations and their invariance

The structure half of effective direct limits, over the carrier contract of
`CeDomainChainIn`: a **c.e. structure chain** has Level-1 c.e. presentations as
stages and carrier steps that preserve functions and preserve-and-reflect relations
on-domain. The derived domain chain (`toDomainChain`) reuses the entire carrier
layer — transport, the limit equivalence, and (under certificates, later) canonical
representatives.

Per the carrier contract's terminology guard, elements of `ℕ × ℕ` are
*representatives*, compared only by `limEquiv`. The raw limit operations move their
arguments to a common stage and apply that stage's interpretation:

* `LimFunGraph f v out` — some common stage `m` receives transports of every argument,
  and the stage-`m` value of `f` there is `limEquiv` to `out`;
* `LimRelHolds R v` — some common stage receives transports of every argument and
  satisfies `R` there.

The laws proved here are exactly the invariance package the descent needs: transport
preserves functions and preserves-and-reflects relations (`transport_funMap`,
`transport_relMap`); the graphs are total and functional up to `limEquiv` on valid
representatives; and both are invariant under pointwise `limEquiv`. No quotient, no
normalization, and no computable extensional carrier appear here — Level 1 receives
only this semantic layer.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- A c.e. structure chain: Level-1 c.e. presentations as stages, with uniformly
partial recursive carrier steps that are injective, domain-preserving, function-
preserving, and relation-preserving-and-reflecting on-domain. -/
structure CeStructureChainIn (O : Set (ℕ →. ℕ)) (L : Language)
    [L.EffectiveLanguage] where
  /-- The stage presentations. -/
  stageAt : ℕ → CePresentationIn O L
  /-- The stage enumerations are computable **uniformly in the stage** — per-stage
  computability does not imply this, so it is a field. -/
  enum_uniform : ComputableIn O fun p : ℕ × ℕ ↦ (stageAt p.1).enum p.2
  /-- The carrier step from stage `i` into stage `i + 1`. -/
  step : ℕ → ℕ →. ℕ
  /-- The steps are partial recursive uniformly in the stage. -/
  step_recursiveIn : RecursiveIn O fun p : ℕ × ℕ ↦ step p.1 p.2
  /-- On-domain, a step halts and lands in the next stage's domain. -/
  step_mem : ∀ i x, x ∈ (stageAt i).domain →
    ∃ y ∈ step i x, y ∈ (stageAt (i + 1)).domain
  /-- Steps are injective on domains. -/
  step_injOn : ∀ i x₁ x₂ y, x₁ ∈ (stageAt i).domain → x₂ ∈ (stageAt i).domain →
    y ∈ step i x₁ → y ∈ step i x₂ → x₁ = x₂
  /-- Steps preserve function interpretations on-domain. -/
  step_funMap : ∀ (i n : ℕ) (f : L.Functions n) (v w : Fin n → ℕ),
    (∀ k, v k ∈ (stageAt i).domain) → (∀ k, w k ∈ step i (v k)) →
      @Structure.funMap L ℕ (stageAt (i + 1)).str n f w
        ∈ step i (@Structure.funMap L ℕ (stageAt i).str n f v)
  /-- Steps preserve and reflect relation interpretations on-domain. -/
  step_relMap : ∀ (i n : ℕ) (R : L.Relations n) (v w : Fin n → ℕ),
    (∀ k, v k ∈ (stageAt i).domain) → (∀ k, w k ∈ step i (v k)) →
      (@Structure.RelMap L ℕ (stageAt (i + 1)).str n R w ↔
        @Structure.RelMap L ℕ (stageAt i).str n R v)

namespace CeStructureChainIn

variable (D : CeStructureChainIn O L)

/-- The derived carrier chain: forget the structures. All carrier machinery —
transport, the limit equivalence, certified normalization — is reused through it. -/
def toDomainChain : CeDomainChainIn O where
  enum i := (D.stageAt i).enum
  enum_computableIn := D.enum_uniform
  step := D.step
  step_recursiveIn := D.step_recursiveIn
  step_mem := D.step_mem
  step_injOn := D.step_injOn

@[simp]
theorem toDomainChain_domainAt (i : ℕ) :
    D.toDomainChain.domainAt i = (D.stageAt i).domain :=
  rfl

/-- Transport along the derived carrier chain. -/
def transportTo (i j x : ℕ) : Part ℕ :=
  D.toDomainChain.transportTo i j x

/-- Right decomposition of transport: one more stage is one more step. -/
theorem transportTo_succ_right {i j x y : ℕ} (hij : i ≤ j)
    (h : y ∈ D.transportTo i (j + 1) x) :
    ∃ u, u ∈ D.transportTo i j x ∧ y ∈ D.step j u := by
  obtain ⟨t, ht, rfl⟩ := (Part.mem_map_iff _).1 h
  have hsplit : j + 1 - i = (j - i) + 1 := by omega
  rw [hsplit, CeDomainChainIn.climbAux_succ] at ht
  obtain ⟨u, hu, hstep⟩ := Part.mem_bind_iff.1 ht
  obtain ⟨z, hz, rfl⟩ := (Part.mem_map_iff _).1 hstep
  have htag : u.1 = j := by
    have := D.toDomainChain.stage_of_mem_climbAux hu
    simp only at this
    omega
  refine ⟨u.2, (Part.mem_map_iff _).2 ⟨u, hu, rfl⟩, ?_⟩
  rw [← htag]
  exact hz

/-- Transport preserves function interpretations on-domain. -/
theorem transport_funMap {i j : ℕ} (hij : i ≤ j) {n : ℕ} (f : L.Functions n)
    {v w : Fin n → ℕ} (hv : ∀ k, v k ∈ (D.stageAt i).domain)
    (hw : ∀ k, w k ∈ D.transportTo i j (v k)) :
    @Structure.funMap L ℕ (D.stageAt j).str n f w
      ∈ D.transportTo i j (@Structure.funMap L ℕ (D.stageAt i).str n f v) := by
  induction j, hij using Nat.le_induction generalizing w with
  | base =>
    have hwv : w = v := funext fun k ↦ by
      have := hw k
      rw [transportTo, CeDomainChainIn.transportTo_self] at this
      exact Part.mem_some_iff.1 this
    rw [hwv, transportTo, CeDomainChainIn.transportTo_self]
    exact Part.mem_some _
  | succ j hij ih =>
    -- Decompose each argument's transport through stage `j`.
    have hdecomp : ∀ k, ∃ u, u ∈ D.transportTo i j (v k) ∧ w k ∈ D.step j u :=
      fun k ↦ D.transportTo_succ_right hij (hw k)
    choose u hu hstepu using hdecomp
    have hudom : ∀ k, u k ∈ (D.stageAt j).domain := fun k ↦ by
      obtain ⟨z, hz, hzdom⟩ :=
        D.toDomainChain.transportTo_dom j hij (hv k)
      rwa [Part.mem_unique (hu k) hz]
    have hmid := ih hu
    have hstepf := D.step_funMap j n f u w hudom hstepu
    have hmiddom : @Structure.funMap L ℕ (D.stageAt j).str n f u
        ∈ (D.stageAt j).domain :=
      (D.stageAt j).domain_closed n f u hudom
    -- Compose: transport to `j`, then one step.
    have hstep_as_transport :
        @Structure.funMap L ℕ (D.stageAt (j + 1)).str n f w
          ∈ D.transportTo j (j + 1)
            (@Structure.funMap L ℕ (D.stageAt j).str n f u) :=
      D.toDomainChain.step_mem_transportTo_succ hstepf
    exact D.toDomainChain.transportTo_trans hij (by omega) hmid hstep_as_transport

/-- Transport preserves and reflects relation interpretations on-domain. -/
theorem transport_relMap {i j : ℕ} (hij : i ≤ j) {n : ℕ} (R : L.Relations n)
    {v w : Fin n → ℕ} (hv : ∀ k, v k ∈ (D.stageAt i).domain)
    (hw : ∀ k, w k ∈ D.transportTo i j (v k)) :
    @Structure.RelMap L ℕ (D.stageAt j).str n R w ↔
      @Structure.RelMap L ℕ (D.stageAt i).str n R v := by
  induction j, hij using Nat.le_induction generalizing w with
  | base =>
    have hwv : w = v := funext fun k ↦ by
      have := hw k
      rw [transportTo, CeDomainChainIn.transportTo_self] at this
      exact Part.mem_some_iff.1 this
    rw [hwv]
  | succ j hij ih =>
    have hdecomp : ∀ k, ∃ u, u ∈ D.transportTo i j (v k) ∧ w k ∈ D.step j u :=
      fun k ↦ D.transportTo_succ_right hij (hw k)
    choose u hu hstepu using hdecomp
    have hudom : ∀ k, u k ∈ (D.stageAt j).domain := fun k ↦ by
      obtain ⟨z, hz, hzdom⟩ :=
        D.toDomainChain.transportTo_dom j hij (hv k)
      rwa [Part.mem_unique (hu k) hz]
    exact (D.step_relMap j n R u w hudom hstepu).trans (ih hu)

/-! ### Raw limit operations at common stages -/

/-- A common stage bound for a tuple of representatives. -/
def tupleStage {n : ℕ} (v : Fin n → ℕ × ℕ) : ℕ :=
  Finset.univ.sup fun k ↦ (v k).1

theorem le_tupleStage {n : ℕ} (v : Fin n → ℕ × ℕ) (k : Fin n) :
    (v k).1 ≤ tupleStage v :=
  Finset.le_sup (f := fun k ↦ (v k).1) (Finset.mem_univ k)

/-- The raw limit function graph: some common stage receives transports of every
argument, and its value of `f` there is `limEquiv` to the output. Representatives are
compared only through `limEquiv`, never by code equality. -/
def LimFunGraph {n : ℕ} (f : L.Functions n) (v : Fin n → ℕ × ℕ)
    (out : ℕ × ℕ) : Prop :=
  ∃ (m : ℕ) (src : Fin n → ℕ), (∀ k, (v k).1 ≤ m) ∧
    (∀ k, src k ∈ D.transportTo (v k).1 m (v k).2) ∧
    D.toDomainChain.limEquiv (m, @Structure.funMap L ℕ (D.stageAt m).str n f src) out

/-- The raw limit relation: some common stage receives transports of every argument
and satisfies the relation there. -/
def LimRelHolds {n : ℕ} (R : L.Relations n) (v : Fin n → ℕ × ℕ) : Prop :=
  ∃ (m : ℕ) (src : Fin n → ℕ), (∀ k, (v k).1 ≤ m) ∧
    (∀ k, src k ∈ D.transportTo (v k).1 m (v k).2) ∧
    @Structure.RelMap L ℕ (D.stageAt m).str n R src

/-- Validity of a tuple of representatives. -/
def TupleMem {n : ℕ} (v : Fin n → ℕ × ℕ) : Prop :=
  ∀ k, D.toDomainChain.limMem (v k)

/-- Transported values of valid representatives land on-domain. -/
theorem mem_domain_of_transport {p : ℕ × ℕ} {m s : ℕ}
    (hp : D.toDomainChain.limMem p) (hm : p.1 ≤ m)
    (hs : s ∈ D.transportTo p.1 m p.2) : s ∈ (D.stageAt m).domain := by
  obtain ⟨z, hz, hzdom⟩ := D.toDomainChain.transportTo_dom m hm hp
  rwa [Part.mem_unique hs hz]

/-- On valid tuples, a canonical realization at any late enough stage. -/
theorem exists_src {n : ℕ} {v : Fin n → ℕ × ℕ} (hv : D.TupleMem v) {m : ℕ}
    (hm : ∀ k, (v k).1 ≤ m) :
    ∃ src : Fin n → ℕ, (∀ k, src k ∈ D.transportTo (v k).1 m (v k).2) ∧
      ∀ k, src k ∈ (D.stageAt m).domain := by
  have h : ∀ k, ∃ s, s ∈ D.transportTo (v k).1 m (v k).2 ∧
      s ∈ (D.stageAt m).domain := fun k ↦ by
    obtain ⟨s, hs, hsdom⟩ := D.toDomainChain.transportTo_dom m (hm k) (hv k)
    exact ⟨s, hs, hsdom⟩
  choose src hsrc hdom using h
  exact ⟨src, hsrc, hdom⟩

/-- Totality: on valid tuples the limit function graph is inhabited, with valid
output. -/
theorem limFunGraph_total {n : ℕ} (f : L.Functions n) {v : Fin n → ℕ × ℕ}
    (hv : D.TupleMem v) :
    ∃ out, D.LimFunGraph f v out ∧ D.toDomainChain.limMem out := by
  obtain ⟨src, hsrc, hdom⟩ := D.exists_src hv (le_tupleStage v)
  refine ⟨(tupleStage v, @Structure.funMap L ℕ (D.stageAt (tupleStage v)).str n f src),
    ⟨tupleStage v, src, le_tupleStage v, hsrc,
      D.toDomainChain.limEquiv_refl _⟩, ?_⟩
  exact (D.stageAt (tupleStage v)).domain_closed n f src hdom

/-- Realizations of pointwise-`limEquiv` tuples at any two admissible stages produce
`limEquiv` values — the engine of both functionality and invariance. The one-tuple case
is `heq := fun k ↦ limEquiv_refl _`. -/
theorem realization_equiv {n : ℕ} (f : L.Functions n) {v v' : Fin n → ℕ × ℕ}
    (hv : D.TupleMem v) (hv' : D.TupleMem v')
    (heq : ∀ k, D.toDomainChain.limEquiv (v k) (v' k))
    {m₁ m₂ : ℕ} {src₁ src₂ : Fin n → ℕ}
    (hm₁ : ∀ k, (v k).1 ≤ m₁) (hm₂ : ∀ k, (v' k).1 ≤ m₂)
    (hsrc₁ : ∀ k, src₁ k ∈ D.transportTo (v k).1 m₁ (v k).2)
    (hsrc₂ : ∀ k, src₂ k ∈ D.transportTo (v' k).1 m₂ (v' k).2) :
    D.toDomainChain.limEquiv
      (m₁, @Structure.funMap L ℕ (D.stageAt m₁).str n f src₁)
      (m₂, @Structure.funMap L ℕ (D.stageAt m₂).str n f src₂) := by
  set M := max m₁ m₂ with hM
  have hdom₁ : ∀ k, src₁ k ∈ (D.stageAt m₁).domain := fun k ↦
    D.mem_domain_of_transport (hv k) (hm₁ k) (hsrc₁ k)
  have hdom₂ : ∀ k, src₂ k ∈ (D.stageAt m₂).domain := fun k ↦
    D.mem_domain_of_transport (hv' k) (hm₂ k) (hsrc₂ k)
  -- Transport both realizations to `M`; they agree there because each argument's two
  -- transports are of `limEquiv` representatives.
  obtain ⟨w₁, hw₁, hw₁dom⟩ :=
    D.exists_src (v := fun k ↦ (m₁, src₁ k)) (fun k ↦ hdom₁ k)
      (fun k ↦ Nat.le_max_left m₁ m₂)
  obtain ⟨w₂, hw₂, hw₂dom⟩ :=
    D.exists_src (v := fun k ↦ (m₂, src₂ k)) (fun k ↦ hdom₂ k)
      (fun k ↦ Nat.le_max_right m₁ m₂)
  have hagree : w₁ = w₂ := funext fun k ↦
    D.toDomainChain.transportTo_eq_of_limEquiv (hv k) (heq k)
      (le_trans (hm₁ k) (Nat.le_max_left m₁ m₂))
      (le_trans (hm₂ k) (Nat.le_max_right m₁ m₂))
      (D.toDomainChain.transportTo_trans (hm₁ k) (Nat.le_max_left m₁ m₂)
        (hsrc₁ k) (hw₁ k))
      (D.toDomainChain.transportTo_trans (hm₂ k) (Nat.le_max_right m₁ m₂)
        (hsrc₂ k) (hw₂ k))
  refine ⟨@Structure.funMap L ℕ (D.stageAt M).str n f w₁, ?_, ?_⟩
  · exact D.transport_funMap (Nat.le_max_left m₁ m₂) f hdom₁ hw₁
  · rw [hagree]
    exact D.transport_funMap (Nat.le_max_right m₁ m₂) f hdom₂ hw₂

/-- Realizations of pointwise-`limEquiv` tuples at any two admissible stages give the
same relation verdict. -/
theorem relMap_realization_iff {n : ℕ} (R : L.Relations n) {v v' : Fin n → ℕ × ℕ}
    (hv : D.TupleMem v) (hv' : D.TupleMem v')
    (heq : ∀ k, D.toDomainChain.limEquiv (v k) (v' k))
    {m₁ m₂ : ℕ} {src₁ src₂ : Fin n → ℕ}
    (hm₁ : ∀ k, (v k).1 ≤ m₁) (hm₂ : ∀ k, (v' k).1 ≤ m₂)
    (hsrc₁ : ∀ k, src₁ k ∈ D.transportTo (v k).1 m₁ (v k).2)
    (hsrc₂ : ∀ k, src₂ k ∈ D.transportTo (v' k).1 m₂ (v' k).2) :
    @Structure.RelMap L ℕ (D.stageAt m₁).str n R src₁ ↔
      @Structure.RelMap L ℕ (D.stageAt m₂).str n R src₂ := by
  set M := max m₁ m₂ with hM
  have hdom₁ : ∀ k, src₁ k ∈ (D.stageAt m₁).domain := fun k ↦
    D.mem_domain_of_transport (hv k) (hm₁ k) (hsrc₁ k)
  have hdom₂ : ∀ k, src₂ k ∈ (D.stageAt m₂).domain := fun k ↦
    D.mem_domain_of_transport (hv' k) (hm₂ k) (hsrc₂ k)
  obtain ⟨w₁, hw₁, hw₁dom⟩ :=
    D.exists_src (v := fun k ↦ (m₁, src₁ k)) (fun k ↦ hdom₁ k)
      (fun k ↦ Nat.le_max_left m₁ m₂)
  obtain ⟨w₂, hw₂, hw₂dom⟩ :=
    D.exists_src (v := fun k ↦ (m₂, src₂ k)) (fun k ↦ hdom₂ k)
      (fun k ↦ Nat.le_max_right m₁ m₂)
  have hagree : w₁ = w₂ := funext fun k ↦
    D.toDomainChain.transportTo_eq_of_limEquiv (hv k) (heq k)
      (le_trans (hm₁ k) (Nat.le_max_left m₁ m₂))
      (le_trans (hm₂ k) (Nat.le_max_right m₁ m₂))
      (D.toDomainChain.transportTo_trans (hm₁ k) (Nat.le_max_left m₁ m₂)
        (hsrc₁ k) (hw₁ k))
      (D.toDomainChain.transportTo_trans (hm₂ k) (Nat.le_max_right m₁ m₂)
        (hsrc₂ k) (hw₂ k))
  calc @Structure.RelMap L ℕ (D.stageAt m₁).str n R src₁
      ↔ @Structure.RelMap L ℕ (D.stageAt M).str n R w₁ :=
        (D.transport_relMap (Nat.le_max_left m₁ m₂) R hdom₁ hw₁).symm
    _ ↔ @Structure.RelMap L ℕ (D.stageAt M).str n R w₂ := by rw [hagree]
    _ ↔ @Structure.RelMap L ℕ (D.stageAt m₂).str n R src₂ :=
        D.transport_relMap (Nat.le_max_right m₁ m₂) R hdom₂ hw₂

/-- Functionality up to `limEquiv`: the graph relates a valid tuple to a single limit
element. -/
theorem limFunGraph_functional {n : ℕ} (f : L.Functions n) {v : Fin n → ℕ × ℕ}
    (hv : D.TupleMem v) {out₁ out₂ : ℕ × ℕ}
    (h₁ : D.LimFunGraph f v out₁) (h₂ : D.LimFunGraph f v out₂)
    (hout₁ : D.toDomainChain.limMem out₁) (hout₂ : D.toDomainChain.limMem out₂) :
    D.toDomainChain.limEquiv out₁ out₂ := by
  obtain ⟨m₁, src₁, hm₁, hsrc₁, he₁⟩ := h₁
  obtain ⟨m₂, src₂, hm₂, hsrc₂, he₂⟩ := h₂
  have hreal := D.realization_equiv f hv hv
    (fun k ↦ D.toDomainChain.limEquiv_refl _) hm₁ hm₂ hsrc₁ hsrc₂
  have hval₁ : D.toDomainChain.limMem
      (m₁, @Structure.funMap L ℕ (D.stageAt m₁).str n f src₁) :=
    (D.stageAt m₁).domain_closed n f src₁ fun k ↦
      D.mem_domain_of_transport (hv k) (hm₁ k) (hsrc₁ k)
  have hval₂ : D.toDomainChain.limMem
      (m₂, @Structure.funMap L ℕ (D.stageAt m₂).str n f src₂) :=
    (D.stageAt m₂).domain_closed n f src₂ fun k ↦
      D.mem_domain_of_transport (hv k) (hm₂ k) (hsrc₂ k)
  exact D.toDomainChain.limEquiv_trans hout₁ hval₁ hout₂
    (D.toDomainChain.limEquiv_symm he₁)
    (D.toDomainChain.limEquiv_trans hval₁ hval₂ hout₂ hreal he₂)

/-! ### Invariance under pointwise `limEquiv` -/

/-- The limit relation is determined by any single admissible realization. -/
theorem limRelHolds_iff_realization {n : ℕ} (R : L.Relations n) {v : Fin n → ℕ × ℕ}
    (hv : D.TupleMem v) {m : ℕ} {src : Fin n → ℕ}
    (hm : ∀ k, (v k).1 ≤ m)
    (hsrc : ∀ k, src k ∈ D.transportTo (v k).1 m (v k).2) :
    D.LimRelHolds R v ↔ @Structure.RelMap L ℕ (D.stageAt m).str n R src := by
  refine ⟨?_, fun h ↦ ⟨m, src, hm, hsrc, h⟩⟩
  rintro ⟨m', src', hm', hsrc', hR⟩
  exact (D.relMap_realization_iff R hv hv
    (fun k ↦ D.toDomainChain.limEquiv_refl _) hm' hm hsrc' hsrc).1 hR

/-- Invariance of the limit relation under pointwise `limEquiv`. -/
theorem limRelHolds_iff_of_limEquiv {n : ℕ} (R : L.Relations n)
    {v v' : Fin n → ℕ × ℕ} (hv : D.TupleMem v) (hv' : D.TupleMem v')
    (heq : ∀ k, D.toDomainChain.limEquiv (v k) (v' k)) :
    D.LimRelHolds R v ↔ D.LimRelHolds R v' := by
  obtain ⟨src, hsrc, hdom⟩ := D.exists_src hv (le_tupleStage v)
  obtain ⟨src', hsrc', hdom'⟩ := D.exists_src hv' (le_tupleStage v')
  rw [D.limRelHolds_iff_realization R hv (le_tupleStage v) hsrc,
    D.limRelHolds_iff_realization R hv' (le_tupleStage v') hsrc']
  exact D.relMap_realization_iff R hv hv' heq
    (le_tupleStage v) (le_tupleStage v') hsrc hsrc'

/-- Invariance of the limit function graph under pointwise `limEquiv` of the arguments
and `limEquiv` of the output, on valid representatives. -/
theorem limFunGraph_of_limEquiv {n : ℕ} (f : L.Functions n)
    {v v' : Fin n → ℕ × ℕ} {out out' : ℕ × ℕ}
    (hv : D.TupleMem v) (hv' : D.TupleMem v')
    (heq : ∀ k, D.toDomainChain.limEquiv (v k) (v' k))
    (hout : D.toDomainChain.limMem out) (hout' : D.toDomainChain.limMem out')
    (houteq : D.toDomainChain.limEquiv out out')
    (h : D.LimFunGraph f v out) : D.LimFunGraph f v' out' := by
  obtain ⟨m, src, hm, hsrc, he⟩ := h
  obtain ⟨src', hsrc', hdom'⟩ := D.exists_src hv' (le_tupleStage v')
  refine ⟨tupleStage v', src', le_tupleStage v', hsrc', ?_⟩
  have hval' : D.toDomainChain.limMem
      (tupleStage v', @Structure.funMap L ℕ (D.stageAt (tupleStage v')).str n f src') :=
    (D.stageAt (tupleStage v')).domain_closed n f src' hdom'
  have hval : D.toDomainChain.limMem
      (m, @Structure.funMap L ℕ (D.stageAt m).str n f src) :=
    (D.stageAt m).domain_closed n f src fun k ↦
      D.mem_domain_of_transport (hv k) (hm k) (hsrc k)
  have h₁ := D.realization_equiv f hv' hv
    (fun k ↦ D.toDomainChain.limEquiv_symm (heq k))
    (le_tupleStage v') hm hsrc' hsrc
  exact D.toDomainChain.limEquiv_trans hval' hval hout' h₁
    (D.toDomainChain.limEquiv_trans hval hout hout' he houteq)

/-- The two-sided form of function-graph invariance. -/
theorem limFunGraph_iff_of_limEquiv {n : ℕ} (f : L.Functions n)
    {v v' : Fin n → ℕ × ℕ} {out out' : ℕ × ℕ}
    (hv : D.TupleMem v) (hv' : D.TupleMem v')
    (heq : ∀ k, D.toDomainChain.limEquiv (v k) (v' k))
    (hout : D.toDomainChain.limMem out) (hout' : D.toDomainChain.limMem out')
    (houteq : D.toDomainChain.limEquiv out out') :
    D.LimFunGraph f v out ↔ D.LimFunGraph f v' out' :=
  ⟨D.limFunGraph_of_limEquiv f hv hv' heq hout hout' houteq,
    D.limFunGraph_of_limEquiv f hv' hv
      (fun k ↦ D.toDomainChain.limEquiv_symm (heq k)) hout' hout
      (D.toDomainChain.limEquiv_symm houteq)⟩

end CeStructureChainIn

end FirstOrder.Language
