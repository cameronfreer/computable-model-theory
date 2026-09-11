/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CeStructureLimit
import ComputableModelTheory.ModelTheory.Computable.CeStructureOmegaLimit

/-!
# Finite-tuple exhaustion: every finite tuple of the limit lies in one stage

Theorem 3.9's homogeneity half opens with "find an `r` such that all coordinates of `d⃗` and `c⃗`
lie in `A_{d(r)}`". That is a statement about the ω-limit, not about the schedule: the chain
exhausts the limit, so finitely many limit elements, each a stage image, are all images of a single
later stage, by transporting each to the maximum of their stages. It is a separate prerequisite
(contract §7), proved here on its own from the limit's coverage and its transport coherence.

Three forms, one proof each:

* `LimitIn.exists_stage_list` / `exists_stage_tuple` — Level 1, on the limit presentation's
  carrier (the accepted codes);
* `LimitIn.exists_omegaStage_list` / `exists_omegaStage_tuple` — the all-ℕ ω structure, under the
  infinitude certificate that coverage of ω requires;
* `exists_stageIntoLimit_tuple` — the semantic limit.

The stage is obtained classically as a maximum; nothing here is a search procedure. The list forms
are proved by induction on the list, moving the accumulated stage up one transport at a time; the
`Fin`-indexed forms are read off the list forms.
-/

open FirstOrder Language

namespace FirstOrder.Language

namespace CeStructureChainIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage] {D : CeStructureChainIn O L}

/-- Transport a stage-`i` element up to a later stage: the value exists and lies in that stage. -/
theorem exists_transport_mem {i j x : ℕ} (hij : i ≤ j) (hx : x ∈ (D.stageAt i).domain) :
    ∃ y ∈ D.transportTo i j x, y ∈ (D.stageAt j).domain :=
  D.toDomainChain.transportTo_dom j hij hx

namespace LimitIn

variable (Z : D.LimitIn)

/-! ### Level 1: the limit presentation -/

/-- **Every finite list of limit elements lies in one stage** (Level 1). -/
theorem exists_stage_list (l : List Z.presentation.domain) :
    ∃ i : ℕ, ∀ c ∈ l, ∃ (x : ℕ) (hx : x ∈ (D.stageAt i).domain),
      Z.stageEmbedding i ⟨x, hx⟩ = c := by
  induction l with
  | nil => exact ⟨0, fun _ h ↦ (List.not_mem_nil h).elim⟩
  | cons c l ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, x, hx, hc⟩ := Z.coverage c
    refine ⟨max i j, fun c' hc' ↦ ?_⟩
    rcases List.mem_cons.1 hc' with rfl | hc'
    · obtain ⟨y, hy, hydom⟩ := exists_transport_mem (le_max_right i j) hx
      obtain ⟨hy', heq⟩ := Z.stageEmbedding_transport (le_max_right i j) hx hy
      exact ⟨y, hy', heq ▸ hc⟩
    · obtain ⟨x', hx', hc''⟩ := hi c' hc'
      obtain ⟨y, hy, hydom⟩ := exists_transport_mem (le_max_left i j) hx'
      obtain ⟨hy', heq⟩ := Z.stageEmbedding_transport (le_max_left i j) hx' hy
      exact ⟨y, hy', heq ▸ hc''⟩

/-- **Every finite tuple of limit elements lies in one stage** (Level 1), as a tuple of stage
elements. -/
theorem exists_stage_tuple {n : ℕ} (v : Fin n → Z.presentation.domain) :
    ∃ (i : ℕ) (w : Fin n → ℕ) (hw : ∀ k, w k ∈ (D.stageAt i).domain),
      ∀ k, Z.stageEmbedding i ⟨w k, hw k⟩ = v k := by
  obtain ⟨i, hi⟩ := Z.exists_stage_list (List.ofFn v)
  choose w hw heq using fun k ↦ hi (v k) (List.mem_ofFn.2 ⟨k, rfl⟩)
  exact ⟨i, w, hw, heq⟩

/-! ### The ω structure -/

/-- **Every finite list of naturals lies in one stage of the ω structure**, under the infinitude
certificate coverage of ω requires. -/
theorem exists_omegaStage_list (cert : Z.presentation.InfinitudeCertificate) (l : List ℕ) :
    ∃ i : ℕ, ∀ m ∈ l, ∃ (x : ℕ) (hx : x ∈ (D.stageAt i).domain),
      Z.omegaStageEmbedding i ⟨x, hx⟩ = m := by
  induction l with
  | nil => exact ⟨0, fun _ h ↦ (List.not_mem_nil h).elim⟩
  | cons m l ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, x, hx, hm⟩ := Z.exists_omegaStageEmbedding_eq cert m
    refine ⟨max i j, fun m' hm' ↦ ?_⟩
    rcases List.mem_cons.1 hm' with rfl | hm'
    · obtain ⟨y, hy, -⟩ := exists_transport_mem (le_max_right i j) hx
      obtain ⟨hy', heq⟩ := Z.omegaStageEmbedding_transport (le_max_right i j) hx hy
      exact ⟨y, hy', heq ▸ hm⟩
    · obtain ⟨x', hx', hm''⟩ := hi m' hm'
      obtain ⟨y, hy, -⟩ := exists_transport_mem (le_max_left i j) hx'
      obtain ⟨hy', heq⟩ := Z.omegaStageEmbedding_transport (le_max_left i j) hx' hy
      exact ⟨y, hy', heq ▸ hm''⟩

/-- **Every finite tuple of naturals lies in one stage of the ω structure.** This is the statement
Theorem 3.9's homogeneity half opens with. -/
theorem exists_omegaStage_tuple (cert : Z.presentation.InfinitudeCertificate) {n : ℕ}
    (v : Fin n → ℕ) :
    ∃ (i : ℕ) (w : Fin n → ℕ) (hw : ∀ k, w k ∈ (D.stageAt i).domain),
      ∀ k, Z.omegaStageEmbedding i ⟨w k, hw k⟩ = v k := by
  obtain ⟨i, hi⟩ := Z.exists_omegaStage_list cert (List.ofFn v)
  choose w hw heq using fun k ↦ hi (v k) (List.mem_ofFn.2 ⟨k, rfl⟩)
  exact ⟨i, w, hw, heq⟩

end LimitIn

/-! ### The semantic limit -/

/-- **Every finite tuple of the semantic limit lies in one stage.** -/
theorem exists_stageIntoLimit_tuple {n : ℕ} (v : Fin n → D.Limit) :
    ∃ (i : ℕ) (w : Fin n → ℕ) (hw : ∀ k, w k ∈ (D.stageAt i).domain),
      ∀ k, D.stageIntoLimit i (w k) (hw k) = v k := by
  suffices h : ∀ l : List D.Limit, ∃ i : ℕ, ∀ q ∈ l,
      ∃ (x : ℕ) (hx : x ∈ (D.stageAt i).domain), D.stageIntoLimit i x hx = q by
    obtain ⟨i, hi⟩ := h (List.ofFn v)
    choose w hw heq using fun k ↦ hi (v k) (List.mem_ofFn.2 ⟨k, rfl⟩)
    exact ⟨i, w, hw, heq⟩
  intro l
  induction l with
  | nil => exact ⟨0, fun _ h ↦ (List.not_mem_nil h).elim⟩
  | cons q l ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, x, hx, hq⟩ := D.exists_stageIntoLimit q
    refine ⟨max i j, fun q' hq' ↦ ?_⟩
    rcases List.mem_cons.1 hq' with rfl | hq'
    · obtain ⟨y, hy, hydom⟩ := exists_transport_mem (le_max_right i j) hx
      exact ⟨y, hydom,
        (D.stageIntoLimit_transport (le_max_right i j) hx hydom hy).symm.trans hq.symm⟩
    · obtain ⟨x', hx', hq''⟩ := hi q' hq'
      obtain ⟨y, hy, hydom⟩ := exists_transport_mem (le_max_left i j) hx'
      exact ⟨y, hydom,
        (D.stageIntoLimit_transport (le_max_left i j) hx' hydom hy).symm.trans hq''⟩

end CeStructureChainIn

end FirstOrder.Language
