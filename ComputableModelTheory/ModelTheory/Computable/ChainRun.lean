/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ChainTransition

/-!
# The run of the clock-stage recursion, and scheduler agreement

## The run (item 3(d))

`runPart K W i s` iterates the `Part`-valued transition from the one-stage initial state on member
`i`, with the exact recurrence `runPart (s + 1) = (runPart s).bind fun S ↦ stepPart K W S s`. By
induction every returned state satisfies the run invariant (`runInvariant_of_mem_runPart`) and every
stage halts (`runPart_dom`) — from the transition's halting and preservation theorems alone, so
neither scheduled-map actualness nor scheduler fairness is used. The completed run is totalized
**once** (`run`), and `run_computableIn` applies `computableIn_get`; `O ⊆ E` appears only there.

Two links let consumers use the transition's specification without unfolding `.get`: `run_mem`
(the totalized state is a member of `runPart`) and `run_succ_mem` (the next state is a member of
`stepPart` at the current one).

## Scheduler agreement (item 3(e))

The recorded prefixes are persistent (`run_stages_prefix`), so the member-index function of the
constructed chain, `memberIdx K W i s`, is well defined as the member recorded at stage `s`, and the
history of the run at any stage `s` represents it at every `r ≤ s` (`history_agrees`). With that,
`run_fired_eq` proves by induction that the run's fired record at `s` **is** the scheduler's
`(K.requirementDovetail (memberIdx K W i)).fired s`, using `pickFromHistory_eq` and the transition's
fired-record equations. Fairness and one-shot-ness then transfer through this equality rather than
being reproved: `exists_firesAt_of_admissible` (every admissible requirement's encoding eventually
fires in the constructed run) and `firesAt_unique`.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace PartialAgeIn

variable (K : PartialAgeIn O L) (W : PartialCAPWitness E K) (i : ℕ)

/-! ### The run -/

/-- **The run**, `Part`-valued: the initial one-stage state, then the transition at each clock. -/
noncomputable def runPart : ℕ → Part RunState
  | 0 => Part.some (RunState.init K i)
  | s + 1 => (runPart s).bind fun S ↦ stepPart K W S s

@[simp] theorem runPart_zero : runPart K W i 0 = Part.some (RunState.init K i) := rfl

/-- **The recurrence.** -/
theorem runPart_succ (s : ℕ) :
    runPart K W i (s + 1) = (runPart K W i s).bind fun S ↦ stepPart K W S s := rfl

variable {K W i}

/-- **Invariant preservation along the run**, by induction from the transition's preservation. -/
theorem runInvariant_of_mem_runPart : ∀ {s : ℕ} {S : RunState}, S ∈ runPart K W i s →
    K.RunInvariant S s
  | 0, S, h => by
    rw [runPart_zero, Part.mem_some_iff] at h
    subst h
    exact K.runInvariant_init i
  | s + 1, S, h => by
    rw [runPart_succ, Part.mem_bind_iff] at h
    obtain ⟨S₀, h₀, hS⟩ := h
    exact runInvariant_of_mem W (runInvariant_of_mem_runPart h₀) hS

/-- **Halting at every stage**, by induction from the transition's halting. -/
theorem runPart_dom : ∀ s : ℕ, (runPart K W i s).Dom
  | 0 => trivial
  | s + 1 => by
    obtain ⟨S, hS⟩ := Part.dom_iff_mem.1 (runPart_dom s)
    obtain ⟨S', hS'⟩ := Part.dom_iff_mem.1 (stepPart_dom W (runInvariant_of_mem_runPart hS))
    exact Part.dom_iff_mem.2 ⟨S', by rw [runPart_succ]; exact Part.mem_bind_iff.2 ⟨S, hS, hS'⟩⟩

/-- The run is partial recursive in the clock, by primitive recursion over the transition. -/
theorem runPart_recursiveIn (hOE : O ⊆ E) : RecursiveIn E (runPart K W i) := by
  have hstep : RecursiveIn₂ E fun (_ : ℕ) (p : ℕ × RunState) ↦ stepPart K W p.2 p.1 :=
    (RecursiveIn.comp (α := ℕ × (ℕ × RunState)) (β := RunState × ℕ) (σ := RunState)
      (f := fun p ↦ stepPart K W p.1 p.2) (g := fun x ↦ (x.2.2, x.2.1))
      (stepPart_recursiveIn W hOE)
      (ComputableIn.pair (α := ℕ × (ℕ × RunState)) (β := RunState) (γ := ℕ) (f := fun x ↦ x.2.2)
        (g := fun x ↦ x.2.1) (ComputableIn.snd.comp ComputableIn.snd)
        (ComputableIn.fst.comp ComputableIn.snd)))
  have h := RecursiveIn.nat_rec (O := E) (α := ℕ) (σ := RunState) (f := fun s ↦ s)
    (g := fun _ ↦ Part.some (RunState.init K i)) (h := fun _ p ↦ stepPart K W p.2 p.1)
    ComputableIn.id (RecursiveIn.comp RecursiveIn.some (ComputableIn.const (RunState.init K i)))
    hstep
  refine h.of_eq fun s ↦ ?_
  induction s with
  | zero => rfl
  | succ s ih => rw [runPart_succ, ← ih]

/-- **The totalized run.** -/
noncomputable def run (K : PartialAgeIn O L) (W : PartialCAPWitness E K) (i : ℕ) (s : ℕ) :
    RunState :=
  (runPart K W i s).get (runPart_dom s)

/-- **Link 1**: the totalized state is a member of the partial run. -/
theorem run_mem (s : ℕ) : run K W i s ∈ runPart K W i s := Part.get_mem _

theorem mem_runPart_iff {s : ℕ} {S : RunState} : S ∈ runPart K W i s ↔ S = run K W i s :=
  ⟨fun h ↦ Part.mem_unique h (run_mem s), fun h ↦ h ▸ run_mem s⟩

theorem run_zero : run K W i 0 = RunState.init K i :=
  (Part.mem_some_iff.1 (run_mem (K := K) (W := W) (i := i) 0))

/-- **Link 2**: the next state is a member of the transition at the current state. -/
theorem run_succ_mem (s : ℕ) : run K W i (s + 1) ∈ stepPart K W (run K W i s) s := by
  have h := run_mem (K := K) (W := W) (i := i) (s + 1)
  rw [runPart_succ, Part.mem_bind_iff] at h
  obtain ⟨S, hS, h'⟩ := h
  rwa [Part.mem_unique hS (run_mem s)] at h'

theorem run_runInvariant (s : ℕ) : K.RunInvariant (run K W i s) s :=
  runInvariant_of_mem_runPart (run_mem s)

/-- **The run is computable** in the clock, at any oracle reading the family and running the
selector: totalization by `computableIn_get`. -/
theorem run_computableIn (hOE : O ⊆ E) : ComputableIn E (run K W i) :=
  RecursiveIn.computableIn_get (runPart_recursiveIn hOE) runPart_dom

/-! ### Persistent prefixes and the member-index function -/

/-- One clock step only appends to the recorded prefix. -/
theorem run_stages_prefix_succ (s : ℕ) : (run K W i s).stages <+: (run K W i (s + 1)).stages := by
  rcases (mem_stepPart_iff K W).1 (run_succ_mem s) with ⟨-, h⟩ | ⟨e, -, q, -, δ, -, F, -, D, -, h⟩
  · rw [h, stages_identityExtension]; exact List.prefix_append _ _
  · rw [h, RunState.stages_capExtension]; exact List.prefix_append _ _

/-- **Persistence**: recorded prefixes are never revised. -/
theorem run_stages_prefix {s t : ℕ} (h : s ≤ t) :
    (run K W i s).stages <+: (run K W i t).stages := by
  induction t, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ t _ ih => exact ih.trans (run_stages_prefix_succ t)

theorem run_stages_length (s : ℕ) : (run K W i s).stages.length = s + 1 :=
  (run_runInvariant s).length

/-- The record at stage `r` is fixed from clock `r` on. -/
theorem run_getElem?_eq {r s : ℕ} (hrs : r ≤ s) :
    (run K W i s).stages[r]? = (run K W i r).stages[r]? := by
  have hlt : r < (run K W i r).stages.length := by rw [run_stages_length]; omega
  rw [List.getElem?_eq_getElem hlt,
    List.getElem?_eq_getElem (by rw [run_stages_length]; omega)]
  exact congrArg some ((run_stages_prefix hrs).getElem hlt).symm

variable (K W i)

/-- **The member-index function of the constructed chain**: the member recorded at stage `s`. -/
noncomputable def memberIdx (s : ℕ) : ℕ := (run K W i s).currentMember s

variable {K W i}

/-- **History agreement**: at any clock `s`, the run's history represents `memberIdx` at every
`r ≤ s`. -/
theorem history_agrees (s : ℕ) : ∀ r ≤ s,
    (stageHistory (run K W i s).stages)[r]? = some (memberIdx K W i r) := by
  intro r hr
  obtain ⟨rec, hrec⟩ := (run_runInvariant (K := K) (W := W) (i := i) r).exists_getElem? le_rfl
  rw [stageHistory_getElem?, run_getElem?_eq hr, hrec, memberIdx, RunState.currentMember,
    (run_runInvariant r).dHist_eq hrec]
  rfl

/-! ### Scheduler agreement -/

variable (K W i)

/-- The dovetailing scheduler at the constructed member-index function. -/
noncomputable abbrev schedule : DovetailAvail := K.requirementDovetail (memberIdx K W i)

variable {K W i}

/-- Selection in the run is the scheduler's selection, given the fired records agree. -/
theorem run_pick_eq (s : ℕ) (hf : (run K W i s).fired = (schedule K W i).fired s) :
    K.pickFromHistory (stageHistory (run K W i s).stages) (run K W i s).fired s =
      (schedule K W i).pick ((schedule K W i).fired s) s := by
  rw [hf]
  exact K.pickFromHistory_eq (history_agrees s) _

/-- **Fired-record agreement**: the run's fired record is the scheduler's, at every clock. -/
theorem run_fired_eq : ∀ s : ℕ, (run K W i s).fired = (schedule K W i).fired s
  | 0 => by rw [run_zero]; rfl
  | s + 1 => by
    have hpick := run_pick_eq (K := K) (W := W) (i := i) s (run_fired_eq s)
    rcases (mem_stepPart_iff K W).1 (run_succ_mem s) with
      ⟨hnone, h⟩ | ⟨e, hsome, q, -, δ, -, F, -, D, -, h⟩
    · rw [hpick] at hnone
      rw [h, fired_identityExtension, run_fired_eq s, (schedule K W i).fired_succ_of_none hnone]
    · rw [hpick] at hsome
      rw [h, RunState.fired_capExtension, run_fired_eq s,
        (schedule K W i).fired_succ_of_some (show (schedule K W i).FiresAt e s from hsome)]

/-- Selection in the run is the scheduler's selection. -/
theorem run_pick (s : ℕ) :
    K.pickFromHistory (stageHistory (run K W i s).stages) (run K W i s).fired s =
      (schedule K W i).pick ((schedule K W i).fired s) s :=
  run_pick_eq s (run_fired_eq s)

/-- **Firing in the run**: the scheduler fires `e` at `s` iff the run's transition at `s` selected
`e`, iff the fired record grows by exactly `e`. -/
theorem firesAt_iff_pick {e s : ℕ} :
    (schedule K W i).FiresAt e s ↔
      K.pickFromHistory (stageHistory (run K W i s).stages) (run K W i s).fired s = some e := by
  rw [run_pick]; rfl

theorem firesAt_iff_fired {e s : ℕ} :
    (schedule K W i).FiresAt e s ↔ (run K W i (s + 1)).fired = (run K W i s).fired ++ [e] := by
  rw [run_fired_eq, run_fired_eq]
  constructor
  · exact (schedule K W i).fired_succ_of_some
  · intro h
    rcases hp : (schedule K W i).pick ((schedule K W i).fired s) s with _ | e'
    · rw [(schedule K W i).fired_succ_of_none hp] at h
      have := congrArg List.length h
      simp at this
    · rw [(schedule K W i).fired_succ_of_some (show (schedule K W i).FiresAt e' s from hp)] at h
      obtain rfl := List.singleton_inj.1 (List.append_cancel_left h)
      exact hp

/-- **Fairness, transferred**: every requirement admissible for the constructed chain has its
encoding fire at some stage of the run. -/
theorem exists_firesAt_of_admissible {q : RequirementData}
    (hq : K.Admissible (memberIdx K W i) q) : ∃ s, (schedule K W i).FiresAt (encode q) s :=
  K.admissible_eventually_fires _ hq

/-- **One-shot, transferred**: a code fires at most once in the run. -/
theorem firesAt_unique {e s t : ℕ} (hs : (schedule K W i).FiresAt e s)
    (ht : (schedule K W i).FiresAt e t) : s = t :=
  (schedule K W i).fires_at_most_once hs ht

/-- **A firing stage in the run is a firing step of the transition**: the next state is the CAP
extension of the current one by a diagram on the transported span of the decoded requirement. -/
theorem exists_capExtension_of_firesAt {e s : ℕ} (h : (schedule K W i).FiresAt e s) :
    ∃ q : RequirementData, (decode e : Option RequirementData) = some q ∧
      ∃ δ ∈ K.transportPart (run K W i s).stages q.chainStage s,
        ∃ F ∈ K.compPart δ (q.chainMap (run K W i s).dHist),
          ∃ D ∈ W.sel (PotentialSpanData.ofPair (F, q.targetMap)),
            run K W i (s + 1) = (run K W i s).capExtension e D := by
  have hp := firesAt_iff_pick.1 h
  rcases (mem_stepPart_iff K W).1 (run_succ_mem s) with
    ⟨hnone, -⟩ | ⟨e', hsome, q, hq, δ, hδ, F, hF, D, hD, hS'⟩
  · rw [hp] at hnone; exact absurd hnone (by simp)
  · rw [hp] at hsome
    obtain rfl := Option.some.inj hsome
    exact ⟨q, hq, δ, hδ, F, hF, D, hD, hS'⟩

end PartialAgeIn

end FirstOrder.Language
