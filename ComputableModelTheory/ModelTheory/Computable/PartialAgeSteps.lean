/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialAge

/-!
# Enumeration steps and on-domain tuples

The re-indexing of an empty-capable family must range over tuples **of member
elements**, not over raw tuples of naturals: a variable term realizes directly to its
tuple entry, so a raw off-domain entry would leak an element outside the member's
carrier. Two dual operations make on-domain tuples first-class through their
enumeration-step indices:

* `tupleAtSteps i steps` — the tuple `steps.filterMap (enum? i)`, always on-domain;
* `stepsForTuple i s` — a partial search for enumeration witnesses of each entry of
  `s`, halting exactly when every entry lies in member `i`'s carrier.

`stepsForTuple` is a partial right-inverse of `tupleAtSteps`
(`tupleAtSteps_of_mem_stepsForTuple`): on its domain the recovered steps reproduce `s`.
The halting characterization is stated only in the direction the presentation contract
justifies — `stepsForTuple` is built from the enumeration, so it halts **exactly** on
on-domain tuples; no claim is made about the stored evaluators off-domain. This partial
inverse serves both same-class reappearance and the CHP selector.

Uniform computability of these operations (`tupleAtSteps` computable in the oracle,
`firstStepFor`/`stepsForTuple` partial recursive, all uniformly in the index) is
established below as public results, so the re-indexed family and the CHP selector can
reuse them. `stepsForTuple` is kept partial recursive with its exact domain theorem —
never totalized.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (A : PartialAgeIn O L)

/-- The tuple presented by a list of enumeration-step indices in member `i`:
enumeration steps that produce nothing are dropped. Always on-domain. -/
def tupleAtSteps (i : ℕ) (steps : List ℕ) : List ℕ :=
  steps.filterMap (A.enum? i)

/-- The least enumeration step producing `x` in member `i` — a per-element witness
search. -/
noncomputable def firstStepFor (i x : ℕ) : Part ℕ :=
  Nat.rfind fun m ↦ Part.some (decide (A.enum? i m = Option.some x))

/-- Step indices realizing a tuple entry by entry; halts exactly when every entry lies
in the member's carrier. -/
noncomputable def stepsForTuple (i : ℕ) (s : List ℕ) : Part (List ℕ) :=
  listMapPart (A.firstStepFor i) s

/-! ### `tupleAtSteps` produces on-domain tuples -/

/-- Every entry of `tupleAtSteps` lies in the member's carrier. -/
theorem mem_domainAt_of_mem_tupleAtSteps {i : ℕ} {steps : List ℕ} {x : ℕ}
    (hx : x ∈ A.tupleAtSteps i steps) : x ∈ A.domainAt i := by
  rw [tupleAtSteps, List.mem_filterMap] at hx
  obtain ⟨m, -, hm⟩ := hx
  exact ⟨m, hm⟩

theorem tupleAtSteps_forall_mem_domainAt {i : ℕ} (steps : List ℕ) :
    ∀ x ∈ A.tupleAtSteps i steps, x ∈ A.domainAt i :=
  fun _ hx ↦ A.mem_domainAt_of_mem_tupleAtSteps hx

/-- Every on-domain tuple is `tupleAtSteps` of some step list. -/
theorem exists_steps_of_forall_mem_domainAt {i : ℕ} {s : List ℕ}
    (hs : ∀ x ∈ s, x ∈ A.domainAt i) :
    ∃ steps, A.tupleAtSteps i steps = s := by
  induction s with
  | nil => exact ⟨[], rfl⟩
  | cons x t ih =>
    obtain ⟨m, hm⟩ := hs x (List.mem_cons_self)
    obtain ⟨steps, hsteps⟩ := ih fun y hy ↦ hs y (List.mem_cons_of_mem x hy)
    refine ⟨m :: steps, ?_⟩
    rw [tupleAtSteps, List.filterMap_cons_some hm]
    rw [show steps.filterMap (A.enum? i) = A.tupleAtSteps i steps from rfl, hsteps]

/-! ### `firstStepFor` halts exactly on-domain -/

/-- The witness search halts exactly when the element lies in the member's carrier. -/
theorem firstStepFor_dom_iff {i x : ℕ} :
    (A.firstStepFor i x).Dom ↔ x ∈ A.domainAt i := by
  have h := Nat.rfind_some_dom_iff
    (f := fun (y : ℕ) k ↦ decide (A.enum? i k = Option.some y)) (a := x)
  rw [firstStepFor]
  exact h.trans
    ⟨fun ⟨n, hn⟩ ↦ ⟨n, of_decide_eq_true hn⟩, fun ⟨n, hn⟩ ↦ ⟨n, decide_eq_true hn⟩⟩

/-- A returned step actually enumerates the element. -/
theorem enum?_of_mem_firstStepFor {i x m : ℕ} (h : m ∈ A.firstStepFor i x) :
    A.enum? i m = Option.some x := by
  rw [firstStepFor, Nat.mem_rfind] at h
  exact of_decide_eq_true (Part.mem_some_iff.1 h.1).symm

/-! ### `stepsForTuple` and the partial inverse -/

/-- The step search halts exactly on on-domain tuples. -/
theorem stepsForTuple_dom_iff {i : ℕ} {s : List ℕ} :
    (A.stepsForTuple i s).Dom ↔ ∀ x ∈ s, x ∈ A.domainAt i := by
  rw [stepsForTuple, listMapPart_dom_iff]
  exact forall₂_congr fun x _ ↦ A.firstStepFor_dom_iff

/-- On its domain, the recovered steps reproduce the tuple: `stepsForTuple` is a
partial right-inverse of `tupleAtSteps`. -/
theorem tupleAtSteps_of_mem_stepsForTuple {i : ℕ} {s steps : List ℕ}
    (h : steps ∈ A.stepsForTuple i s) : A.tupleAtSteps i steps = s := by
  rw [stepsForTuple, mem_listMapPart_iff] at h
  rw [tupleAtSteps]
  induction h with
  | nil => rfl
  | @cons x m t stepsTail hmem _ ih =>
    rw [List.filterMap_cons_some (A.enum?_of_mem_firstStepFor hmem), ih]

/-- Combined: the step search halts on on-domain tuples and returns steps recovering
them. -/
theorem exists_mem_stepsForTuple {i : ℕ} {s : List ℕ}
    (hs : ∀ x ∈ s, x ∈ A.domainAt i) :
    ∃ steps ∈ A.stepsForTuple i s, A.tupleAtSteps i steps = s := by
  obtain ⟨steps, hsteps⟩ := Part.dom_iff_mem.1 ((A.stepsForTuple_dom_iff).2 hs)
  exact ⟨steps, hsteps, A.tupleAtSteps_of_mem_stepsForTuple hsteps⟩

/-! ### Uniform computability

Public, so the CHP construction can reuse them. Two elaboration hazards, both crossed by
staying in explicit natural-number encodings: `Option`-equality (`Primrec.eq (α := Option ℕ)`)
and `option_casesOn` both diverge at `whnf` here, so the enumeration comparison goes
through `encode` and `Nat`-equality, and the fold step through `Option.map`/`getD` rather
than a case split. Composing the oracle-computable `enum?` with plain projections is
fine at any product depth; it is `Nat.unpair` (whose `ℕ × ℕ` output reopens the
Primcodable machinery) that must be avoided. -/

/-- The witness search is partial recursive uniformly in the member and element. -/
theorem firstStepFor_recursiveIn :
    RecursiveIn O fun p : ℕ × ℕ ↦ A.firstStepFor p.1 p.2 := by
  have hpred : ComputableIn O fun q : (ℕ × ℕ) × ℕ ↦
      decide (A.enum? q.1.1 q.2 = Option.some q.1.2) := by
    have he : ComputableIn O fun q : (ℕ × ℕ) × ℕ ↦ A.enum? q.1.1 q.2 :=
      A.enum?_computableIn.comp
        ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd)
    have hs : ComputableIn O fun q : (ℕ × ℕ) × ℕ ↦ (Option.some q.1.2 : Option ℕ) :=
      ComputableIn.option_some.comp (ComputableIn.snd.comp ComputableIn.fst)
    exact (((Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂ (O := O)).comp
      (ComputableIn.encode.comp he) (ComputableIn.encode.comp hs)).of_eq
      fun _ ↦ (decide_eq_decide).2 Encodable.encode_inj
  unfold firstStepFor
  exact RecursiveIn.rfind_total (f := fun (p : ℕ × ℕ) (m : ℕ) ↦
    decide (A.enum? p.1 m = Option.some p.2)) hpred

/-- The step search is partial recursive uniformly in the member and tuple. Its exact
domain theorem is `stepsForTuple_dom_iff`; it is never totalized. -/
theorem stepsForTuple_recursiveIn :
    RecursiveIn O fun p : ℕ × List ℕ ↦ A.stepsForTuple p.1 p.2 := by
  unfold stepsForTuple
  exact RecursiveIn.listMapPart₂ (g := A.firstStepFor) A.firstStepFor_recursiveIn

/-- `tupleAtSteps` is computable uniformly in the member and step list. -/
theorem tupleAtSteps_computableIn :
    ComputableIn O fun p : ℕ × List ℕ ↦ A.tupleAtSteps p.1 p.2 := by
  have hmap : ComputableIn O fun r : (ℕ × List ℕ) × ℕ × List ℕ ↦
      (A.enum? r.1.1 r.2.1).map (· :: r.2.2) :=
    ComputableIn.option_map
      (A.enum?_computableIn.comp
        ((ComputableIn.fst.comp ComputableIn.fst).pair
          (ComputableIn.fst.comp ComputableIn.snd)))
      ((Computable.list_cons.computableIn₂ (O := O)).comp ComputableIn.snd
        (ComputableIn.snd.comp (ComputableIn.snd.comp ComputableIn.fst))).to₂
  have hstep : ComputableIn₂ O fun (p : ℕ × List ℕ) (bs : ℕ × List ℕ) ↦
      ((A.enum? p.1 bs.1).map (· :: bs.2)).getD bs.2 :=
    (ComputableIn.option_getD hmap (ComputableIn.snd.comp ComputableIn.snd)).to₂
  refine (ComputableIn.list_foldr ComputableIn.snd (ComputableIn.const [])
    hstep).of_eq fun p ↦ ?_
  obtain ⟨i, l⟩ := p
  rw [tupleAtSteps]
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ih]
    rcases h : A.enum? i a with - | b
    · rw [List.filterMap_cons_none h]; simp
    · rw [List.filterMap_cons_some h]; simp

end PartialAgeIn

end FirstOrder.Language
