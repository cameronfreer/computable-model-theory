/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.RecursiveIn

/-!
# Staged partial computations, as supplied data

`RecursiveIn O` is **extensional**: it says a partial function is computable in an oracle, and
nothing more. It gives no bounded interpreter, so it cannot express "run this procedure while
simultaneously searching for evidence against it" — which is what a priority construction does at
every step. `StagedPartialIn` is the missing intensional layer: an explicit stage-indexed
approximation, uniformly computable, sound, monotone, and complete.

## It is supplied, never derived

**There is deliberately no theorem `RecursiveIn O f → StagedPartialIn O f`, and none should be
added here.** That implication is a relativized oracle-machine representation theorem — the
relativized analogue of going through `Nat.Partrec.Code.evaln` — and it is a separate obligation
with its own content. Stating the layer against *supplied* staged data keeps that obligation
visible instead of assumed; a consumer that needs staging says so in its hypotheses, exactly as
consumers of `InfinitudeCertificate` and `UniformEvaluatorsIn` already do.

The same discipline explains what is *not* in this file: no racing, no dovetailing, no merge. Those
are consumers, and they land separately.

## The extensional API

Everything a consumer should need about the *values* is here:

* `mem_iff_exists_approx` — membership in the partial function is exactly discovery at some stage;
* `dom_iff_exists_approx` — halting is exactly discovery of *something* at some stage;
* `approx_of_le` — persistence: a discovery at stage `s` survives to every later stage;
* `approx_unique` — and it is the only discovery, at any stage.

Together these say the approximation determines `f` and nothing about `f` determines a *stage* —
which is the honest asymmetry. Two staged approximations of the same function may discover the same
value at wildly different stages, and any construction that races them is choosing between
*presentations*, not between functions. That is why the first consumer has to fix a discovery rule
rather than read off a current-stage value.
-/

open Encodable

variable {α β : Type*} [Primcodable α] [Primcodable β]

/-- **A staged computation of a partial function**: an explicit, uniformly computable, monotone
approximation that is sound and complete for `f`.

Supplied data. Nothing in this file derives one from `RecursiveIn O f`; see the module docstring. -/
structure StagedPartialIn (O : Set (ℕ →. ℕ)) (f : α →. β) where
  /-- What has been discovered by stage `s`. -/
  approx : ℕ → α → Option β
  /-- The approximation is computable uniformly in the stage. -/
  approx_computableIn : ComputableIn O fun p : ℕ × α ↦ approx p.1 p.2
  /-- Discoveries are correct. -/
  sound : ∀ {s x y}, approx s x = some y → y ∈ f x
  /-- Discoveries persist. -/
  monotone : ∀ {s t x y}, s ≤ t → approx s x = some y → approx t x = some y
  /-- Every value is eventually discovered. -/
  complete : ∀ {x y}, y ∈ f x → ∃ s, approx s x = some y

namespace StagedPartialIn

variable {O : Set (ℕ →. ℕ)} {f : α →. β} (F : StagedPartialIn O f)

/-! ### The extensional API -/

/-- **Persistence.** A discovery at stage `s` is still there at every later stage. -/
theorem approx_of_le {s t x y} (h : s ≤ t) (hs : F.approx s x = some y) :
    F.approx t x = some y :=
  F.monotone h hs

/-- **Membership is discovery.** -/
theorem mem_iff_exists_approx {x : α} {y : β} : y ∈ f x ↔ ∃ s, F.approx s x = some y :=
  ⟨F.complete, fun ⟨_, h⟩ ↦ F.sound h⟩

/-- **Halting is discovery of something.** -/
theorem dom_iff_exists_approx {x : α} : (f x).Dom ↔ ∃ s y, F.approx s x = some y := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 h
    obtain ⟨s, hs⟩ := F.complete hy
    exact ⟨s, y, hs⟩
  · rintro ⟨s, y, hs⟩
    exact Part.dom_iff_mem.2 ⟨y, F.sound hs⟩

/-- **Discoveries never disagree**, at any two stages: `f` is a partial *function*, and soundness
puts both values in it. -/
theorem approx_unique {s t x y z} (hs : F.approx s x = some y) (ht : F.approx t x = some z) :
    y = z :=
  Part.mem_unique (F.sound hs) (F.sound ht)

/-- Two stages that both discover something discover the same thing — the `Option` form. -/
theorem approx_eq_of_isSome {s t x} (hs : (F.approx s x).isSome) (ht : (F.approx t x).isSome) :
    F.approx s x = F.approx t x := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 ht
  rw [hy, hz, F.approx_unique hy hz]

/-- Discovery is upward closed in the stage, stated on `isSome`. -/
theorem isSome_of_le {s t x} (h : s ≤ t) (hs : (F.approx s x).isSome) :
    (F.approx t x).isSome := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
  rw [F.approx_of_le h hy]
  rfl

/-- Off the domain nothing is ever discovered. -/
theorem approx_eq_none_of_not_dom {x : α} (h : ¬ (f x).Dom) (s : ℕ) : F.approx s x = none := by
  rcases hx : F.approx s x with - | y
  · rfl
  · exact absurd (F.dom_iff_exists_approx.2 ⟨s, y, hx⟩) h

end StagedPartialIn
