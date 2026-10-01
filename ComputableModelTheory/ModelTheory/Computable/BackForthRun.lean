/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.BackForth

/-!
# The run — CHMM Proposition 3.2, the stage recursion

Both half-steps, iterated. One **round** at stage `n` performs *both* halves with the same `n`: the
forth step matches the source point `n`, and the back step — on the state the forth step produced —
matches the target point `n`. The run is `Nat.rec` over rounds, starting from a supplied initial
state `s₀` — Proposition 3.2 starts from `empty`, Corollary 3.5 from a prescribed match.

## Not parity alternation

Every successor performs both halves. A scheme that alternated on parity — forth at even stages,
back at odd — would need `n / 2` as the point to match and would leave the two tuples at different
lengths between stages. Here each tuple of `stateAt s₀ n` has its initial length plus `2 * n`, and
after stage `n + 1` the number `n` is present on *both* sides: at source position
`s₀.sourceTuple.length + 2 * n` because the forth half pushed it there, and at target position
`s₀.targetTuple.length + 2 * n + 1` because the back half did. Those two positions are what the
eventual surjectivity arguments consume, and they are deliberately different. On a matched seed the
two initial lengths agree, so both offsets are the seed length `ℓ`; from `empty` they are `0`.

## The seed

The initial state is arbitrary data. Only `stateAt_matched` needs it to be matched, and nothing else
in this module looks at it: the half-steps assume only that the *current* state is matched. The run
only appends, so every coordinate of the seed — repeated ones included — survives at every stage.

## Persistence

`stateAt` never revises: each round appends, so every earlier stage's tuple is a prefix of every
later one. That is the load-bearing input for the total maps — a value read at some stage stays
readable, at the same position, forever. It is proved from the append equations, not from lookup
arithmetic, so the two-entry step is stated once and the general `m ≤ n` case is transitivity.

## Effectivity

The whole run is computable in the **map** oracle `E`. The presentation oracle is never consulted
and no inclusion between them is assumed, which is inherited from the two half-steps: this module
adds only `Nat.rec`, whose base case is the fixed seed (a constant).

Stopping here. The total maps — the common-later-stage lookup lemmas, and the inverse and structure
laws — are their own unit.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

section Run

variable {E : Set (ℕ →. ℕ)} {S T : ComputableStructureIn O L}
  (r : RepresentationCoverIn E S.canonicalAge T.canonicalAge)
  (rb : RepresentationCoverIn E T.canonicalAge S.canonicalAge)
  (H : ComputablyHomogeneousIn E T) (Hs : ComputablyHomogeneousIn E S) (s₀ : BackForthState)

namespace BackForthState

/-! ### One round -/

/-- **A round at stage `n`**: forth at `n`, then back at `n` on the state the forth half produced.
Both halves run at the *same* `n`. -/
noncomputable def roundState (n : ℕ) (s : BackForthState) : BackForthState :=
  backState rb (forthState r s n H) n Hs

/-- The point the **forth** half chose for the target side. Note it does not depend on the backward
cover or the source's homogeneity: the forth half is complete before the back half starts. -/
noncomputable def roundForthPoint (n : ℕ) (s : BackForthState) : ℕ :=
  H.imageOfNewPoint (forthQuery r s n)

/-- The point the **back** half chose for the source side. This one depends on all four pieces of
data, because the query it answers is asked about the state the forth half produced. -/
noncomputable def roundBackPoint (n : ℕ) (s : BackForthState) : ℕ :=
  Hs.imageOfNewPoint (backQuery rb (forthState r s n H) n)

/-- **The source append**: the pushed point `n` first, then the point the back half chose. -/
@[simp] theorem roundState_sourceTuple (n : ℕ) (s : BackForthState) :
    (roundState r rb H Hs n s).sourceTuple
      = s.sourceTuple ++ [n, roundBackPoint r rb H Hs n s] := by
  change (s.sourceTuple ++ [n]) ++ [roundBackPoint r rb H Hs n s] = _
  rw [List.append_assoc]
  rfl

/-- **The target append**: the point the forth half chose first, then the pushed point `n`. The two
new entries appear in the opposite order from the source side — that is what puts `n` at source
position `2 * k` and at target position `2 * k + 1`. -/
@[simp] theorem roundState_targetTuple (n : ℕ) (s : BackForthState) :
    (roundState r rb H Hs n s).targetTuple
      = s.targetTuple ++ [roundForthPoint r H n s, n] := by
  change (s.targetTuple ++ [roundForthPoint r H n s]) ++ [n] = _
  rw [List.append_assoc]
  rfl

theorem roundState_matched {s : BackForthState} (n : ℕ) (h : s.Matched S T) :
    (roundState r rb H Hs n s).Matched S T :=
  backState_matched rb (forthState r s n H) n Hs (forthState_matched r s n H h)

theorem roundState_computableIn :
    ComputableIn E fun p : ℕ × BackForthState ↦ roundState r rb H Hs p.1 p.2 := by
  have hpair : ComputableIn E fun p : ℕ × BackForthState ↦
      (p.1, forthState r p.2 p.1 H) :=
    ComputableIn.fst.pair (forthState_computableIn r H)
  exact ((backState_computableIn rb Hs).comp hpair).of_eq fun _ ↦ rfl

/-! ### The run -/

/-- **The run**: rounds iterated from the seed `s₀`. -/
noncomputable def stateAt (n : ℕ) : BackForthState :=
  Nat.rec s₀ (fun y IH ↦ roundState r rb H Hs y IH) n

@[simp] theorem stateAt_zero : stateAt r rb H Hs s₀ 0 = s₀ := rfl

@[simp] theorem stateAt_succ (n : ℕ) :
    stateAt r rb H Hs s₀ (n + 1) = roundState r rb H Hs n (stateAt r rb H Hs s₀ n) := rfl

theorem stateAt_computableIn : ComputableIn E (stateAt r rb H Hs s₀) := by
  have hround : ComputableIn₂ E fun (_ : ℕ) (p : ℕ × BackForthState) ↦
      roundState r rb H Hs p.1 p.2 :=
    ((roundState_computableIn r rb H Hs).comp ComputableIn.snd).to₂
  exact (ComputableIn.nat_rec ComputableIn.id (ComputableIn.const s₀) hround).of_eq
    fun _ ↦ rfl

/-- **The invariant holds at every stage**, from a matched seed; each successor is one round. -/
theorem stateAt_matched {s₀ : BackForthState} (h₀ : s₀.Matched S T) (n : ℕ) :
    (stateAt r rb H Hs s₀ n).Matched S T := by
  induction n with
  | zero => exact h₀
  | succ n ih => exact roundState_matched r rb H Hs n ih

/-- **The empty start** is matched by the forward cover alone — Proposition 3.2's base case. -/
theorem stateAt_empty_matched (n : ℕ) : (stateAt r rb H Hs empty n).Matched S T :=
  stateAt_matched r rb H Hs (empty_matched r) n

/-! ### Lengths and discovery positions -/

theorem stateAt_sourceTuple_length (n : ℕ) :
    (stateAt r rb H Hs s₀ n).sourceTuple.length = s₀.sourceTuple.length + 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stateAt_succ, roundState_sourceTuple, List.length_append, ih]
    simp
    omega

theorem stateAt_targetTuple_length (n : ℕ) :
    (stateAt r rb H Hs s₀ n).targetTuple.length = s₀.targetTuple.length + 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stateAt_succ, roundState_targetTuple, List.length_append, ih]
    simp
    omega

/-- **The source point `n` is discovered at position `s₀.sourceTuple.length + 2 * n`** — the forth
half of round `n` put it there. -/
theorem stateAt_sourceTuple_getElem?_two_mul (n : ℕ) :
    (stateAt r rb H Hs s₀ (n + 1)).sourceTuple[s₀.sourceTuple.length + 2 * n]? = some n := by
  rw [stateAt_succ, roundState_sourceTuple,
    List.getElem?_append_right (by rw [stateAt_sourceTuple_length]),
    stateAt_sourceTuple_length]
  simp

/-- **The target point `n` is discovered at position `s₀.targetTuple.length + 2 * n + 1`** — the
back half of round `n` put it there. A different position from the source side, because the two
rounds append their two new entries in opposite orders. -/
theorem stateAt_targetTuple_getElem?_two_mul_succ (n : ℕ) :
    (stateAt r rb H Hs s₀ (n + 1)).targetTuple[s₀.targetTuple.length + 2 * n + 1]? = some n := by
  rw [stateAt_succ, roundState_targetTuple,
    List.getElem?_append_right (by rw [stateAt_targetTuple_length]; omega),
    stateAt_targetTuple_length]
  simp

/-! ### Persistence

Each round appends, so nothing is ever revised. Both statements are proved from the append equations
and then extended by transitivity — no lookup arithmetic is involved, which is what keeps them
usable at an arbitrary pair of stages. -/

theorem stateAt_sourceTuple_prefix_succ (n : ℕ) :
    (stateAt r rb H Hs s₀ n).sourceTuple <+: (stateAt r rb H Hs s₀ (n + 1)).sourceTuple := by
  rw [stateAt_succ, roundState_sourceTuple]
  exact List.prefix_append _ _

theorem stateAt_targetTuple_prefix_succ (n : ℕ) :
    (stateAt r rb H Hs s₀ n).targetTuple <+: (stateAt r rb H Hs s₀ (n + 1)).targetTuple := by
  rw [stateAt_succ, roundState_targetTuple]
  exact List.prefix_append _ _

theorem stateAt_sourceTuple_prefix {m n : ℕ} (h : m ≤ n) :
    (stateAt r rb H Hs s₀ m).sourceTuple <+: (stateAt r rb H Hs s₀ n).sourceTuple := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih => exact ih.trans (stateAt_sourceTuple_prefix_succ r rb H Hs s₀ (m + k))

theorem stateAt_targetTuple_prefix {m n : ℕ} (h : m ≤ n) :
    (stateAt r rb H Hs s₀ m).targetTuple <+: (stateAt r rb H Hs s₀ n).targetTuple := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih => exact ih.trans (stateAt_targetTuple_prefix_succ r rb H Hs s₀ (m + k))

end BackForthState

end Run

end FirstOrder.Language
