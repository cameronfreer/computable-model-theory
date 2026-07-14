/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.OraclePred
import Mathlib.Computability.PartrecCode

/-!
# Minimal oracle jump calculus

The smallest jump substrate the upper bounds need, on the oracle-set layer
(`O : Set (ℕ →. ℕ)`). General computability theory with no model-theory imports; kept
standalone and marked for eventual upstream extraction (mathlib or TauCeti), but built
only to the size this repository needs — extraction waits until the API has survived
downstream usage.

`ComputesJumpOf J O` is the abstract interface: the oracle set `J` lifts `O`-computation
and decides the domain of every `O`-partial-recursive function. These are exactly the two
capabilities of the classical jump that upper-bound arguments use; minimality of `J` is
deliberately not required (that is degree theory, out of scope), which is also what keeps
the notion independent of any machine or index representation. The public bridge theorems
quantify over any such `J`:

* `ComputesJumpOf.rePredIn_computablePredIn` — an `O`-r.e. predicate is decidable in `J`;
* `ComputesJumpOf.compl_rePredIn_computablePredIn` — the pivotal bridge: a predicate with
  `O`-r.e. complement is decidable in `J`;
* `ComputesJumpOf.trans` — composing interfaces gives iterated jumps: a `J₂` computing the
  jump of a `J₁` computing the jump of `O` computes (at least) the jump of `O`.

The machine/index representation is isolated in the implementation section: `haltingChar`
is the characteristic function of the absolute halting kernel over mathlib's
`Nat.Partrec.Code`, and `computesJumpOf_haltingChar_empty` instantiates the interface at
the empty oracle set, displaying the classical `0′`. Relativized code layers (a concrete
`O ↦ O′` for nonempty `O`) are deferred until downstream usage requires them: the bridge
theorems above never mention codes.

Deliberately excluded: the arithmetical hierarchy, Post's theorem, degree quotients, and
index sets.
-/

open Encodable Part

section Interface

variable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

/-- The oracle set `J` computes (at least) the jump of the oracle set `O`: it lifts
`O`-computation, and it decides the domain of every `O`-partial-recursive function. The
two clauses are exactly the capabilities of the classical jump that upper-bound arguments
use; minimality is deliberately not required, keeping the notion representation-free. -/
def ComputesJumpOf (J O : Set (ℕ →. ℕ)) : Prop :=
  (∀ f : ℕ →. ℕ, Nat.RecursiveIn O f → Nat.RecursiveIn J f) ∧
    ∀ f : ℕ →. ℕ, Nat.RecursiveIn O f → ComputablePredIn J fun n ↦ (f n).Dom

namespace ComputesJumpOf

variable {J J₁ J₂ O O₁ : Set (ℕ →. ℕ)}

/-- Oracle lifting: `O`-partial-recursive functions are `J`-partial-recursive. -/
theorem recursiveIn_lift {f : α →. σ} (hJ : ComputesJumpOf J O) (hf : RecursiveIn O f) :
    RecursiveIn J f :=
  hJ.1 _ hf

/-- Oracle lifting for total functions. -/
theorem computableIn_lift {f : α → σ} (hJ : ComputesJumpOf J O) (hf : ComputableIn O f) :
    ComputableIn J f :=
  hJ.recursiveIn_lift hf

/-- Oracle lifting for computable predicates. -/
theorem computablePredIn_lift {p : α → Prop} (hJ : ComputesJumpOf J O)
    (hp : ComputablePredIn O p) : ComputablePredIn J p :=
  let ⟨D, h⟩ := hp
  ⟨D, hJ.computableIn_lift h⟩

/-- Oracle lifting for r.e. predicates. -/
theorem rePredIn_lift {p : α → Prop} (hJ : ComputesJumpOf J O) (hp : REPredIn O p) :
    REPredIn J p :=
  hJ.recursiveIn_lift hp

/-- The domain of an `O`-partial-recursive function on any coded type is decidable
in `J`. -/
theorem dom_computablePredIn {f : α →. σ} (hJ : ComputesJumpOf J O)
    (hf : RecursiveIn O f) : ComputablePredIn J fun a ↦ (f a).Dom := by
  have h := hJ.2 _ hf
  exact (h.comp (f := fun a : α ↦ encode a) ComputableIn.encode).of_eq fun a ↦ by
    simp [encodek]

/-- An `O`-r.e. predicate is decidable in `J`. -/
theorem rePredIn_computablePredIn {p : α → Prop} (hJ : ComputesJumpOf J O)
    (hp : REPredIn O p) : ComputablePredIn J p :=
  (hJ.dom_computablePredIn hp).of_eq fun _ ↦ ⟨fun ⟨h, _⟩ ↦ h, fun h ↦ ⟨h, trivial⟩⟩

/-- The pivotal bridge: a predicate whose complement is `O`-r.e. is decidable in `J`.
This alone will discharge `EI(K) ≤ O′`-style upper bounds from r.e.-complement
theorems, without invoking any arithmetical hierarchy. -/
theorem compl_rePredIn_computablePredIn {p : α → Prop} (hJ : ComputesJumpOf J O)
    (hp : REPredIn O fun a ↦ ¬p a) : ComputablePredIn J p :=
  (hJ.rePredIn_computablePredIn hp).not.of_eq fun _ ↦ not_not

/-- Enlarging the deciding oracle set preserves the interface. -/
theorem mono_left (hJJ : J₁ ⊆ J) (hJ : ComputesJumpOf J₁ O) : ComputesJumpOf J O :=
  ⟨fun f hf ↦ Nat.RecursiveIn.subst (hJ.1 f hf)
      fun g hg ↦ Nat.RecursiveIn.oracle g (hJJ hg),
    fun f hf ↦ (hJ.2 f hf).mono hJJ⟩

/-- Interfaces compose: computing the jump of a jump computes (at least) the jump.
This is the iterated-jump principle in the form the double-jump upper bounds will
consume. -/
theorem trans (h₂ : ComputesJumpOf J₂ J₁) (h₁ : ComputesJumpOf J₁ O) :
    ComputesJumpOf J₂ O :=
  ⟨fun f hf ↦ h₂.1 f (h₁.1 f hf), fun f hf ↦ h₂.2 f (h₁.1 f hf)⟩

end ComputesJumpOf

end Interface

/-! ### Implementation: the displayed `0′`

The machine/index representation is confined to this section. The public bridge theorems
above never mention codes; only the existence of a concrete instance does. -/

section Implementation

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- The absolute halting kernel: the paired code `n` halts, over mathlib's
`Nat.Partrec.Code`. The representation-dependent core of the displayed `0′`. -/
def haltingKernel (n : ℕ) : Prop :=
  ((Denumerable.ofNat Code n.unpair.1).eval n.unpair.2).Dom

open Classical in
/-- The characteristic function of the halting kernel, as an oracle: the displayed `0′`.
Total but not computable; oracles carry no computability obligation. -/
noncomputable def haltingChar : ℕ →. ℕ :=
  fun n ↦ Part.some (if haltingKernel n then 1 else 0)

open Classical in
/-- Implementation lemma, isolating the index representation: the domain of any partial
recursive function is decidable in the halting characteristic. Via `exists_code`, the
membership question becomes one oracle call to `haltingChar` at a paired code. -/
theorem computablePredIn_dom_haltingChar {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    ComputablePredIn {haltingChar} fun n ↦ (f n).Dom := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hf
  have hcall : RecursiveIn {haltingChar} fun n : ℕ ↦ haltingChar (Nat.pair (encode c) n) :=
    RecursiveIn.comp (f := haltingChar)
      (RecursiveIn.iff_nat.2 (Nat.RecursiveIn.oracle _ rfl))
      ((Primrec₂.natPair.to_comp.computableIn₂).comp
        (ComputableIn.const (encode c)) ComputableIn.id)
  have hind : ComputableIn {haltingChar}
      fun n : ℕ ↦ if haltingKernel (Nat.pair (encode c) n) then (1 : ℕ) else 0 :=
    hcall.of_eq fun n ↦ rfl
  have hB : ComputableIn {haltingChar} fun n : ℕ ↦
      decide ((if haltingKernel (Nat.pair (encode c) n) then (1 : ℕ) else 0) = 1) :=
    (Primrec.eq (α := ℕ)).decide.to_comp.computableIn₂.comp hind (ComputableIn.const 1)
  refine ⟨fun n ↦ Classical.propDecidable _, hB.of_eq fun n ↦ decide_eq_decide.2 ?_⟩
  have hkernel : haltingKernel (Nat.pair (encode c) n) ↔ (f n).Dom := by
    simp only [haltingKernel, Nat.unpair_pair, Denumerable.ofNat_encode, hc]
  by_cases h : haltingKernel (Nat.pair (encode c) n) <;> simp [h, hkernel.symm]

/-- The halting characteristic computes the jump of the empty oracle set: the displayed
`0′`. The concrete instance of the abstract interface. -/
theorem computesJumpOf_haltingChar_empty :
    ComputesJumpOf {haltingChar} (∅ : Set (ℕ →. ℕ)) :=
  ⟨fun _ hf ↦ Nat.RecursiveIn.subst hf fun g hg ↦ absurd hg (Set.notMem_empty g),
    fun _ hf ↦ computablePredIn_dom_haltingChar
      (Nat.RecursiveIn.partrec_of_oracle (fun g hg ↦ absurd hg (Set.notMem_empty g)) hf)⟩

/-- Non-vacuity: the halting kernel itself — the classical halting problem — is decidable
in the halting characteristic, via the universal evaluation being partial recursive. -/
theorem haltingKernel_computablePredIn :
    ComputablePredIn {haltingChar} haltingKernel := by
  have huniv : Nat.Partrec fun n : ℕ ↦
      (Denumerable.ofNat Code n.unpair.1).eval n.unpair.2 :=
    Partrec.nat_iff.1 (eval_part.comp
      ((Computable.ofNat Code).comp (Computable.fst.comp Computable.unpair))
      (Computable.snd.comp Computable.unpair))
  exact (computablePredIn_dom_haltingChar huniv).of_eq fun n ↦ Iff.rfl

end Implementation
