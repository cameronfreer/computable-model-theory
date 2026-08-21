/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.AgeChainWitness
import ComputableModelTheory.ModelTheory.Computable.PartialSelectorSpecs
import ComputableModelTheory.ModelTheory.Computable.PartialMemberEmbedding

/-!
# The CJEP schedule

CHMM Theorem 2.10 (⇐) drives Lemma 2.9 with a chain built from the joint embedding property. The
schedule is

```
d 0       = baseIdx
d (n + 1) = (sel (d n) n).apexIdx
```

and each transition carries **two** legs, doing different jobs, which is why the schedule takes the
previous stage on the left and the next original index on the right:

* the **left** leg embeds `d n` into `d (n+1)` — this is the chain step, and the only leg
  nonemptiness travels along;
* the **right** leg embeds the original member `n` into `d (n+1)` — this is what makes the schedule
  cofinal in the representation, so the limit's age is all of `K`'s class rather than part of it.

The base index is a *named witness*, not `0`. At the empty-capable layer a representation of a
perfectly infinite age may have an empty member at index `0`, and nothing distinguishes the first
index; the hypothesis that must be supplied is a nonempty member somewhere, together with which one.

**Nonemptiness is established here, before any enumeration is totalized.** It travels along the left
legs from the base witness by induction, using nothing but the fact that an embedding maps a carrier
element to a carrier element. That ordering matters: `firstSomeStep` needs nonemptiness to be total,
so deriving nonemptiness from the totalized enumeration would be circular.

This file stops at the data and its realizers. Turning the left legs into uniformly partial
recursive carrier maps is `applyPotentialPart`'s job, and comes next.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O E : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-! ### The schedule -/

variable (sel : ℕ → ℕ → PartialJointEmbeddingData) (baseIdx : ℕ)

/-- The schedule: start at the named base index, then joint-embed the previous stage with the next
original index. -/
def cjepSchedule : ℕ → ℕ := fun n ↦
  Nat.rec (motive := fun _ ↦ ℕ) baseIdx (fun y IH ↦ (sel IH y).apexIdx) n

@[simp] theorem cjepSchedule_zero : cjepSchedule sel baseIdx 0 = baseIdx := rfl

@[simp] theorem cjepSchedule_succ (n : ℕ) :
    cjepSchedule sel baseIdx (n + 1) = (sel (cjepSchedule sel baseIdx n) n).apexIdx := rfl

theorem cjepSchedule_computableIn (hsel : ComputableIn E fun p : ℕ × ℕ ↦ sel p.1 p.2) :
    ComputableIn E (cjepSchedule sel baseIdx) := by
  have hstep : ComputableIn₂ E fun (_ : ℕ) (p : ℕ × ℕ) ↦ (sel p.2 p.1).apexIdx :=
    ((PartialJointEmbeddingData.primrec_apexIdx.to_comp.computableIn).comp
      (hsel.comp ((ComputableIn.snd.comp ComputableIn.snd).pair
        (ComputableIn.fst.comp ComputableIn.snd)))).to₂
  exact ComputableIn.nat_rec ComputableIn.id (ComputableIn.const baseIdx) hstep

/-! ### The two legs

`stepData n` is the chain step out of stage `n`; `cofinalData n` records that the `n`-th *original*
member lands in stage `n+1`. Both are read off the same joint-embedding answer, and only the first
is a chain step — conflating them would make the chain cofinal by accident or not at all. -/

/-- The left leg at transition `n`: stage `n` into stage `n+1`. -/
def stepData (n : ℕ) : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple
    (cjepSchedule sel baseIdx n, cjepSchedule sel baseIdx (n + 1),
      (sel (cjepSchedule sel baseIdx n) n).leftImage)

/-- The right leg at transition `n`: the original member `n` into stage `n+1`. -/
def cofinalData (n : ℕ) : PotentialEmbeddingData :=
  PotentialEmbeddingData.ofTriple
    (n, cjepSchedule sel baseIdx (n + 1),
      (sel (cjepSchedule sel baseIdx n) n).rightImage)

@[simp] theorem stepData_domIdx (n : ℕ) :
    (stepData sel baseIdx n).domIdx = cjepSchedule sel baseIdx n := rfl

@[simp] theorem stepData_codIdx (n : ℕ) :
    (stepData sel baseIdx n).codIdx = cjepSchedule sel baseIdx (n + 1) := rfl

@[simp] theorem cofinalData_domIdx (n : ℕ) : (cofinalData sel baseIdx n).domIdx = n := rfl

@[simp] theorem cofinalData_codIdx (n : ℕ) :
    (cofinalData sel baseIdx n).codIdx = cjepSchedule sel baseIdx (n + 1) := rfl

variable {K : PartialAgeIn O L} {sel baseIdx}

/-- The chain step is actual. -/
theorem stepData_partialIsEmbedding (hspec : K.JointSpec sel) (n : ℕ) :
    K.PartialIsEmbedding (stepData sel baseIdx n) :=
  (hspec (cjepSchedule sel baseIdx n) n).1

/-- And so is the cofinality leg. -/
theorem cofinalData_partialIsEmbedding (hspec : K.JointSpec sel) (n : ℕ) :
    K.PartialIsEmbedding (cofinalData sel baseIdx n) :=
  (hspec (cjepSchedule sel baseIdx n) n).2

/-! ### Nonemptiness travels along the left legs

Established **before** any enumeration is totalized: `firstSomeStep` needs nonemptiness to be total,
so deriving nonemptiness from a totalized enumeration would be circular. -/

/-- An actual embedding carries a nonempty source carrier to a nonempty target carrier. -/
theorem domainAt_nonempty_of_partialIsEmbedding {F : PotentialEmbeddingData}
    (h : K.PartialIsEmbedding F) (hne : (K.domainAt F.domIdx).Nonempty) :
    (K.domainAt F.codIdx).Nonempty := by
  obtain ⟨f, -⟩ := h
  obtain ⟨x, hx⟩ := hne
  exact ⟨((f ⟨x, hx⟩ : (K.memberAt F.codIdx).domain) : ℕ), (f ⟨x, hx⟩).2⟩

/-- **Every scheduled stage is nonempty**, from the named base witness alone. -/
theorem cjepSchedule_domainAt_nonempty (hspec : K.JointSpec sel)
    (hbase : (K.domainAt baseIdx).Nonempty) :
    ∀ n, (K.domainAt (cjepSchedule sel baseIdx n)).Nonempty
  | 0 => hbase
  | n + 1 =>
    domainAt_nonempty_of_partialIsEmbedding (stepData_partialIsEmbedding hspec n)
      (cjepSchedule_domainAt_nonempty hspec hbase n)

end PartialAgeIn

end FirstOrder.Language
