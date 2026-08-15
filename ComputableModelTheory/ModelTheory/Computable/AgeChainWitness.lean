/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.PartialAgeSteps

/-!
# Uniform witness extraction along a scheduled family

The first piece of CHMM Lemma 2.9's input. `CeStructureChainIn`'s stages are **nonempty**
`CePresentationIn`s, while a `PartialAgeIn`'s members may be empty, so building a chain out of a
representation needs each scheduled member's enumeration turned into a total one.

`PartialCePresentationIn.toCePresentation` already does that conversion — given a *witness*
`P.enum? m₀ = some x₀` it falls back to `x₀` on the empty steps, and `range_getD` says the domain is
unchanged. So the missing ingredient is not another totalization API: it is the **uniform extraction
of that witness** across the schedule. Per-presentation `toCePresentation` supplies no uniformity,
and uniformity is what a chain needs.

`firstSomeStep` is that extraction. Two naming points, since both are easy to misread:

* it returns the least enumeration **step**, not the least carrier element — the enumeration is not
  monotone and its steps are not its values;
* it is total, and totality is exactly what the nonemptiness hypothesis buys. Internally the search
  is `Nat.find`; the public computability statement goes through `ComputableIn.find`, whose
  hypothesis is the same nonemptiness.

The hypothesis is stated on the **scheduled** members `d n`, not on all of `K`. That is the honest
shape for Lemma 2.9's consumer: a base witness proves the initial selected stage nonempty, and the
chain's injective steps propagate the fact along the schedule. No member off the schedule is
constrained, and a representation with empty members elsewhere is still admissible.

Kept beside the chain construction rather than promoted to the age layer; promote only on a second
consumer.
-/

open Encodable Part FirstOrder Language

namespace FirstOrder.Language

namespace PartialAgeIn

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable (K : PartialAgeIn O L) (d : ℕ → ℕ) (hne : ∀ n, (K.domainAt (d n)).Nonempty)

include hne in
/-- Nonemptiness of a scheduled member, in the form the search consumes. -/
theorem exists_enum?_isSome (n : ℕ) : ∃ m, (K.enum? (d n) m).isSome = true := by
  obtain ⟨_, m, hm⟩ := hne n
  exact ⟨m, by rw [hm]; rfl⟩

include hne in
/-- The least enumeration **step** at which the `n`-th scheduled member produces a value. Total
because the member is nonempty. -/
noncomputable def firstSomeStep (n : ℕ) : ℕ :=
  Nat.find (K.exists_enum?_isSome d hne n)

include hne in
/-- The value the `n`-th scheduled member produces at that step: the uniformly extracted witness. -/
noncomputable def firstEnumeratedValue (n : ℕ) : ℕ :=
  (K.enum? (d n) (K.firstSomeStep d hne n)).getD 0

/-- **The witness equation.** This is the input `toCePresentation` wants, now available uniformly
in the schedule. -/
theorem enum?_firstSomeStep (n : ℕ) :
    K.enum? (d n) (K.firstSomeStep d hne n) =
      Option.some (K.firstEnumeratedValue d hne n) := by
  have h : (K.enum? (d n) (K.firstSomeStep d hne n)).isSome = true :=
    Nat.find_spec (K.exists_enum?_isSome d hne n)
  rw [firstEnumeratedValue]
  cases hcase : K.enum? (d n) (K.firstSomeStep d hne n) with
  | none => rw [hcase] at h; exact absurd h (by simp)
  | some x => rfl

/-- The extracted witness lies in the scheduled member's carrier. -/
theorem firstEnumeratedValue_mem (n : ℕ) :
    K.firstEnumeratedValue d hne n ∈ K.domainAt (d n) :=
  ⟨_, K.enum?_firstSomeStep d hne n⟩

/-- The step search is computable, uniformly in the schedule. -/
theorem firstSomeStep_computableIn (hd : ComputableIn O d) :
    ComputableIn O (K.firstSomeStep d hne) := by
  have hf : ComputableIn₂ O fun (n m : ℕ) ↦ (K.enum? (d n) m).isSome :=
    (Primrec.option_isSome.to_comp.computableIn.comp
      (K.enum?_computableIn.comp ((hd.comp ComputableIn.fst).pair ComputableIn.snd))).to₂
  exact ComputableIn.find hf (K.exists_enum?_isSome d hne)

/-- And so is the extracted witness. -/
theorem firstEnumeratedValue_computableIn (hd : ComputableIn O d) :
    ComputableIn O (K.firstEnumeratedValue d hne) := by
  have henum : ComputableIn O fun n ↦ K.enum? (d n) (K.firstSomeStep d hne n) :=
    K.enum?_computableIn.comp ((hd.pair (K.firstSomeStep_computableIn d hne hd)))
  exact (ComputableIn.option_casesOn henum (ComputableIn.const 0)
    ComputableIn.snd.to₂).of_eq fun n ↦ by
      rw [firstEnumeratedValue]
      cases K.enum? (d n) (K.firstSomeStep d hne n) <;> rfl

end PartialAgeIn

end FirstOrder.Language
