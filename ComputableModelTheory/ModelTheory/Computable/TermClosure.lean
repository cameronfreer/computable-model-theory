/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.TermEvaluation
import ComputableModelTheory.ModelTheory.TupleClosure

/-!
# Effective term enumeration over tuple closures

Effective enumeration of a tuple's closure at a fixed width: `termValue?` decodes a
natural-number code as a term and evaluates it at the tuple, so the codes whose
decoding succeeds enumerate exactly the closure (`termValue?_eq_some_iff_mem_closure`,
through the semantic closure gate), and membership in the closure of a fixed tuple is
r.e. in the oracle of a computable structure (`closure_mem_rePredIn`, with the list
form `tuple_closure_mem_rePredIn`).

Everything here is at a fixed width: no single uniform algorithm over all list lengths
is claimed. R.e. diagrams of closure elements beyond membership would require encoding
all term witnesses together and are deferred with the dovetailing substrate.
-/

open Encodable FirstOrder Language Language.BoundedFormula

namespace FirstOrder.Language

variable {L : Language} [L.EffectiveLanguage] [L.Structure ℕ] {k : ℕ}

/-- Decode a code as a term and evaluate it at the tuple. The decoding runs through
the registered `Primcodable` instance (whose `Encodable` parent is pinned explicitly:
the ambient `Encodable` resolution assembles the same instance with different leaf
arguments, and mixing the two forms is the known elaboration swamp). -/
def termValue? (a : Fin k → ℕ) (c : ℕ) : Option ℕ :=
  (@decode (L.Term (Fin k)) Primcodable.toEncodable c).map fun t ↦ t.realize a

set_option maxHeartbeats 1000000 in
/-- Decode-and-evaluate is oracle-computable in a computable structure. -/
theorem termValue?_computableIn (O : Set (ℕ →. ℕ)) [IsComputableStructureIn O L]
    (k : ℕ) : ComputableIn₂ O (termValue? (L := L) (k := k)) := by
  have hf : ComputableIn₂ O fun (a : Fin k → ℕ) (t : L.Term (Fin k)) ↦ t.realize a :=
    ((Term.realize_computableIn O (m := k)).comp
      (ComputableIn.snd.pair ComputableIn.fst)).to₂
  exact (ComputableIn.map_decode hf).of_eq fun p ↦ rfl

/-- On the code of a term, decode-and-evaluate returns its value. -/
theorem termValue?_encode (a : Fin k → ℕ) (t : L.Term (Fin k)) :
    termValue? (L := L) a (@encode (L.Term (Fin k)) Primcodable.toEncodable t) =
      some (t.realize a) := by
  show (@decode (L.Term (Fin k)) Primcodable.toEncodable
      (@encode (L.Term (Fin k)) Primcodable.toEncodable t)).map
      (fun t : L.Term (Fin k) ↦ t.realize a) = some (t.realize a)
  rw [@encodek (L.Term (Fin k)) Primcodable.toEncodable t]
  rfl

/-- Every term value is enumerated by some code. -/
theorem exists_code_termValue? (a : Fin k → ℕ) (t : L.Term (Fin k)) :
    ∃ c, termValue? (L := L) a c = some (t.realize a) :=
  ⟨_, termValue?_encode a t⟩

/-- The enumeration is exactly the closure: a value is hit by some code iff it lies in
the closure of the tuple's range. -/
theorem termValue?_eq_some_iff_mem_closure (a : Fin k → ℕ) (x : ℕ) :
    (∃ c, termValue? (L := L) a c = some x) ↔
      x ∈ Substructure.closure L (Set.range a) := by
  rw [mem_closure_range_iff_exists_term]
  constructor
  · rintro ⟨c, hc⟩
    rcases hd : @decode (L.Term (Fin k)) Primcodable.toEncodable c with - | t
    · rw [termValue?, hd] at hc
      simp at hc
    · rw [termValue?, hd] at hc
      exact ⟨t, by simpa using hc⟩
  · rintro ⟨t, ht⟩
    exact ht ▸ exists_code_termValue? a t

/-- Membership in the closure of a fixed tuple is r.e. in the oracle of a computable
structure. -/
theorem closure_mem_rePredIn (O : Set (ℕ →. ℕ)) [IsComputableStructureIn O L]
    (a : Fin k → ℕ) :
    REPredIn O fun x : ℕ ↦ x ∈ Substructure.closure L (Set.range a) := by
  have hfix : ComputableIn O fun c : ℕ ↦ termValue? (L := L) a c :=
    ComputableIn₂.comp (termValue?_computableIn O k) (ComputableIn.const a)
      ComputableIn.id
  have hcore : ComputablePredIn O fun p : ℕ × ℕ ↦
      termValue? (L := L) a p.2 = some p.1 := by
    obtain ⟨hd, hp⟩ := (Primrec.eq :
      PrimrecRel fun o₁ o₂ : Option ℕ ↦ o₁ = o₂)
    have heq : ComputableIn₂ O fun o₁ o₂ : Option ℕ ↦ decide (o₁ = o₂) :=
      (hp.to_comp.computableIn).of_eq fun p ↦ decide_eq_decide.2 Iff.rfl
    refine ⟨fun p ↦ hd (termValue? (L := L) a p.2, some p.1), ?_⟩
    refine (heq.comp (hfix.comp ComputableIn.snd)
      (ComputableIn.option_some.comp ComputableIn.fst)).of_eq fun p ↦ ?_
    exact decide_eq_decide.2 Iff.rfl
  exact (REPredIn.exists_nat_of_computablePredIn hcore).of_eq fun x ↦
    termValue?_eq_some_iff_mem_closure a x

/-- The list form: membership in a fixed list tuple's closure is r.e. in the
oracle. -/
theorem tuple_closure_mem_rePredIn (O : Set (ℕ →. ℕ)) [IsComputableStructureIn O L]
    (a : Tuple ℕ) : REPredIn O fun x : ℕ ↦ x ∈ Tuple.closure L a :=
  (closure_mem_rePredIn O a.view).of_eq fun x ↦ by rw [Tuple.closure_eq]

end FirstOrder.Language
