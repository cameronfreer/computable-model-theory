/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.CanonicalTransport
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for canonical transport

Named acceptance tests for canonical least-term transport, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Computable/CanonicalTransportAudit.lean
```

Coverage: the reusable total-search helper; the four computability contracts; the
encoding-independent specification; the realized-embedding agreement; the semantic
identity gate; and the two off-spec cases — a range tuple shorter than the domain
generators (default-padded environment) and the bound guard rejecting an out-of-range
variable code.
-/

open Encodable FirstOrder Language

section

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

/-- The reusable total-search helper stays in the standard axiom set. -/
theorem test_computableIn_find {α : Type*} [Primcodable α] {f : α → ℕ → Bool}
    (hf : ComputableIn₂ O f) (h : ∀ a, ∃ n, f a n = true) :
    ComputableIn O fun a ↦ Nat.find (h a) :=
  ComputableIn.find hf h

/-- Transport is oracle-computable, uniformly in the data and value. -/
theorem test_transportValue_computableIn (K : ComputableAgeIn O L) :
    ComputableIn O fun q : PotentialEmbeddingData × ℕ ↦ K.transportValue q.1 q.2 :=
  K.transportValue_computableIn

/-- The canonical code is oracle-computable. -/
theorem test_termCodeFor_computableIn (K : ComputableAgeIn O L) :
    ComputableIn O fun p : ℕ × ℕ ↦ K.termCodeFor p.1 p.2 :=
  K.termCodeFor_computableIn

/-- The representing term is oracle-computable. -/
theorem test_representingTerm_computableIn (K : ComputableAgeIn O L) :
    ComputableIn O fun p : ℕ × ℕ ↦ K.representingTerm p.1 p.2 :=
  K.representingTerm_computableIn

/-- The code test is oracle-computable. -/
theorem test_isTermCodeFor_computableIn (K : ComputableAgeIn O L) :
    ComputableIn₂ O fun (p : ℕ × ℕ) (c : ℕ) ↦ K.isTermCodeFor p.1 p.2 c :=
  K.isTermCodeFor_computableIn

/-- The encoding-independent specification: the code decodes to a bounded generator term
realizing `x`. -/
theorem test_termCodeFor_spec' (K : ComputableAgeIn O L) (i x : ℕ) :
    ∃ t : L.Term ℕ,
      @decode (L.Term ℕ) Primcodable.toEncodable (K.termCodeFor i x) = some t ∧
        Term.VarsBelow (K.gens i).length t ∧ K.termRealize ((i, K.gens i), t) = x :=
  K.termCodeFor_spec' i x

/-- On actual data, transport agrees with the realized embedding. -/
theorem test_transportValue_eq_toEmbedding (K : ComputableAgeIn O L)
    {G : PotentialEmbeddingData} (h : G.WellFormed K)
    (hAE : @AtomicEquivalent L ℕ ℕ (K.structureAt G.domIdx) (K.structureAt G.codIdx) _
      (K.gens G.domIdx).view (G.targetView h)) (x : ℕ) :
    K.transportValue G x = G.toEmbedding h hAE x :=
  K.transportValue_eq_toEmbedding h hAE x

/-- Semantic gate: transport along the identity potential embedding is the identity on
values. -/
theorem test_transportValue_id (K : ComputableAgeIn O L) (i x : ℕ) :
    K.transportValue (PotentialEmbeddingData.id K i) x = x :=
  K.transportValue_id i x

/-- Off-spec totality: on malformed data with a range tuple shorter than the domain
generators (here empty), transport still evaluates, realizing the representing term under
the default-padded (`envFun`-zero) environment. -/
theorem test_transportValue_malformed (K : ComputableAgeIn O L) (i x : ℕ) :
    K.transportValue ⟨i, i, []⟩ x = K.termRealize ((i, []), K.representingTerm i x) := by
  rw [ComputableAgeIn.transportValue, K.decode_termCodeFor, Option.elim]

/-- Off-spec input: the bound guard rejects a code for a term with an out-of-range
variable. -/
theorem test_isTermCodeFor_reject_high_var (K : ComputableAgeIn O L) (i x v : ℕ)
    (hv : (K.gens i).length ≤ v) :
    K.isTermCodeFor i x
      (@encode (L.Term ℕ) Primcodable.toEncodable (Term.var v)) = false := by
  unfold ComputableAgeIn.isTermCodeFor
  rw [@encodek (L.Term ℕ) Primcodable.toEncodable (Term.var v)]
  simp only [Option.elim]
  have hfalse : Term.varsBelowBool (K.gens i).length (Term.var (L := L) v) = false := by
    rw [← Bool.not_eq_true, Term.varsBelowBool_iff]
    exact fun hvb ↦ absurd (hvb v (by simp [Term.varFinset])) (Nat.not_lt.2 hv)
  rw [hfalse, Bool.false_and]

end

#assert_standard_axioms test_computableIn_find
#assert_standard_axioms test_transportValue_computableIn
#assert_standard_axioms test_termCodeFor_computableIn
#assert_standard_axioms test_representingTerm_computableIn
#assert_standard_axioms test_isTermCodeFor_computableIn
#assert_standard_axioms test_termCodeFor_spec'
#assert_standard_axioms test_transportValue_eq_toEmbedding
#assert_standard_axioms test_transportValue_id
#assert_standard_axioms test_transportValue_malformed
#assert_standard_axioms test_isTermCodeFor_reject_high_var
