/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.OracleCode
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit: program codes for one oracle

**The oracle instruction is the oracle.** `test_oracle_is_oracle` is definitional, and
`test_oracle_query_composes` runs a program that genuinely queries a non-computable-looking oracle
(doubling) and post-processes the answer — the composition is with a real oracle call, not an
absolute computable example dressed up.

**Partiality is preserved, not papered over.** `test_divergent_oracle_stays_divergent` interprets
the oracle instruction against the everywhere-undefined oracle; `test_rfind_diverges` runs an
unbounded search that never succeeds, against *every* oracle, and shows it does not converge. A
"total" reading of `evalIn` would be caught by either.

**Representation and countability.** Soundness and completeness are gated as the two directions
of `nat_recursiveIn_iff`; `test_absolute_has_code` shows every absolutely partial recursive
function has a code relative to any oracle; `test_countable` is the countability theorem for the
singleton oracle set. Nothing here claims uniform evaluation in the code, a staged evaluator, or a
compiler — those are separate, and unproved in this module by design.
-/

open Encodable OracleCode

/-! ### The oracle instruction -/

/-- **`oracle` is interpreted as the oracle itself**, definitionally. -/
theorem test_oracle_is_oracle (X : ℕ →. ℕ) : evalIn X oracle = X := rfl

/-- The doubling oracle. -/
def doubling : ℕ →. ℕ := fun n => Part.some (2 * n)

/-- **A real oracle query, composed**: query the doubling oracle at `3`, then take the successor. -/
theorem test_oracle_query_composes : 7 ∈ evalIn doubling (comp succ oracle) 3 := by
  simp [doubling, Part.bind_some]

/-- The same program against a different oracle gives a different answer: the interpretation
depends on the oracle parameter, not on the code alone. -/
theorem test_oracle_parameter_matters :
    4 ∈ evalIn (fun n => Part.some n) (comp succ oracle) 3 := by
  simp [Part.bind_some]

/-! ### Partiality -/

/-- **The everywhere-undefined oracle stays undefined** through the oracle instruction. -/
theorem test_divergent_oracle_stays_divergent (n : ℕ) :
    ¬ (evalIn (fun _ => Part.none) oracle n).Dom := fun h => h

/-- **An unbounded search that never succeeds does not converge**, against any oracle: the tested
value `succ (pair a n)` is never `0`. -/
theorem test_rfind_diverges (X : ℕ →. ℕ) (a : ℕ) : ¬ (evalIn X (rfind succ) a).Dom := by
  rw [evalIn_rfind, Nat.rfind_dom]
  rintro ⟨n, hn, -⟩
  simp at hn

/-! ### Representation and countability -/

/-- **Soundness.** -/
theorem test_sound (X : ℕ →. ℕ) (c : OracleCode) : Nat.RecursiveIn {X} (evalIn X c) :=
  evalIn_recursiveIn X c

/-- **Completeness**, as an existential proposition. -/
theorem test_complete (X : ℕ →. ℕ) {f : ℕ →. ℕ} (h : Nat.RecursiveIn {X} f) :
    ∃ c : OracleCode, evalIn X c = f :=
  exists_code X h

/-- **Every absolutely partial recursive function has a code relative to any oracle.** -/
theorem test_absolute_has_code (X : ℕ →. ℕ) {f : ℕ →. ℕ} (h : Nat.Partrec f) :
    ∃ c : OracleCode, evalIn X c = f :=
  exists_code X (Nat.Partrec.recursiveIn h)

/-- The typed representation theorem, through `RecursiveIn.iff_nat`. -/
theorem test_typed_representation (X : ℕ →. ℕ) (f : ℕ →. ℕ) :
    RecursiveIn {X} f ↔ ∃ c : OracleCode, evalIn X c = f :=
  recursiveIn_iff X

/-- **Countability** of the functions recursive in one fixed oracle. -/
theorem test_countable (X : ℕ →. ℕ) : Set.Countable {f : ℕ →. ℕ | RecursiveIn {X} f} :=
  countable_setOf_recursiveIn X

/-- The derived numbering round-trips. -/
theorem test_decode_encode (c : OracleCode) :
    (decode (encode c) : Option OracleCode) = Option.some c :=
  decode_encode c

#assert_standard_axioms test_oracle_is_oracle
#assert_standard_axioms test_oracle_query_composes
#assert_standard_axioms test_oracle_parameter_matters
#assert_standard_axioms test_divergent_oracle_stays_divergent
#assert_standard_axioms test_rfind_diverges
#assert_standard_axioms test_sound
#assert_standard_axioms test_complete
#assert_standard_axioms test_absolute_has_code
#assert_standard_axioms test_typed_representation
#assert_standard_axioms test_countable
#assert_standard_axioms test_decode_encode
