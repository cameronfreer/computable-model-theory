/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Tactic.DeriveEncodable
import Mathlib.Data.Set.Countable
import ComputableModelTheory.Computability.RecursiveIn

/-!
# Program codes for functions recursive in one oracle

A concrete countable syntax whose constructors mirror those of `Nat.RecursiveIn`, together with its
compositional interpretation relative to a fixed partial oracle `X : ℕ →. ℕ`. The oracle is a
parameter of the *interpretation*, not a payload of the code: `oracle` is one nullary instruction,
and `evalIn X oracle = X`.

## What this module proves, and what it does not

* **Soundness** (`evalIn_recursiveIn`): every interpreted code is recursive in `{X}`. The proof
  follows the constructors.
* **Completeness** (`exists_code`): every function `Nat.RecursiveIn {X}` is the interpretation of
  some code. The proof follows the derivation; the oracle case eliminates singleton membership. The
  statement is an existential proposition — no code is extracted from the `Prop`-valued derivation.
* **Countability** (`countable_setOf_recursiveIn`): the functions `ℕ →. ℕ` recursive in `{X}` form a
  countable set, as the range of `evalIn X` over the countable code type. The typed corollary
  `recursiveIn_iff` lifts through `RecursiveIn.iff_nat`.

This is **code representation and countability**, not an effective universal enumeration. In
particular nothing here states or proves:

* uniform recursion of `(c, n) ↦ evalIn X c n` in the pair;
* a total stage-indexed `Option`-valued evaluator with soundness and eventual completeness;
* a computable compiler or parameterization theorem on codes.

Those are separate theorems with separate names, and for an arbitrary *partial* oracle the second
needs either total oracle data or explicit staged oracle data, because an oracle call may itself
diverge. `StagedPartialIn` continues to take staged data as an input; no instance is manufactured
here.

The `Encodable` instance is derived, and should be treated as opaque: the specific numbering is an
implementation detail. What is used is only that codes are countable and that
`decode (encode c) = some c`.
-/

open Encodable

/-- Program codes for functions recursive in one oracle: the constructors of `Nat.RecursiveIn`,
with a single nullary `oracle` instruction in place of the oracle-membership hypothesis. -/
inductive OracleCode : Type
  | zero : OracleCode
  | succ : OracleCode
  | left : OracleCode
  | right : OracleCode
  | oracle : OracleCode
  | pair : OracleCode → OracleCode → OracleCode
  | comp : OracleCode → OracleCode → OracleCode
  | prec : OracleCode → OracleCode → OracleCode
  | rfind : OracleCode → OracleCode
  deriving DecidableEq, Encodable

namespace OracleCode

instance : Countable OracleCode := Encodable.countable

/-- The compositional interpretation of a code relative to the oracle `X`. Each clause is the
corresponding clause of `Nat.RecursiveIn`; `oracle` is interpreted as `X` itself. -/
def evalIn (X : ℕ →. ℕ) : OracleCode → ℕ →. ℕ
  | zero => fun _ => 0
  | succ => Nat.succ
  | left => fun n => (Nat.unpair n).1
  | right => fun n => (Nat.unpair n).2
  | oracle => X
  | pair cf cg => fun n => Nat.pair <$> evalIn X cf n <*> evalIn X cg n
  | comp cf cg => fun n => evalIn X cg n >>= evalIn X cf
  | prec cf cg => fun p =>
      let (a, n) := Nat.unpair p
      n.rec (evalIn X cf a) fun y IH => do
        let i ← IH
        evalIn X cg (Nat.pair a (Nat.pair y i))
  | rfind cf => fun a => Nat.rfind fun n => (fun m => m = 0) <$> evalIn X cf (Nat.pair a n)

variable (X : ℕ →. ℕ)

@[simp] theorem evalIn_zero : evalIn X zero = fun _ => 0 := rfl
@[simp] theorem evalIn_succ : evalIn X succ = Nat.succ := rfl
@[simp] theorem evalIn_left : evalIn X left = fun n => (Nat.unpair n).1 := rfl
@[simp] theorem evalIn_right : evalIn X right = fun n => (Nat.unpair n).2 := rfl
/-- **The oracle instruction is interpreted as the oracle itself.** -/
@[simp] theorem evalIn_oracle : evalIn X oracle = X := rfl
@[simp] theorem evalIn_pair (cf cg : OracleCode) :
    evalIn X (pair cf cg) = fun n => Nat.pair <$> evalIn X cf n <*> evalIn X cg n := rfl
@[simp] theorem evalIn_comp (cf cg : OracleCode) :
    evalIn X (comp cf cg) = fun n => evalIn X cg n >>= evalIn X cf := rfl
@[simp] theorem evalIn_rfind (cf : OracleCode) :
    evalIn X (rfind cf) =
      fun a => Nat.rfind fun n => (fun m => m = 0) <$> evalIn X cf (Nat.pair a n) := rfl

/-- **Soundness**: every interpreted code is recursive in the singleton oracle `{X}`. -/
theorem evalIn_recursiveIn : ∀ c : OracleCode, Nat.RecursiveIn {X} (evalIn X c)
  | zero => .zero
  | succ => .succ
  | left => .left
  | right => .right
  | oracle => .oracle X rfl
  | pair cf cg => .pair (evalIn_recursiveIn cf) (evalIn_recursiveIn cg)
  | comp cf cg => .comp (evalIn_recursiveIn cf) (evalIn_recursiveIn cg)
  | prec cf cg => .prec (evalIn_recursiveIn cf) (evalIn_recursiveIn cg)
  | rfind cf => .rfind (evalIn_recursiveIn cf)

/-- **Completeness**: every function recursive in `{X}` is the interpretation of some code. The
oracle case eliminates singleton membership; the result is an existential proposition. -/
theorem exists_code {f : ℕ →. ℕ} (h : Nat.RecursiveIn {X} f) :
    ∃ c : OracleCode, evalIn X c = f := by
  induction h with
  | zero => exact ⟨zero, rfl⟩
  | succ => exact ⟨succ, rfl⟩
  | left => exact ⟨left, rfl⟩
  | right => exact ⟨right, rfl⟩
  | oracle g hg =>
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact ⟨oracle, rfl⟩
  | pair _ _ ihf ihg =>
    obtain ⟨cf, rfl⟩ := ihf
    obtain ⟨cg, rfl⟩ := ihg
    exact ⟨pair cf cg, rfl⟩
  | comp _ _ ihf ihg =>
    obtain ⟨cf, rfl⟩ := ihf
    obtain ⟨cg, rfl⟩ := ihg
    exact ⟨comp cf cg, rfl⟩
  | prec _ _ ihf ihg =>
    obtain ⟨cf, rfl⟩ := ihf
    obtain ⟨cg, rfl⟩ := ihg
    exact ⟨prec cf cg, rfl⟩
  | rfind _ ihf =>
    obtain ⟨cf, rfl⟩ := ihf
    exact ⟨rfind cf, rfl⟩

/-- **Representation**: recursive in `{X}` is exactly "interpretation of some code". -/
theorem nat_recursiveIn_iff {f : ℕ →. ℕ} :
    Nat.RecursiveIn {X} f ↔ ∃ c : OracleCode, evalIn X c = f :=
  ⟨exists_code X, fun ⟨c, hc⟩ => hc ▸ evalIn_recursiveIn X c⟩

/-- The typed form on naturals, through `RecursiveIn.iff_nat`. -/
theorem recursiveIn_iff {f : ℕ →. ℕ} :
    RecursiveIn {X} f ↔ ∃ c : OracleCode, evalIn X c = f := by
  rw [RecursiveIn.iff_nat]
  exact nat_recursiveIn_iff X

/-- The functions recursive in `{X}` are the range of the interpretation. -/
theorem setOf_recursiveIn_eq_range :
    {f : ℕ →. ℕ | RecursiveIn {X} f} = Set.range (evalIn X) := by
  ext f
  rw [Set.mem_setOf_eq, Set.mem_range, recursiveIn_iff]

/-- **Countability**: the functions `ℕ →. ℕ` recursive in one fixed oracle form a countable set.
Stated for a singleton oracle set; nothing is claimed for an arbitrary set of oracles. -/
theorem countable_setOf_recursiveIn : Set.Countable {f : ℕ →. ℕ | RecursiveIn {X} f} := by
  rw [setOf_recursiveIn_eq_range]
  exact Set.countable_range _

/-- The derived numbering decodes its own codes. -/
theorem decode_encode (c : OracleCode) : (decode (encode c) : Option OracleCode) = Option.some c :=
  encodek c

end OracleCode
