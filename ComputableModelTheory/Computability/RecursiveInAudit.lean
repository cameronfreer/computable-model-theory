/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.RecursiveIn
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for oracle recursion combinators

Named acceptance tests for the oracle-level recursion and fold combinators, checked by
`#assert_standard_axioms`. Each combinator gets both a computability gate and a semantic
equation exercising the computed value against the specification recursion on concrete
input. Outside the root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/Computability/RecursiveInAudit.lean
```
-/

section

variable {O : Set (ℕ →. ℕ)}

/-- Primitive recursion gate: the triangular-sum recursion is computable in any oracle
set. -/
theorem test_computableIn_nat_rec :
    ComputableIn O fun p : ℕ × ℕ ↦
      Nat.rec (motive := fun _ ↦ ℕ) p.2 (fun y IH ↦ y + IH) p.1 :=
  ComputableIn.nat_rec ComputableIn.fst ComputableIn.snd
    ((Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to_comp.computableIn.to₂)

/-- Semantic equation: the recursion computes the triangular sum. -/
theorem test_nat_rec_value :
    Nat.rec (motive := fun _ ↦ ℕ) 5 (fun y IH ↦ y + IH) 4 = 11 :=
  rfl

/-- Iteration gate: iterated successor is computable in any oracle set. -/
theorem test_computableIn_nat_iterate :
    ComputableIn O fun p : ℕ × ℕ ↦ Nat.succ^[p.1] p.2 :=
  ComputableIn.nat_iterate ComputableIn.fst ComputableIn.snd
    ((Primrec.succ.comp Primrec.snd).to_comp.computableIn.to₂)

/-- Semantic equation: iterating the successor adds the iteration count. -/
theorem test_nat_iterate_value : Nat.succ^[3] 4 = 7 :=
  rfl

/-- Left-fold gate: summing a list by a left fold is computable in any oracle set. -/
theorem test_computableIn_list_foldl :
    ComputableIn O fun l : List ℕ ↦ l.foldl (fun s b ↦ s + b) 0 :=
  ComputableIn.list_foldl ComputableIn.id (ComputableIn.const 0)
    ((Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to_comp.computableIn.to₂)

/-- Semantic equation: the left fold sums the list. -/
theorem test_list_foldl_value : ([1, 2, 3] : List ℕ).foldl (fun s b ↦ s + b) 0 = 6 :=
  rfl

/-- Right-fold gate: summing a list by a right fold is computable in any oracle set. -/
theorem test_computableIn_list_foldr :
    ComputableIn O fun l : List ℕ ↦ l.foldr (fun b s ↦ b + s) 0 :=
  ComputableIn.list_foldr ComputableIn.id (ComputableIn.const 0)
    ((Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to_comp.computableIn.to₂)

/-- Semantic equation: the right fold sums the list. -/
theorem test_list_foldr_value : ([1, 2, 3] : List ℕ).foldr (fun b s ↦ b + s) 0 = 6 :=
  rfl

end

#assert_standard_axioms test_computableIn_nat_rec
#assert_standard_axioms test_nat_rec_value
#assert_standard_axioms test_computableIn_nat_iterate
#assert_standard_axioms test_nat_iterate_value
#assert_standard_axioms test_computableIn_list_foldl
#assert_standard_axioms test_list_foldl_value
#assert_standard_axioms test_computableIn_list_foldr
#assert_standard_axioms test_list_foldr_value
