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
variable {α σ : Type*} [Primcodable α] [Primcodable σ]

/-- Primitive recursion with a computed recursion argument at the `ℕ` level. -/
theorem test_recursiveIn_prec' {f g h : ℕ →. ℕ} (hf : Nat.RecursiveIn O f)
    (hg : Nat.RecursiveIn O g) (hh : Nat.RecursiveIn O h) :
    Nat.RecursiveIn O fun a ↦ (f a).bind fun n ↦ n.rec (g a)
      fun y IH ↦ do {let i ← IH; h (Nat.pair a (Nat.pair y i))} :=
  Nat.RecursiveIn.prec' hf hg hh

/-- Primitive recursion with partial base and step, at the typed level. -/
theorem test_recursiveIn_nat_rec {f : α → ℕ} {g : α →. σ} {h : α → ℕ × σ →. σ}
    (hf : ComputableIn O f) (hg : RecursiveIn O g) (hh : RecursiveIn₂ O h) :
    RecursiveIn O fun a ↦ (f a).rec (g a) fun y IH ↦ IH.bind fun i ↦ h a (y, i) :=
  RecursiveIn.nat_rec hf hg hh

/-- Case-analysis gate: the predecessor by cases is computable in any oracle set. -/
theorem test_computableIn_nat_casesOn :
    ComputableIn O fun p : ℕ × ℕ ↦
      Nat.casesOn (motive := fun _ ↦ ℕ) p.1 p.2 fun y ↦ y :=
  ComputableIn.nat_casesOn ComputableIn.fst ComputableIn.snd
    Computable.snd.computableIn.to₂

/-- Semantic equation: the case analysis returns the predecessor on successors. -/
theorem test_nat_casesOn_value :
    Nat.casesOn (motive := fun _ ↦ ℕ) 3 5 (fun y ↦ y) = 2 :=
  rfl

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

/-- List-map gate: doubling every entry is computable in any oracle set. -/
theorem test_computableIn_list_map :
    ComputableIn O fun l : List ℕ ↦ l.map fun b ↦ b + b :=
  ComputableIn.list_map ComputableIn.id
    ((Primrec.nat_add.comp Primrec.snd Primrec.snd).to_comp.computableIn.to₂)

/-- Semantic equation: the map doubles the list. -/
theorem test_list_map_value : ([1, 2, 3] : List ℕ).map (fun b ↦ b + b) = [2, 4, 6] :=
  rfl

/-- Option case analysis gate: `Option.getD` via cases is computable in any oracle
set. -/
theorem test_computableIn_option_casesOn {f : α → Option ℕ} (hf : ComputableIn O f) :
    ComputableIn O fun a ↦ Option.casesOn (motive := fun _ ↦ ℕ) (f a) 0 fun b ↦ b :=
  ComputableIn.option_casesOn hf (ComputableIn.const 0) ComputableIn.snd.to₂

/-- Sum case analysis gate: `Sum.elim` of oracle-computable functions is computable in
any oracle set. -/
theorem test_computableIn_sumCasesOn {f : α → ℕ ⊕ ℕ} (hf : ComputableIn O f) :
    ComputableIn O fun a ↦ Sum.casesOn (motive := fun _ ↦ ℕ) (f a) (fun b ↦ b) fun c ↦
      c + 1 :=
  ComputableIn.sumCasesOn hf ComputableIn.snd.to₂
    ((Primrec.succ.comp Primrec.snd).to_comp.computableIn.to₂)

/-- Strong recursion gate: the powers of two, defined by doubling the last entry of the
course-of-values list, are computable in any oracle set. -/
theorem test_computableIn_nat_strong_rec :
    ComputableIn₂ O fun (_ : Unit) (n : ℕ) ↦ 2 ^ n := by
  have hlen : ComputableIn O fun p : Unit × List ℕ ↦ p.2.length :=
    (Primrec.list_length.to_comp.computableIn).comp ComputableIn.snd
  have hg : ComputableIn₂ O fun (_ : Unit) (l : List ℕ) ↦
      Option.some ((l[l.length - 1]?.map (2 * ·)).getD 1) :=
    (ComputableIn.option_some.comp
      (ComputableIn.option_getD
        (ComputableIn.option_map
          ((Computable.list_getElem?.computableIn₂ (O := O)).comp ComputableIn.snd
            ((Primrec.pred.to_comp.computableIn).comp hlen))
          (((Primrec.nat_mul.to_comp.computableIn₂ (O := O)).comp
            (ComputableIn.const 2) ComputableIn.snd).to₂))
        (ComputableIn.const 1))).to₂
  refine ComputableIn.nat_strong_rec _ hg fun _ n ↦ ?_
  cases n with
  | zero => simp
  | succ m => simp [pow_succ, Nat.mul_comm]

/-- Semantic equation: the strong-recursion guess function recovers the next power of
two from the course-of-values list. -/
theorem test_nat_strong_rec_value :
    ((([1, 2, 4] : List ℕ)[2]?.map (2 * ·)).getD 1 : ℕ) = 2 ^ 3 :=
  rfl

end

#assert_standard_axioms test_computableIn_option_casesOn
#assert_standard_axioms test_computableIn_sumCasesOn
#assert_standard_axioms test_recursiveIn_prec'
#assert_standard_axioms test_recursiveIn_nat_rec
#assert_standard_axioms test_computableIn_nat_casesOn
#assert_standard_axioms test_nat_casesOn_value
#assert_standard_axioms test_computableIn_nat_rec
#assert_standard_axioms test_nat_rec_value
#assert_standard_axioms test_computableIn_nat_iterate
#assert_standard_axioms test_nat_iterate_value
#assert_standard_axioms test_computableIn_list_foldl
#assert_standard_axioms test_list_foldl_value
#assert_standard_axioms test_computableIn_list_foldr
#assert_standard_axioms test_list_foldr_value
#assert_standard_axioms test_computableIn_list_map
#assert_standard_axioms test_list_map_value
#assert_standard_axioms test_computableIn_nat_strong_rec
#assert_standard_axioms test_nat_strong_rec_value
