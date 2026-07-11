/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.ComputableOps
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for computable term operations

Named acceptance tests for the list-level shadows and computability of term operations,
checked by `#assert_standard_axioms`. Outside the root import spine; CI checks it
explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Syntax/ComputableOpsAudit.lean
```
-/

open Encodable FirstOrder Language Language.Term

section

variable {L : Language} {α β : Type*} [Primcodable α] [Primcodable β] [L.EffectiveLanguage]

omit [Primcodable α] [Primcodable β] [L.EffectiveLanguage] in
/-- The relabelling shadow: `listEncode` intertwines `relabel` with a symbol map. -/
theorem test_listEncode_relabel (g : α → β) (t : L.Term α) :
    (t.relabel g).listEncode = t.listEncode.map (Sum.map g id) :=
  listEncode_relabel g t

omit [Primcodable α] [Primcodable β] [L.EffectiveLanguage] in
/-- The substitution shadow: `listEncode` intertwines `subst` with a symbol `flatMap`. -/
theorem test_listEncode_subst (σf : α → L.Term β) (t : L.Term α) :
    (t.subst σf).listEncode =
      t.listEncode.flatMap
        (Sum.elim (fun a ↦ (σf a).listEncode) fun F ↦ [Sum.inr F]) :=
  listEncode_subst σf t

/-- `listEncode` is primitive recursive. -/
theorem test_primrec_listEncode :
    Primrec (listEncode : L.Term α → List (α ⊕ (Σ i, L.Functions i))) :=
  primrec_listEncode

/-- Reading off the first decoded term is primitive recursive. -/
theorem test_primrec_listDecode_head? :
    Primrec fun l : List (α ⊕ (Σ i, L.Functions i)) ↦ (Term.listDecode l).head? :=
  primrec_listDecode_head?

/-- The variable constructor is primitive recursive. -/
theorem test_primrec_var : Primrec (Term.var : α → L.Term α) :=
  primrec_var

/-- Relabelling along a primitive recursive map is primitive recursive. -/
theorem test_primrec_relabel {g : α → β} (hg : Primrec g) :
    Primrec fun t : L.Term α ↦ t.relabel g :=
  primrec_relabel hg

/-- Substitution along a primitive recursive assignment is primitive recursive. -/
theorem test_primrec_subst {σf : α → L.Term β} (hσ : Primrec σf) :
    Primrec fun t : L.Term α ↦ t.subst σf :=
  primrec_subst hσ

/-- The public contract: the variable constructor is computable. -/
theorem test_computable_var : Computable (Term.var : α → L.Term α) :=
  computable_var

/-- The public contract: relabelling along a merely computable map is computable. -/
theorem test_computable_relabel {g : α → β} (hg : Computable g) :
    Computable fun t : L.Term α ↦ t.relabel g :=
  computable_relabel hg

/-- The public contract: substitution along a merely computable assignment is
computable. -/
theorem test_computable_subst {σf : α → L.Term β} (hσ : Computable σf) :
    Computable fun t : L.Term α ↦ t.subst σf :=
  computable_subst hσ

/-- Computable functions are closed under list map (the new combinator itself). -/
theorem test_computable_list_map {g : α → β} (hg : Computable g) :
    Computable fun l : List α ↦ l.map g :=
  Computable.list_map hg

end

#assert_standard_axioms test_listEncode_relabel
#assert_standard_axioms test_listEncode_subst
#assert_standard_axioms test_primrec_listEncode
#assert_standard_axioms test_primrec_listDecode_head?
#assert_standard_axioms test_primrec_var
#assert_standard_axioms test_primrec_relabel
#assert_standard_axioms test_primrec_subst
#assert_standard_axioms test_computable_var
#assert_standard_axioms test_computable_relabel
#assert_standard_axioms test_computable_subst
#assert_standard_axioms test_computable_list_map
