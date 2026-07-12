/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.ComputableAge

/-!
# Uniform term evaluation over a computable age

Terms with natural-number variables are evaluated uniformly in an age index and a list
environment: `ComputableAgeIn.termRealize` realizes a term at the structure of the
given index, reading variables from the list with default `0` out of range, and
`termRealize_computableIn` computes it by a single oracle program. The witness is the
value-stack machine of fixed-structure term evaluation with the age index and list
environment carried in the context: variables push their list lookup, function symbols
package application data and call the age's uniform function interpretation, and the
machine equation `termValueStack_eq_map_realize` identifies the stack with standard
realization. The evaluator is a reusable public interface, not internal to any single
proof.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]

namespace ComputableAgeIn

variable (K : ComputableAgeIn O L)

/-- The list environment as a total valuation: list lookup with default `0`. -/
def envFun (env : Tuple ℕ) : ℕ → ℕ :=
  fun n ↦ (env[n]?).getD 0

/-- Uniform term evaluation: realize a natural-variable term at the structure of the
given index, under a list environment. -/
def termRealize (p : (ℕ × Tuple ℕ) × L.Term ℕ) : ℕ :=
  @Term.realize L ℕ (K.structureAt p.1.1) ℕ (envFun p.1.2) p.2

/-- One step of the uniform value-stack machine: a variable pushes its environment
lookup; a function symbol consumes its arity in values through uniform application
data at the given index. -/
def termValueStep (i : ℕ) (env : Tuple ℕ) (g : ℕ ⊕ (Σ j, L.Functions j))
    (acc : List ℕ) : List ℕ :=
  match g with
  | Sum.inl n => envFun env n :: acc
  | Sum.inr s =>
    ((FunctionApplicationData.ofSymbolArgs? ((s, acc.take s.1) :
        L.FunctionSymbol × List ℕ)).map
      fun d ↦ @FunctionApplicationData.funMap L ℕ (K.structureAt i) d ::
        acc.drop s.1).getD []

/-- The uniform value-stack machine. -/
def termValueStack (i : ℕ) (env : Tuple ℕ)
    (l : List (ℕ ⊕ (Σ j, L.Functions j))) : List ℕ :=
  l.foldr (K.termValueStep i env) []

/-- The machine computes term values: each entry of the decoded-term list, realized at
the index's structure under the environment. -/
theorem termValueStack_eq_map_realize (i : ℕ) (env : Tuple ℕ)
    (l : List (ℕ ⊕ (Σ j, L.Functions j))) :
    K.termValueStack i env l =
      (Term.listDecode l).map fun t ↦
        @Term.realize L ℕ (K.structureAt i) ℕ (envFun env) t := by
  letI := K.structureAt i
  induction l with
  | nil => rfl
  | cons g l ih =>
    have hstep : K.termValueStack i env (g :: l) =
        K.termValueStep i env g (K.termValueStack i env l) := rfl
    cases g with
    | inl n =>
      rw [hstep, ih, Term.listDecode]
      rfl
    | inr s =>
      obtain ⟨n, f⟩ := s
      rw [hstep, ih, Term.listDecode, termValueStep,
        FunctionApplicationData.ofSymbolArgs?]
      dsimp only
      by_cases h : n ≤ (Term.listDecode l).length
      · rw [dif_pos (show (((Term.listDecode l).map fun t ↦
              t.realize (envFun env)).take n).length =
            FunctionSymbol.arity (⟨n, f⟩ : L.FunctionSymbol) from by
              simp only [List.length_take, List.length_map]
              exact min_eq_left h),
          dif_pos h, Option.map_some, Option.getD_some, List.map_cons,
          ← List.map_drop]
        congr 1
        rw [FunctionApplicationData.funMap_equivSubtype_symm]
        show Structure.funMap f _ = Structure.funMap f _
        refine congrArg _ (funext fun j ↦ ?_)
        rw [List.get_eq_getElem, List.getElem_take, List.getElem_map]
        rfl
      · rw [dif_neg (show ¬(((Term.listDecode l).map fun t ↦
              t.realize (envFun env)).take n).length =
            FunctionSymbol.arity (⟨n, f⟩ : L.FunctionSymbol) from by
              simp only [List.length_take, List.length_map]
              exact fun hc ↦ h (min_eq_left_iff.1 hc)),
          dif_neg h]
        rfl

set_option maxHeartbeats 1000000 in
/-- Uniform term evaluation is computable in the oracle: one program over the age
index, the list environment, and the term. -/
theorem termRealize_computableIn : ComputableIn O K.termRealize := by
  have hstep : ComputableIn₂ O fun (p : (ℕ × Tuple ℕ) × L.Term ℕ)
      (q : (ℕ ⊕ (Σ j, L.Functions j)) × List ℕ) ↦
      K.termValueStep p.1.1 p.1.2 q.1 q.2 := by
    have hinl : ComputableIn₂ O fun (x : ((ℕ × Tuple ℕ) × L.Term ℕ) ×
        (ℕ ⊕ (Σ j, L.Functions j)) × List ℕ) (n : ℕ) ↦
        envFun x.1.1.2 n :: x.2.2 :=
      ((Computable.list_cons.computableIn₂ (O := O)).comp
        ((Primrec.option_getD.comp
          (Primrec.list_getElem?.comp
            (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            Primrec.snd)
          (Primrec.const 0)).to_comp.computableIn)
        ((Primrec.snd.comp (Primrec.snd.comp
          Primrec.fst)).to_comp.computableIn)).to₂
    have hinr : ComputableIn₂ O fun (x : ((ℕ × Tuple ℕ) × L.Term ℕ) ×
        (ℕ ⊕ (Σ j, L.Functions j)) × List ℕ) (s : Σ j, L.Functions j) ↦
        ((FunctionApplicationData.ofSymbolArgs? ((s, x.2.2.take s.1) :
            L.FunctionSymbol × List ℕ)).map
          fun d ↦ @FunctionApplicationData.funMap L ℕ (K.structureAt x.1.1.1) d ::
            x.2.2.drop s.1).getD [] := by
      have hacc : Primrec fun y : (((ℕ × Tuple ℕ) × L.Term ℕ) ×
          (ℕ ⊕ (Σ j, L.Functions j)) × List ℕ) × (Σ j, L.Functions j) ↦
          y.1.2.2 :=
        Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
      have harity : Primrec fun y : (((ℕ × Tuple ℕ) × L.Term ℕ) ×
          (ℕ ⊕ (Σ j, L.Functions j)) × List ℕ) × (Σ j, L.Functions j) ↦
          y.2.1 :=
        (primrec_functionSymbol_arity (L := L)).comp Primrec.snd
      have hdec : Primrec fun y : (((ℕ × Tuple ℕ) × L.Term ℕ) ×
          (ℕ ⊕ (Σ j, L.Functions j)) × List ℕ) × (Σ j, L.Functions j) ↦
          FunctionApplicationData.ofSymbolArgs? ((y.2, y.1.2.2.take y.2.1) :
            L.FunctionSymbol × List ℕ) :=
        FunctionApplicationData.primrec_ofSymbolArgs?.comp
          (Primrec.snd.pair (Primrec.list_take.comp harity hacc))
      have hfun : ComputableIn₂ O fun (y : ((((ℕ × Tuple ℕ) × L.Term ℕ) ×
          (ℕ ⊕ (Σ j, L.Functions j)) × List ℕ) × (Σ j, L.Functions j)))
          (d : FunctionApplicationData L ℕ) ↦
          @FunctionApplicationData.funMap L ℕ (K.structureAt y.1.1.1.1) d ::
            y.1.2.2.drop y.2.1 :=
        ((Computable.list_cons.computableIn₂ (O := O)).comp
          ((K.funMap_computableIn).comp
            (((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
              (Primrec.fst.comp Primrec.fst)))).to_comp.computableIn).pair
              ComputableIn.snd))
          (((Primrec.list_drop.comp
            ((primrec_functionSymbol_arity (L := L)).comp
              (Primrec.snd.comp Primrec.fst))
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp
              Primrec.fst)))).to_comp).computableIn)).to₂
      exact ComputableIn.option_getD
        (ComputableIn.option_map (hdec.to_comp.computableIn) hfun)
        (ComputableIn.const [])
    exact (ComputableIn.sumCasesOn (ComputableIn.fst.comp ComputableIn.snd)
      hinl hinr).of_eq fun x ↦ by rcases x with ⟨p, g | s, acc⟩ <;> rfl
  have hstack : ComputableIn O fun p : (ℕ × Tuple ℕ) × L.Term ℕ ↦
      K.termValueStack p.1.1 p.1.2 p.2.listEncode :=
    (ComputableIn.list_foldr
      ((Term.primrec_listEncode.to_comp.computableIn).comp ComputableIn.snd)
      (ComputableIn.const []) hstep).of_eq fun p ↦ rfl
  have h : ComputableIn O fun p : (ℕ × Tuple ℕ) × L.Term ℕ ↦
      ((K.termValueStack p.1.1 p.1.2 p.2.listEncode).head?).getD 0 :=
    ComputableIn.option_getD
      ((Primrec.list_head?.to_comp.computableIn).comp hstack) (ComputableIn.const 0)
  refine h.of_eq fun p ↦ ?_
  have hdec1 : Term.listDecode (α := ℕ) p.2.listEncode = [p.2] := by
    have h := Term.listDecode_encode_list [p.2]
    rwa [List.flatMap_singleton] at h
  rw [termValueStack_eq_map_realize, hdec1]
  rfl

end ComputableAgeIn

end FirstOrder.Language
