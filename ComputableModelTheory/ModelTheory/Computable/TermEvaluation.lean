/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Computable.Structure
import ComputableModelTheory.ModelTheory.Syntax.ComputableOps
import Mathlib.ModelTheory.Semantics

/-!
# Computable term evaluation

In an ω-presented computable structure, term evaluation is computable in the oracle:
`realize_computableIn` gives `ComputableIn O` of
`fun p : L.Term (Fin m) × (Fin m → ℕ) ↦ p.1.realize p.2`.

The witness is a value-stack machine (`valueStack`): the mirror of `Term.listDecode`
whose stack holds values rather than terms, folding `valueStep` over the term's
`listEncode`. A variable symbol pushes its environment value; a function symbol
assembles uniform application data from itself and its arity's worth of stack values —
by decoding the code of the symbol/argument-list pair, which succeeds exactly on
matching lengths (`FunctionApplicationData.decode_encode`) — and pushes the uniform
`funMap` of the data. The machine equation `valueStack_eq_map_realize` states the stack
computes the realizations of `listDecode`'s terms, and the oracle fold
`ComputableIn.list_foldr` with the uniform `IsComputableStructureIn.funMap_computableIn`
field carries the computability.
-/

open Encodable FirstOrder Language

namespace FirstOrder.Language

variable {L : Language} [L.EffectiveLanguage]

/-- Decoding the code of a symbol/argument-list pair as function application data
succeeds exactly on matching lengths, yielding the packaged data. -/
theorem FunctionApplicationData.decode_encode (p : L.FunctionSymbol × List ℕ) :
    decode (α := FunctionApplicationData L ℕ) (encode p) =
      if h : p.2.length = p.1.arity then
        some (FunctionApplicationData.equivSubtype.symm ⟨p, h⟩)
      else none := by
  rw [decode_ofEquiv FunctionApplicationData.equivSubtype (encode p),
    show decode (α := { q : L.FunctionSymbol × List ℕ // q.2.length = q.1.arity })
        (encode p) = Encodable.decodeSubtype (encode p) from rfl,
    Encodable.decodeSubtype, encodek]
  by_cases h : p.2.length = p.1.arity
  · simp [h]
  · simp [h]

omit [L.EffectiveLanguage] in
/-- Evaluating the data packaged from a symbol/argument-list pair. -/
theorem FunctionApplicationData.funMap_equivSubtype_symm [L.Structure ℕ]
    (p : L.FunctionSymbol × List ℕ) (h : p.2.length = p.1.arity) :
    (FunctionApplicationData.equivSubtype.symm ⟨p, h⟩ :
        FunctionApplicationData L ℕ).funMap =
      Structure.funMap p.1.2 fun i ↦ p.2.get (Fin.cast h.symm i) :=
  rfl

namespace Term

variable {m : ℕ}

section Machine

variable [L.Structure ℕ]

/-- One step of the value-stack machine: a variable pushes its environment value; a
function symbol consumes its arity in values through the uniform application data,
emptying the stack on underflow exactly as `Term.listDecode`'s guard does. -/
def valueStep (env : Fin m → ℕ) (g : Fin m ⊕ (Σ i, L.Functions i))
    (acc : List ℕ) : List ℕ :=
  match g with
  | Sum.inl i => env i :: acc
  | Sum.inr s =>
    ((decode (α := FunctionApplicationData L ℕ)
        (encode ((s, acc.take s.1) : L.FunctionSymbol × List ℕ))).map
      fun d ↦ d.funMap :: acc.drop s.1).getD []

/-- The value-stack machine: `listDecode` with each decoded term replaced by its value
under the environment. -/
def valueStack (env : Fin m → ℕ) (l : List (Fin m ⊕ (Σ i, L.Functions i))) : List ℕ :=
  l.foldr (valueStep env) []

/-- The value-stack machine computes term values: each entry of the decoded-term list,
realized under the environment. -/
theorem valueStack_eq_map_realize (env : Fin m → ℕ)
    (l : List (Fin m ⊕ (Σ i, L.Functions i))) :
    valueStack env l = (Term.listDecode l).map fun t ↦ t.realize env := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    have hstep : valueStack env (g :: l) = valueStep env g (valueStack env l) := rfl
    cases g with
    | inl i =>
      rw [hstep, ih, listDecode]
      rfl
    | inr s =>
      obtain ⟨n, f⟩ := s
      rw [hstep, ih, listDecode, valueStep, FunctionApplicationData.decode_encode]
      dsimp only
      by_cases h : n ≤ (listDecode l).length
      · rw [dif_pos (show (((listDecode l).map fun t ↦ t.realize env).take n).length =
            FunctionSymbol.arity (⟨n, f⟩ : L.FunctionSymbol) from by
              simp only [List.length_take, List.length_map]
              exact min_eq_left h),
          dif_pos h, Option.map_some, Option.getD_some, List.map_cons, ← List.map_drop]
        congr 1
        rw [FunctionApplicationData.funMap_equivSubtype_symm]
        show Structure.funMap f _ = Structure.funMap f _
        refine congrArg _ (funext fun i ↦ ?_)
        rw [List.get_eq_getElem, List.getElem_take, List.getElem_map]
        rfl
      · rw [dif_neg (show ¬(((listDecode l).map fun t ↦ t.realize env).take n).length =
            FunctionSymbol.arity (⟨n, f⟩ : L.FunctionSymbol) from by
              simp only [List.length_take, List.length_map]
              exact fun hc ↦ h (min_eq_left_iff.1 hc)),
          dif_neg h]
        rfl

end Machine

section Evaluation

variable (O : Set (ℕ →. ℕ)) [L.Structure ℕ] [IsComputableStructureIn O L]

set_option maxHeartbeats 1000000 in
/-- Term evaluation in a computable structure is computable in the oracle: the value
stack runs by an oracle fold whose function steps call the uniform `funMap`. -/
theorem realize_computableIn :
    ComputableIn O fun p : L.Term (Fin m) × (Fin m → ℕ) ↦ p.1.realize p.2 := by
  have hstep : ComputableIn₂ O fun (p : L.Term (Fin m) × (Fin m → ℕ))
      (q : (Fin m ⊕ (Σ i, L.Functions i)) × List ℕ) ↦ valueStep p.2 q.1 q.2 := by
    have hinl : ComputableIn₂ O fun (x : (L.Term (Fin m) × (Fin m → ℕ)) ×
        (Fin m ⊕ (Σ i, L.Functions i)) × List ℕ) (i : Fin m) ↦ x.1.2 i :: x.2.2 :=
      ((Computable.list_cons.computableIn₂).comp
        ((Computable.fin_app.computableIn₂).comp
          ((Computable.snd.computableIn).comp
            ((Computable.fst.computableIn).comp ComputableIn.fst))
          ComputableIn.snd)
        ((Computable.snd.computableIn).comp
          ((Computable.snd.computableIn).comp ComputableIn.fst))).to₂
    have hinr : ComputableIn₂ O fun (x : (L.Term (Fin m) × (Fin m → ℕ)) ×
        (Fin m ⊕ (Σ i, L.Functions i)) × List ℕ) (s : Σ i, L.Functions i) ↦
        ((decode (α := FunctionApplicationData L ℕ)
            (encode ((s, x.2.2.take s.1) : L.FunctionSymbol × List ℕ))).map
          fun d ↦ d.funMap :: x.2.2.drop s.1).getD [] := by
      have hacc : Computable fun y : ((L.Term (Fin m) × (Fin m → ℕ)) ×
          (Fin m ⊕ (Σ i, L.Functions i)) × List ℕ) × (Σ i, L.Functions i) ↦
          y.1.2.2 :=
        Computable.snd.comp (Computable.snd.comp Computable.fst)
      have harity : Computable fun y : ((L.Term (Fin m) × (Fin m → ℕ)) ×
          (Fin m ⊕ (Σ i, L.Functions i)) × List ℕ) × (Σ i, L.Functions i) ↦
          y.2.1 :=
        (primrec_functionSymbol_arity (L := L)).to_comp.comp Computable.snd
      have hdec : Computable fun y : ((L.Term (Fin m) × (Fin m → ℕ)) ×
          (Fin m ⊕ (Σ i, L.Functions i)) × List ℕ) × (Σ i, L.Functions i) ↦
          decode (α := FunctionApplicationData L ℕ)
            (encode ((y.2, y.1.2.2.take y.2.1) : L.FunctionSymbol × List ℕ)) :=
        Computable.decode.comp (Computable.encode.comp
          (Computable.snd.pair (Primrec.list_take.to_comp.comp harity hacc)))
      have hfun : ComputableIn₂ O fun (y : ((L.Term (Fin m) × (Fin m → ℕ)) ×
          (Fin m ⊕ (Σ i, L.Functions i)) × List ℕ) × (Σ i, L.Functions i))
          (d : FunctionApplicationData L ℕ) ↦ d.funMap :: y.1.2.2.drop y.2.1 :=
        ((Computable.list_cons.computableIn₂ (O := O)).comp
          ((IsComputableStructureIn.funMap_computableIn (O := O) (L := L)).comp
            ComputableIn.snd)
          ((Primrec.list_drop.to_comp.comp (harity.comp Computable.fst)
            (hacc.comp Computable.fst)).computableIn)).to₂
      exact ComputableIn.option_getD
        (ComputableIn.option_map hdec.computableIn hfun) (ComputableIn.const [])
    exact (ComputableIn.sumCasesOn (ComputableIn.fst.comp ComputableIn.snd)
      hinl hinr).of_eq fun x ↦ by rcases x with ⟨p, g | s, acc⟩ <;> rfl
  have hstack : ComputableIn O fun p : L.Term (Fin m) × (Fin m → ℕ) ↦
      valueStack p.2 p.1.listEncode :=
    (ComputableIn.list_foldr
      ((primrec_listEncode.to_comp.computableIn).comp ComputableIn.fst)
      (ComputableIn.const []) hstep).of_eq fun p ↦ rfl
  have h : ComputableIn O fun p : L.Term (Fin m) × (Fin m → ℕ) ↦
      ((valueStack p.2 p.1.listEncode).head?).getD 0 :=
    ComputableIn.option_getD
      ((Primrec.list_head?.to_comp.computableIn).comp hstack) (ComputableIn.const 0)
  refine h.of_eq fun p ↦ ?_
  have hdec1 : Term.listDecode (α := Fin m) p.1.listEncode = [p.1] := by
    have h := Term.listDecode_encode_list [p.1]
    rwa [List.flatMap_singleton] at h
  rw [valueStack_eq_map_realize, hdec1]
  rfl

end Evaluation

end Term

end FirstOrder.Language
