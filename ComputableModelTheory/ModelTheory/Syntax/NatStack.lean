/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.Encoding
import ComputableModelTheory.ModelTheory.Syntax.Primcodable

/-!
# The term stack machine on natural-number codes

`natDecodeStack` is the term stack machine (`Term.decodeStack`) transported to the level
of natural-number symbol codes: even codes are variable leaves, odd codes are function
symbols whose arity is read off the code through the language's symbol decoding. The
machine is uniform in the variable type — that uniformity is the point: it is the only
level at which the `Primcodable` instance for `Σ k, L.Term (α ⊕ Fin k)` can state its
primitive recursion witness uniformly in `k`.

This file defines the machine and its step invariants, proves the machine primitive
recursive, proves it sound against each fiber's `decodeStack`, and provides the code
canonicalization for the term alphabet, in that order below.
-/

open Encodable

namespace FirstOrder.Language.Term

variable (L : Language) [L.EffectiveLanguage]

/-- The arity of the function symbol coded by `c`, if any. -/
def arityOfCode (c : ℕ) : Option ℕ :=
  (decode (α := Σ i, L.Functions i) c).map (·.1)

/-- One step of the term stack machine at the level of natural-number symbol codes.
Even codes are variable leaves; odd codes are function symbols, whose arity is read off
the code. The machine is uniform in the variable type: only the language's symbol
decoding enters. -/
def natDecodeStackStep (c : ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
  if c % 2 = 1 then
    match arityOfCode L (c / 2) with
    | some n => if n ≤ acc.length then (c :: (acc.take n).flatten) :: acc.drop n else []
    | none => []
  else [c] :: acc

/-- The term stack machine at the level of natural-number symbol codes. -/
def natDecodeStack (l : List ℕ) : List (List ℕ) :=
  l.foldr (natDecodeStackStep L) []

@[simp]
theorem natDecodeStack_nil : natDecodeStack L [] = [] := rfl

theorem natDecodeStack_cons (c : ℕ) (l : List ℕ) :
    natDecodeStack L (c :: l) = natDecodeStackStep L c (natDecodeStack L l) := rfl

theorem natDecodeStackStep_even {c : ℕ} (h : c % 2 = 0) (acc : List (List ℕ)) :
    natDecodeStackStep L c acc = [c] :: acc := by
  rw [natDecodeStackStep, if_neg (by omega)]

theorem natDecodeStackStep_odd_some {c n : ℕ} (h : c % 2 = 1)
    (ha : arityOfCode L (c / 2) = some n) (acc : List (List ℕ)) :
    natDecodeStackStep L c acc =
      if n ≤ acc.length then (c :: (acc.take n).flatten) :: acc.drop n else [] := by
  rw [natDecodeStackStep, if_pos h, ha]

theorem natDecodeStackStep_odd_none {c : ℕ} (h : c % 2 = 1)
    (ha : arityOfCode L (c / 2) = none) (acc : List (List ℕ)) :
    natDecodeStackStep L c acc = [] := by
  rw [natDecodeStackStep, if_pos h, ha]

/-- On the code of a variable leaf, the step pushes a singleton. -/
theorem natDecodeStackStep_encode_inl {β : Type*} [Primcodable β] (b : β)
    (acc : List (List ℕ)) :
    natDecodeStackStep L (encode (Sum.inl b : β ⊕ (Σ i, L.Functions i))) acc =
      [encode (Sum.inl b : β ⊕ (Σ i, L.Functions i))] :: acc :=
  natDecodeStackStep_even L (by rw [encode_sum_inl]; omega) acc

/-- On the code of a function symbol, the step reads off exactly that symbol's arity. -/
theorem natDecodeStackStep_encode_inr {β : Type*} [Primcodable β]
    (s : Σ i, L.Functions i) (acc : List (List ℕ)) :
    natDecodeStackStep L (encode (Sum.inr s : β ⊕ (Σ i, L.Functions i))) acc =
      if s.1 ≤ acc.length then
        (encode (Sum.inr s : β ⊕ (Σ i, L.Functions i)) :: (acc.take s.1).flatten) ::
          acc.drop s.1
      else [] := by
  have henc : encode (Sum.inr s : β ⊕ (Σ i, L.Functions i)) = 2 * encode s + 1 :=
    encode_sum_inr s
  have h1 : encode (Sum.inr s : β ⊕ (Σ i, L.Functions i)) % 2 = 1 := by omega
  have h2 : encode (Sum.inr s : β ⊕ (Σ i, L.Functions i)) / 2 = encode s := by omega
  rw [natDecodeStackStep_odd_some L h1 (by rw [h2, arityOfCode, encodek]; rfl)]

/-! ### Primitive recursiveness -/


/-- Reading the arity off a symbol code is primitive recursive. -/
theorem primrec_arityOfCode : Primrec (arityOfCode L) :=
  Primrec.option_map Primrec.decode
    (((primrec_functionSymbol_arity (L := L)).comp Primrec.snd).to₂)

/-- The code-level stack machine step is primitive recursive. -/
theorem primrec_natDecodeStackStep : Primrec₂ (natDecodeStackStep L) := by
  have hbranch : Primrec fun p : ℕ × List (List ℕ) ↦
      Option.casesOn (motive := fun _ ↦ List (List ℕ)) (arityOfCode L (p.1 / 2)) []
        fun n ↦ if n ≤ p.2.length then (p.1 :: (p.2.take n).flatten) :: p.2.drop n
          else [] := by
    have ho : Primrec fun p : ℕ × List (List ℕ) ↦ arityOfCode L (p.1 / 2) :=
      (primrec_arityOfCode L).comp
        (Primrec.nat_div.comp Primrec.fst (Primrec.const 2))
    have hg : Primrec₂ fun (p : ℕ × List (List ℕ)) (n : ℕ) ↦
        if n ≤ p.2.length then (p.1 :: (p.2.take n).flatten) :: p.2.drop n else [] := by
      have hn : Primrec fun q : (ℕ × List (List ℕ)) × ℕ ↦ q.2 := Primrec.snd
      have hacc : Primrec fun q : (ℕ × List (List ℕ)) × ℕ ↦ q.1.2 :=
        Primrec.snd.comp Primrec.fst
      exact (Primrec.ite (Primrec.nat_le.comp hn (Primrec.list_length.comp hacc))
        (Primrec.list_cons.comp
          (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
            (Primrec.list_flatten.comp (Primrec.list_take.comp hn hacc)))
          (Primrec.list_drop.comp hn hacc))
        (Primrec.const [])).to₂
    exact Primrec.option_casesOn ho (Primrec.const []) hg
  have hwhole : Primrec fun p : ℕ × List (List ℕ) ↦
      if p.1 % 2 = 1 then
        Option.casesOn (motive := fun _ ↦ List (List ℕ)) (arityOfCode L (p.1 / 2)) []
          fun n ↦ if n ≤ p.2.length then (p.1 :: (p.2.take n).flatten) :: p.2.drop n
            else []
      else [p.1] :: p.2 :=
    Primrec.ite
      (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2))
        (Primrec.const 1))
      hbranch
      (Primrec.list_cons.comp
        (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) Primrec.snd)
  have h2 : Primrec fun p : ℕ × List (List ℕ) ↦ natDecodeStackStep L p.1 p.2 := by
    refine hwhole.of_eq fun p ↦ ?_
    rcases p with ⟨c, acc⟩
    rw [natDecodeStackStep]
    rcases arityOfCode L (c / 2) with - | n <;> rfl
  exact h2

/-- The code-level stack machine is primitive recursive. -/
theorem primrec_natDecodeStack : Primrec (natDecodeStack L) := by
  have hfold : Primrec fun l : List ℕ ↦
      l.foldr (fun c s ↦ natDecodeStackStep L c s) [] :=
    Primrec.list_foldr Primrec.id (Primrec.const [])
      (((primrec_natDecodeStackStep L).comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂)
  exact hfold.of_eq fun l ↦ rfl

/-! ### Soundness -/


/-- Soundness of the code-level machine: on encode-images it computes exactly the
fiber machine `decodeStack`, uniformly in the variable type. -/
theorem natDecodeStack_map_encode {β : Type*} [Primcodable β]
    (l : List (β ⊕ (Σ i, L.Functions i))) :
    natDecodeStack L (l.map encode) = (decodeStack l).map (List.map encode) := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    rw [List.map_cons, natDecodeStack_cons, ih,
      show decodeStack (g :: l) = decodeStackStep g (decodeStack l) from rfl]
    cases g with
    | inl b => rw [natDecodeStackStep_encode_inl]; rfl
    | inr s =>
      rw [natDecodeStackStep_encode_inr, decodeStackStep]
      rw [List.length_map]
      by_cases h : s.1 ≤ (decodeStack l).length
      · rw [if_pos h, if_pos h, List.map_cons, List.map_cons, ← List.map_drop,
          ← List.map_take, List.map_flatten]
      · rw [if_neg h, if_neg h]
        rfl

/-! ### Canonicalization -/

variable (α : Type*) [Primcodable α]


/-- Canonicalize one symbol code of the term alphabet `(α ⊕ Fin k) ⊕ (Σ i, L.Functions i)`:
recode whatever the code decodes to, uniformly in `k`. Only the `Fin` bound depends on
`k`, and only as a value. -/
def canonCode (k c : ℕ) : Option ℕ :=
  if c % 2 = 1 then
    (decode (α := Σ i, L.Functions i) (c / 2)).map fun s ↦ 2 * encode s + 1
  else if (c / 2) % 2 = 1 then
    if (c / 2) / 2 < k then some c else none
  else
    (decode (α := α) ((c / 2) / 2)).map fun a ↦ 4 * encode a

/-- `canonCode` is exactly fiber decoding followed by re-encoding. -/
theorem canonCode_eq (k c : ℕ) :
    canonCode L α k c =
      (decode (α := (α ⊕ Fin k) ⊕ (Σ i, L.Functions i)) c).map encode := by
  by_cases h : c % 2 = 1
  · rw [canonCode, if_pos h, decode_sum_odd h, Option.map_map]
    rcases decode (α := Σ i, L.Functions i) (c / 2) with - | s
    · rfl
    · rfl
  · have h0 : c % 2 = 0 := by omega
    rw [canonCode, if_neg h, decode_sum_even h0, Option.map_map]
    by_cases h1 : (c / 2) % 2 = 1
    · rw [if_pos h1, decode_sum_odd h1, Option.map_map]
      by_cases h2 : (c / 2) / 2 < k
      · rw [if_pos h2, decode_fin_of_lt h2]
        simp only [Option.map_some, Function.comp_apply, encode_sum_inl, encode_sum_inr,
          encode_fin_val]
        exact congrArg some (by omega)
      · rw [if_neg h2, decode_fin_eq_none_of_le (Nat.not_lt.1 h2)]
        rfl
    · have h10 : (c / 2) % 2 = 0 := by omega
      rw [if_neg h1, decode_sum_even h10, Option.map_map]
      rcases decode (α := α) ((c / 2) / 2) with - | a
      · rfl
      · simp only [Option.map_some, Function.comp_apply, encode_sum_inl]
        exact congrArg some (by omega)

attribute [irreducible] canonCode

/-- Canonicalize a list of symbol codes elementwise. -/
def canonAll (k : ℕ) : List ℕ → Option (List ℕ)
  | [] => some []
  | c :: cs => (canonCode L α k c).bind fun c' ↦ (canonAll k cs).map (c' :: ·)

/-- `canonAll` is exactly elementwise fiber decoding followed by re-encoding. -/
theorem canonAll_eq (k : ℕ) (cs : List ℕ) :
    canonAll L α k cs =
      (decodeAll ((α ⊕ Fin k) ⊕ (Σ i, L.Functions i)) cs).map (List.map encode) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [canonAll, decodeAll_cons, ih, canonCode_eq]
    rcases decode (α := (α ⊕ Fin k) ⊕ (Σ i, L.Functions i)) c with - | g
    · rfl
    · rcases decodeAll ((α ⊕ Fin k) ⊕ (Σ i, L.Functions i)) cs with - | l <;> rfl

/-- `canonCode` is primitive recursive, jointly in the bound and the code. -/
theorem primrec₂_canonCode : Primrec₂ (canonCode L α) := by
  have hc2 : Primrec fun p : ℕ × ℕ ↦ p.2 / 2 :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have hc4 : Primrec fun p : ℕ × ℕ ↦ p.2 / 2 / 2 :=
    Primrec.nat_div.comp hc2 (Primrec.const 2)
  have hsym : Primrec fun p : ℕ × ℕ ↦
      (decode (α := Σ i, L.Functions i) (p.2 / 2)).map fun s ↦ 2 * encode s + 1 :=
    Primrec.option_map (Primrec.decode.comp hc2)
      ((Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.encode.comp Primrec.snd))).to₂)
  have hfin : Primrec fun p : ℕ × ℕ ↦
      if p.2 / 2 / 2 < p.1 then some p.2 else none :=
    Primrec.ite (Primrec.nat_lt.comp hc4 Primrec.fst)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  have hvar : Primrec fun p : ℕ × ℕ ↦
      (decode (α := α) (p.2 / 2 / 2)).map fun a ↦ 4 * encode a :=
    Primrec.option_map (Primrec.decode.comp hc4)
      ((Primrec.nat_mul.comp (Primrec.const 4) (Primrec.encode.comp Primrec.snd)).to₂)
  have hw : Primrec fun p : ℕ × ℕ ↦
      if p.2 % 2 = 1 then
        (decode (α := Σ i, L.Functions i) (p.2 / 2)).map fun s ↦ 2 * encode s + 1
      else if (p.2 / 2) % 2 = 1 then
        if (p.2 / 2) / 2 < p.1 then some p.2 else none
      else
        (decode (α := α) ((p.2 / 2) / 2)).map fun a ↦ 4 * encode a :=
    Primrec.ite
      (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
        (Primrec.const 1))
      hsym
      (Primrec.ite
        (Primrec.eq.comp (Primrec.nat_mod.comp hc2 (Primrec.const 2)) (Primrec.const 1))
        hfin hvar)
  have h2 : Primrec fun p : ℕ × ℕ ↦ canonCode L α p.1 p.2 :=
    hw.of_eq fun p ↦ by rw [canonCode]
  exact h2

/-- `canonAll` is primitive recursive, jointly in the code list and the bound. -/
theorem primrec₂_canonAll : Primrec₂ fun (cs : List ℕ) (k : ℕ) ↦ canonAll L α k cs := by
  have hcc : Primrec fun r : (List ℕ × ℕ) × ℕ × Option (List ℕ) ↦
      canonCode L α r.1.2 r.2.1 :=
    (primrec₂_canonCode L α).comp (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  have hmap : Primrec fun a : ((List ℕ × ℕ) × ℕ × Option (List ℕ)) × ℕ ↦
      (a.1.2.2).map (a.2 :: ·) :=
    Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      ((Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂)
  have hfold : Primrec fun p : List ℕ × ℕ ↦
      p.1.foldr
        (fun c s ↦ (canonCode L α p.2 c).bind fun c' ↦ s.map (c' :: ·))
        (some []) :=
    Primrec.list_foldr Primrec.fst (Primrec.const (some []))
      ((Primrec.option_bind hcc hmap.to₂).to₂)
  have h2 : Primrec fun p : List ℕ × ℕ ↦ canonAll L α p.2 p.1 := by
    refine hfold.of_eq fun p ↦ ?_
    obtain ⟨cs, k⟩ := p
    induction cs with
    | nil => rfl
    | cons c cs ih => simp only [List.foldr_cons, ih]; rfl
  exact h2

end FirstOrder.Language.Term
