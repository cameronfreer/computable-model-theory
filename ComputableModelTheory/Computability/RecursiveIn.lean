/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.RecursiveIn

/-!
# Typed combinators for relative computability

This file supplements `Mathlib.Computability.RecursiveIn` with typed combinators for
`RecursiveIn` and `ComputableIn`: composition, pairing, bind, map, Boolean conditionals,
μ-search, primitive recursion (`Nat.RecursiveIn.prec'` through `ComputableIn.nat_rec`,
`nat_casesOn`, and `nat_iterate`), list folds (`ComputableIn.list_foldl` and
`list_foldr`, by running the fold as a partial recursion over positions and discharging
totality), and option and sum case analysis (through
`RecursiveIn.nat_casesOn_right` and the `decode` bridges, mirroring the absolute
proofs), together with thin domain and specification wrappers for `Nat.rfind` over
total `Bool`-valued predicates. Each combinator is proved by descending to the
`Nat.RecursiveIn` constructors through `Primcodable` encodings, following the proofs of
the corresponding absolute facts in `Mathlib.Computability.Partrec`.

The typed combinators are upstream candidates for mathlib; the `Nat.rfind` wrappers are
local conveniences.
-/

open Encodable Part Primrec

section

variable {α β γ σ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]
variable {O : Set (ℕ →. ℕ)}

namespace Nat.RecursiveIn

/-- `Part.some` is recursive in any oracle set. -/
protected theorem some : Nat.RecursiveIn O Part.some :=
  Nat.Partrec.some.recursiveIn

end Nat.RecursiveIn

/-- A binary computable function is computable in any oracle set. -/
theorem Computable₂.computableIn₂ {f : α → β → σ} {O} (hf : Computable₂ f) :
    ComputableIn₂ O f :=
  hf.computableIn

namespace ComputableIn

/-- Functions extensionally equal to an oracle-computable function are oracle-computable. -/
protected theorem of_eq {f g : α → σ} (hf : ComputableIn O f) (H : ∀ a, f a = g a) :
    ComputableIn O g :=
  (funext H : f = g) ▸ hf

/-- A function is oracle-computable iff its composition with `encode` is. -/
theorem encode_iff {f : α → σ} : ComputableIn O (fun a ↦ encode (f a)) ↔ ComputableIn O f :=
  Iff.rfl

/-- `encode` is computable in any oracle set. -/
protected theorem encode : ComputableIn O (@encode α _) :=
  Computable.encode.computableIn

/-- Pairing of oracle-computable functions is oracle-computable. -/
protected theorem pair {f : α → β} {g : α → γ} (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O fun a ↦ (f a, g a) :=
  (Nat.RecursiveIn.pair hf hg).of_eq fun n ↦ by cases decode (α := α) n <;> simp [Seq.seq]

end ComputableIn

namespace RecursiveIn

/-- Composition of an oracle-partial-recursive function with an oracle-computable function. -/
protected theorem comp {f : β →. σ} {g : α → β} (hf : RecursiveIn O f)
    (hg : ComputableIn O g) : RecursiveIn O fun a ↦ f (g a) :=
  (Nat.RecursiveIn.comp hf hg).of_eq fun n ↦ by
    simp only [map_some, bind_eq_bind]
    rcases e : decode (α := α) n with - | a <;> simp [encodek]

/-- `Part.bind` of oracle-partial-recursive functions is oracle-partial-recursive. -/
protected theorem bind {f : α →. β} {g : α → β →. σ} (hf : RecursiveIn O f)
    (hg : RecursiveIn₂ O g) : RecursiveIn O fun a ↦ (f a).bind (g a) :=
  (Nat.RecursiveIn.comp hg (Nat.RecursiveIn.pair Nat.RecursiveIn.some hf)).of_eq fun n ↦ by
    rcases e : decode (α := α) n <;> simp [Seq.seq, e, encodek]

/-- `Part.map` by an oracle-computable function preserves oracle-partial-recursiveness. -/
theorem map {f : α →. β} {g : α → β → σ} (hf : RecursiveIn O f)
    (hg : ComputableIn₂ O g) : RecursiveIn O fun a ↦ (f a).map (g a) := by
  simpa [bind_some_eq_map] using RecursiveIn.bind (g := fun a b ↦ Part.some (g a b)) hf hg

end RecursiveIn

namespace ComputableIn

/-- Composition of oracle-computable functions is oracle-computable. -/
protected theorem comp {f : β → σ} {g : α → β} (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O fun a ↦ f (g a) :=
  RecursiveIn.comp (f := fun b ↦ Part.some (f b)) hf hg

/-- Curry an oracle-computable function on a product type. -/
theorem to₂ {f : α × β → σ} (hf : ComputableIn O f) :
    ComputableIn₂ O fun a b ↦ f (a, b) :=
  hf.of_eq fun ⟨_, _⟩ ↦ rfl

/-- An oracle-computable `Option`-valued function, viewed as a partial function, is
oracle-partial-recursive. -/
theorem ofOption {f : α → Option β} (hf : ComputableIn O f) :
    RecursiveIn O fun a ↦ (f a : Part β) :=
  (Nat.RecursiveIn.comp Nat.Partrec.ppred.recursiveIn hf).of_eq fun n ↦ by
    rcases decode (α := α) n with - | a <;> simp
    cases f a <;> simp

end ComputableIn

namespace ComputableIn₂

/-- Composition of a binary oracle-computable function with two oracle-computable functions. -/
protected theorem comp {f : β → γ → σ} {g : α → β} {h : α → γ}
    (hf : ComputableIn₂ O f) (hg : ComputableIn O g) (hh : ComputableIn O h) :
    ComputableIn O fun a ↦ f (g a) (h a) :=
  ComputableIn.comp (f := fun p : β × γ ↦ f p.1 p.2) hf (hg.pair hh)

end ComputableIn₂

namespace RecursiveIn₂

/-- Composition of a binary oracle-partial-recursive function with two oracle-computable
functions. -/
protected theorem comp {f : β → γ →. σ} {g : α → β} {h : α → γ}
    (hf : RecursiveIn₂ O f) (hg : ComputableIn O g) (hh : ComputableIn O h) :
    RecursiveIn O fun a ↦ f (g a) (h a) :=
  RecursiveIn.comp (f := fun p : β × γ ↦ f p.1 p.2) hf (hg.pair hh)

end RecursiveIn₂

namespace ComputableIn

/-- Oracle-computable functions are closed under `Bool`-valued conditionals. -/
theorem cond {c : α → Bool} {f g : α → σ} (hc : ComputableIn O c) (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O fun a ↦ bif c a then f a else g a := by
  have harith :
      ComputableIn O fun a ↦
        encode (c a) * encode (f a) + (1 - encode (c a)) * encode (g a) :=
    Primrec.nat_add.to_comp.computableIn₂.comp
      (Primrec.nat_mul.to_comp.computableIn₂.comp (ComputableIn.encode.comp hc)
        (ComputableIn.encode.comp hf))
      (Primrec.nat_mul.to_comp.computableIn₂.comp
        (Primrec.nat_sub.to_comp.computableIn₂.comp (ComputableIn.const 1)
          (ComputableIn.encode.comp hc))
        (ComputableIn.encode.comp hg))
  exact encode_iff.1 <| harith.of_eq fun a ↦ by cases c a <;> simp

end ComputableIn

namespace RecursiveIn

/-- μ-search: unbounded minimization of an oracle-partial-recursive `Bool`-valued predicate
is oracle-partial-recursive. -/
theorem rfind {p : α → ℕ →. Bool} (hp : RecursiveIn₂ O p) :
    RecursiveIn O fun a ↦ Nat.rfind (p a) :=
  (Nat.RecursiveIn.rfind <|
        RecursiveIn.map hp
          (((Primrec.dom_bool fun b ↦ bif b then 0 else 1).comp
            Primrec.snd).to₂.to_comp.computableIn₂)).of_eq
    fun n ↦ by rcases e : decode (α := α) n <;> simp [e, Nat.rfind_zero_none, map_map, map_id']

/-- μ-search over a total `Bool`-valued predicate that is computable in `O` is
partial recursive in `O`. -/
theorem rfind_total {f : α → ℕ → Bool} (hf : ComputableIn₂ O f) :
    RecursiveIn O fun a ↦ Nat.rfind fun n ↦ Part.some (f a n) :=
  RecursiveIn.rfind (p := fun a n ↦ Part.some (f a n)) hf

end RecursiveIn

/-! ### Recursion and folds -/

namespace Nat.RecursiveIn

/-- Primitive recursion with a computed recursion argument: the oracle mirror of
`Nat.Partrec.prec'`. -/
protected theorem prec' {f g h : ℕ →. ℕ} (hf : Nat.RecursiveIn O f)
    (hg : Nat.RecursiveIn O g) (hh : Nat.RecursiveIn O h) :
    Nat.RecursiveIn O fun a ↦ (f a).bind fun n ↦ n.rec (g a)
      fun y IH ↦ do {let i ← IH; h (Nat.pair a (Nat.pair y i))} :=
  ((hg.prec hh).comp (Nat.RecursiveIn.some.pair hf)).of_eq fun a ↦
    Part.ext fun s ↦ by simp [Seq.seq]

end Nat.RecursiveIn

namespace RecursiveIn

/-- Primitive recursion with partial base and step: the oracle mirror of
`Partrec.nat_rec`. -/
protected theorem nat_rec {f : α → ℕ} {g : α →. σ} {h : α → ℕ × σ →. σ}
    (hf : ComputableIn O f) (hg : RecursiveIn O g) (hh : RecursiveIn₂ O h) :
    RecursiveIn O fun a ↦ (f a).rec (g a) fun y IH ↦ IH.bind fun i ↦ h a (y, i) :=
  (Nat.RecursiveIn.prec' hf hg hh).of_eq fun n ↦ by
    rcases e : decode (α := α) n with - | a
    · simp
    · simp only [coe_some, bind_some]
      induction f a <;> simp_all

end RecursiveIn

namespace ComputableIn

/-- Primitive recursion of oracle-computable functions: the oracle mirror of
`Computable.nat_rec`. -/
protected theorem nat_rec {f : α → ℕ} {g : α → σ} {h : α → ℕ × σ → σ}
    (hf : ComputableIn O f) (hg : ComputableIn O g) (hh : ComputableIn₂ O h) :
    ComputableIn O fun a ↦
      Nat.rec (motive := fun _ ↦ σ) (g a) (fun y IH ↦ h a (y, IH)) (f a) :=
  (RecursiveIn.nat_rec hf hg hh.recursiveIn₂).of_eq fun a ↦ by
    simp
    induction f a <;> simp [*]

/-- Case analysis on a computed natural number: the oracle mirror of
`Computable.nat_casesOn`. -/
protected theorem nat_casesOn {f : α → ℕ} {g : α → σ} {h : α → ℕ → σ}
    (hf : ComputableIn O f) (hg : ComputableIn O g) (hh : ComputableIn₂ O h) :
    ComputableIn O fun a ↦ Nat.casesOn (motive := fun _ ↦ σ) (f a) (g a) (h a) :=
  ComputableIn.nat_rec hf hg
    (hh.comp ComputableIn.fst (ComputableIn.fst.comp ComputableIn.snd)).to₂

/-- Iteration of an oracle-computable function: the oracle mirror of
`Primrec.nat_iterate`. -/
protected theorem nat_iterate {f : α → ℕ} {g : α → β} {h : α → β → β}
    (hf : ComputableIn O f) (hg : ComputableIn O g) (hh : ComputableIn₂ O h) :
    ComputableIn O fun a ↦ (h a)^[f a] (g a) :=
  (ComputableIn.nat_rec hf hg
    (hh.comp ComputableIn.fst (ComputableIn.snd.comp ComputableIn.snd)).to₂).of_eq
    fun a ↦ by
      induction f a with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ← ih]

end ComputableIn

omit [Primcodable β] [Primcodable σ] in
private theorem nat_rec_getElem_foldl (l : List β) (op : σ → β → σ) (init : σ) :
    ∀ n, n ≤ l.length →
      Nat.rec (motive := fun _ ↦ Part σ) (Part.some init)
        (fun y IH ↦ IH.bind fun s ↦ (l[y]? : Part β).map fun b ↦ op s b) n =
      Part.some ((l.take n).foldl op init)
  | 0, _ => by simp
  | n + 1, hn => by
    rw [show Nat.rec (motive := fun _ ↦ Part σ) (Part.some init)
        (fun y IH ↦ IH.bind fun s ↦ (l[y]? : Part β).map fun b ↦ op s b) (n + 1) =
      (Nat.rec (motive := fun _ ↦ Part σ) (Part.some init)
        (fun y IH ↦ IH.bind fun s ↦ (l[y]? : Part β).map fun b ↦ op s b) n).bind
        (fun s ↦ (l[n]? : Part β).map fun b ↦ op s b) from rfl,
      nat_rec_getElem_foldl l op init n (by omega),
      List.getElem?_eq_getElem (show n < l.length by omega)]
    simp only [Part.bind_some, Part.coe_some, Part.map_some, List.take_add_one,
      List.getElem?_eq_getElem (show n < l.length by omega), Option.toList_some,
      List.foldl_append, List.foldl_cons, List.foldl_nil]

namespace ComputableIn

/-- Left fold of an oracle-computable function over a list: the workhorse for list
recursion at the oracle level. -/
theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : ComputableIn O f) (hg : ComputableIn O g) (hh : ComputableIn₂ O h) :
    ComputableIn O fun a ↦ (f a).foldl (fun s b ↦ h a (s, b)) (g a) := by
  have hstep : RecursiveIn₂ O fun (a : α) (p : ℕ × σ) ↦
      ((f a)[p.1]? : Part β).map fun b ↦ h a (p.2, b) :=
    RecursiveIn.map
      (ComputableIn.ofOption
        (Computable.list_getElem?.computableIn.comp
          ((hf.comp ComputableIn.fst).pair (ComputableIn.fst.comp ComputableIn.snd))))
      ((hh.comp (ComputableIn.fst.comp ComputableIn.fst)
        ((ComputableIn.snd.comp (ComputableIn.snd.comp ComputableIn.fst)).pair
          ComputableIn.snd)).to₂)
  have hF : RecursiveIn O fun a ↦
      Nat.rec (motive := fun _ ↦ Part σ) (Part.some (g a))
        (fun y IH ↦ IH.bind fun s ↦ ((f a)[y]? : Part β).map fun b ↦ h a (s, b))
        (f a).length :=
    RecursiveIn.nat_rec (Computable.list_length.computableIn.comp hf) hg hstep
  exact hF.of_eq fun a ↦ by
    rw [nat_rec_getElem_foldl (f a) (fun s b ↦ h a (s, b)) (g a) (f a).length le_rfl,
      List.take_length]

/-- Right fold of an oracle-computable function over a list. -/
theorem list_foldr {f : α → List β} {g : α → σ} {h : α → β × σ → σ}
    (hf : ComputableIn O f) (hg : ComputableIn O g) (hh : ComputableIn₂ O h) :
    ComputableIn O fun a ↦ (f a).foldr (fun b s ↦ h a (b, s)) (g a) :=
  (list_foldl (Computable.list_reverse.computableIn.comp hf) hg
    ((hh.comp ComputableIn.fst
      ((ComputableIn.snd.comp ComputableIn.snd).pair
        (ComputableIn.fst.comp ComputableIn.snd))).to₂)).of_eq
    fun a ↦ by rw [List.foldl_reverse]

end ComputableIn

/-! ### Option and sum case analysis -/

namespace RecursiveIn

/-- Repackage an oracle-partial-recursive function on a product as a binary one. -/
protected theorem to₂ {f : α × β →. σ} (hf : RecursiveIn O f) :
    RecursiveIn₂ O fun a b ↦ f (a, b) :=
  hf.of_eq fun ⟨_, _⟩ ↦ rfl

/-- Case analysis on a computed natural with partial successor branch: the oracle mirror
of `Partrec.nat_casesOn_right`. -/
theorem nat_casesOn_right {f : α → ℕ} {g : α → σ} {h : α → ℕ →. σ} (hf : ComputableIn O f)
    (hg : ComputableIn O g) (hh : RecursiveIn₂ O h) :
    RecursiveIn O fun a ↦ (f a).casesOn (Part.some (g a)) (h a) :=
  (RecursiveIn.nat_rec hf hg
    (hh.comp ComputableIn.fst
      ((Primrec.pred.to_comp.computableIn).comp (hf.comp ComputableIn.fst))).to₂).of_eq
    fun a ↦ by
      simp only [Nat.pred_eq_sub_one]
      rcases f a with - | n
      · simp
      · refine Part.ext fun b ↦ ⟨fun H ↦ ?_, fun H ↦ ?_⟩
        · rcases Part.mem_bind_iff.1 H with ⟨c, _, h₂⟩
          exact h₂
        · have : ∀ m, (Nat.rec (motive := fun _ ↦ Part σ)
              (Part.some (g a)) (fun y IH ↦ IH.bind fun _ ↦ h a n) m).Dom := by
            intro m
            induction m <;> simp [*, H.fst]
          exact ⟨⟨this n, H.fst⟩, H.snd⟩

end RecursiveIn

namespace ComputableIn

/-- `Option.some` is computable in any oracle set. -/
protected theorem option_some : ComputableIn O (@Option.some α) :=
  Computable.option_some.computableIn

/-- A total function is oracle-computable iff its `Option.some`-lift is. -/
theorem option_some_iff {f : α → σ} :
    (ComputableIn O fun a ↦ Option.some (f a)) ↔ ComputableIn O f :=
  ⟨fun h ↦ encode_iff.1 ((Primrec.pred.to_comp.computableIn).comp (encode_iff.2 h)),
    fun hf ↦ ComputableIn.option_some.comp hf⟩

/-- Precomposing an oracle-computable `Option`-valued binary function with `decode`:
one direction of the oracle mirror of `Computable.bind_decode_iff`. -/
theorem bind_decode {f : α → β → Option σ} (hf : ComputableIn₂ O f) :
    ComputableIn₂ O fun a n ↦ (decode (α := β) n).bind (f a) := by
  have h : RecursiveIn O fun a : α × ℕ ↦
      (encode (decode (α := β) a.2)).casesOn
        (Part.some (Option.none : Option σ))
        fun n ↦ Part.map (f a.1) (Part.ofOption (decode (α := β) n)) :=
    RecursiveIn.nat_casesOn_right
      ((Primrec.encdec.to_comp.computableIn).comp ComputableIn.snd)
      (ComputableIn.const Option.none)
      ((RecursiveIn.map
        (ComputableIn.ofOption ((Computable.decode.computableIn).comp ComputableIn.snd))
        ((hf.comp (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst))
          ComputableIn.snd).to₂)).to₂)
  refine h.of_eq fun a ↦ ?_
  rcases hd : decode (α := β) a.2 with - | b <;> simp [hd, encodek]

/-- Postcomposing `decode` with an oracle-computable binary function: one direction of
the oracle mirror of `Computable.map_decode_iff`. -/
theorem map_decode {f : α → β → σ} (hf : ComputableIn₂ O f) :
    ComputableIn₂ O fun a n ↦ (decode (α := β) n).map (f a) :=
  (bind_decode (f := fun a b ↦ Option.some (f a b))
    (ComputableIn.option_some.comp hf)).of_eq fun p ↦ by
    dsimp only
    rcases hd : decode (α := β) p.2 with - | b <;> simp

/-- Case analysis on a computed option: the oracle mirror of
`Computable.option_casesOn`. -/
theorem option_casesOn {o : α → Option β} {f : α → σ} {g : α → β → σ}
    (ho : ComputableIn O o) (hf : ComputableIn O f) (hg : ComputableIn₂ O g) :
    ComputableIn O fun a ↦ Option.casesOn (motive := fun _ ↦ σ) (o a) (f a) (g a) :=
  option_some_iff.1 <|
    (ComputableIn.nat_casesOn (encode_iff.2 ho) (option_some_iff.2 hf)
      (map_decode hg)).of_eq fun a ↦ by
        cases o a <;> simp [encodek]

/-- `Option.bind` of oracle-computable functions: the oracle mirror of
`Computable.option_bind`. -/
theorem option_bind {f : α → Option β} {g : α → β → Option σ}
    (hf : ComputableIn O f) (hg : ComputableIn₂ O g) :
    ComputableIn O fun a ↦ (f a).bind (g a) :=
  (option_casesOn hf (ComputableIn.const Option.none) hg).of_eq fun a ↦ by
    cases f a <;> rfl

/-- `Option.map` by an oracle-computable function: the oracle mirror of
`Computable.option_map`. -/
theorem option_map {f : α → Option β} {g : α → β → σ} (hf : ComputableIn O f)
    (hg : ComputableIn₂ O g) : ComputableIn O fun a ↦ (f a).map (g a) :=
  (option_bind hf (g := fun a b ↦ Option.some (g a b))
    (ComputableIn.option_some.comp hg)).of_eq fun a ↦ by
    cases f a <;> rfl

/-- `Option.getD` of oracle-computable functions. -/
theorem option_getD {f : α → Option β} {g : α → β} (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O fun a ↦ (f a).getD (g a) :=
  (option_casesOn hf hg
    (show ComputableIn₂ O fun _ b ↦ b from ComputableIn.snd)).of_eq
    fun a ↦ by cases f a <;> rfl

/-- Case analysis on a computed sum: the oracle mirror of `Computable.sumCasesOn`. -/
theorem sumCasesOn {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ → σ}
    (hf : ComputableIn O f) (hg : ComputableIn₂ O g) (hh : ComputableIn₂ O h) :
    ComputableIn O fun a ↦ Sum.casesOn (motive := fun _ ↦ σ) (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (ComputableIn.cond ((Primrec.nat_bodd.to_comp.computableIn).comp (encode_iff.2 hf))
      (option_map ((Computable.decode.computableIn).comp
        ((Primrec.nat_div2.to_comp.computableIn).comp (encode_iff.2 hf))) hh)
      (option_map ((Computable.decode.computableIn).comp
        ((Primrec.nat_div2.to_comp.computableIn).comp (encode_iff.2 hf))) hg)).of_eq
      fun a ↦ by rcases f a with b | c <;> simp [Nat.div2_val]

end ComputableIn

end

namespace Nat

/-- `Nat.rfind` over a total `Bool`-valued predicate halts exactly when a witness exists.
Note that `Nat.rfind` searches for the value `true`, not for `0`. This is a thin wrapper
around `Nat.rfind_dom` for the total case. -/
theorem rfind_some_dom_iff {α : Type*} {f : α → ℕ → Bool} {a : α} :
    (Nat.rfind fun n ↦ Part.some (f a n)).Dom ↔ ∃ n, f a n = true := by
  simp [Nat.rfind_dom]

/-- The result of `Nat.rfind` over a total `Bool`-valued predicate satisfies the predicate.
This is a thin wrapper around `Nat.rfind_spec` for the total case. -/
theorem rfind_some_spec {α : Type*} {f : α → ℕ → Bool} {a : α} {n : ℕ}
    (h : n ∈ Nat.rfind fun k ↦ Part.some (f a k)) : f a n = true := by
  simpa using Nat.rfind_spec h

end Nat
