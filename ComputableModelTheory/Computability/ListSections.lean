/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.List.Sections
import Mathlib.Computability.Primrec.List

/-!
# Tuples over a list

`List.sections` enumerates the choice functions of a list of lists. The case needed for
bounded search over a finite carrier is the **constant** one: `(List.replicate n l).sections`
is exactly the list of length-`n` tuples with every entry drawn from `l`.

`mem_sections_replicate` is that semantic characterization, and it is what correctness
arguments and audits consume; the computability of the enumeration is a separate matter and is
built on top of it. Both are upstream candidates for mathlib, which has `List.mem_sections` but
not the constant specialization.

The file also collects the pure `List.Forall₂` facts this development needs and mathlib does not
carry — `forall₂_mem_replicate` above, and `Forall₂.exists_of_mem_right`, which reads a traversal's
output backwards. Both are upstream candidates on the same footing.
-/

namespace List

variable {α : Type*}

/-- **A right-hand entry of a `Forall₂` comes from some left-hand entry.** Mathlib has the
left-to-right direction through `Forall₂.get` but no membership form in this direction, and reading
a traversal's output backwards is exactly what halting arguments over `listMapPart` need.

Upstream candidate. -/
theorem Forall₂.exists_of_mem_right {β : Type*} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {y : β} (hy : y ∈ l') : ∃ x ∈ l, R x y := by
  obtain ⟨n, hn⟩ := List.mem_iff_get.1 hy
  have hlt : (n : ℕ) < l.length := by rw [h.length_eq]; exact n.isLt
  exact ⟨l.get ⟨n, hlt⟩, List.get_mem _ _, hn ▸ h.get hlt n.isLt⟩

/-- `Forall₂ (· ∈ ·)` against a constant list is a length condition plus memberwise
membership. -/
theorem forall₂_mem_replicate {l : List α} :
    ∀ {n : ℕ} {f : List α},
      List.Forall₂ (· ∈ ·) f (List.replicate n l) ↔ (f.length = n ∧ ∀ x ∈ f, x ∈ l) := by
  intro n
  induction n with
  | zero =>
    intro f
    rw [List.replicate_zero, List.forall₂_nil_right_iff]
    constructor
    · rintro rfl
      exact ⟨rfl, by simp⟩
    · rintro ⟨hlen, -⟩
      exact List.length_eq_zero_iff.1 hlen
  | succ m ih =>
    intro f
    rw [List.replicate_succ, List.forall₂_cons_right_iff]
    constructor
    · rintro ⟨a, f', ha, hf', rfl⟩
      obtain ⟨hlen, hmem⟩ := ih.1 hf'
      refine ⟨by simp [hlen], fun x hx ↦ ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact hmem x hx
    · rintro ⟨hlen, hmem⟩
      rcases f with - | ⟨a, f'⟩
      · exact absurd hlen (by simp)
      · refine ⟨a, f', hmem a List.mem_cons_self, ih.2 ⟨by simpa using hlen, ?_⟩, rfl⟩
        exact fun x hx ↦ hmem x (List.mem_cons_of_mem a hx)

/-- **Tuples over a list.** `(List.replicate n l).sections` is exactly the length-`n` lists all
of whose entries lie in `l` — the enumeration a bounded search over a finite carrier needs. -/
theorem mem_sections_replicate {l : List α} {n : ℕ} {f : List α} :
    f ∈ (List.replicate n l).sections ↔ (f.length = n ∧ ∀ x ∈ f, x ∈ l) :=
  List.mem_sections.trans forall₂_mem_replicate

/-- Every tuple over `l` of the right length is enumerated. -/
theorem mem_sections_replicate_of {l f : List α} (hmem : ∀ x ∈ f, x ∈ l) :
    f ∈ (List.replicate f.length l).sections :=
  mem_sections_replicate.2 ⟨rfl, hmem⟩

end List

/-! ### Computability

`List.sections` is a `foldr` whose step is a `flatMap` of a `map`, so it goes through the
existing list combinators; no new recursion scheme is needed. -/

namespace Primrec

variable {β : Type*} [Primcodable β]

/-- `List.replicate`, primitive recursive in the count and the element. Mathlib has no
combinator for it; it is a bare `Nat.rec`. -/
theorem list_replicate : Primrec₂ fun (n : ℕ) (b : β) ↦ List.replicate n b := by
  have h : Primrec fun p : ℕ × β ↦
      Nat.rec (motive := fun _ ↦ List β) [] (fun _ ih ↦ p.2 :: ih) p.1 :=
    Primrec.nat_rec' Primrec.fst (Primrec.const [])
      ((Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd)).to₂)
  refine h.of_eq fun p ↦ ?_
  obtain ⟨n, b⟩ := p
  show Nat.rec (motive := fun _ ↦ List β) [] (fun _ ih ↦ b :: ih) n = List.replicate n b
  induction n with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, ← ih]

theorem list_sections : Primrec (List.sections : List (List β) → List (List β)) := by
  have hstep : Primrec₂ fun (_ : List (List β)) (p : List β × List (List β)) ↦
      p.2.flatMap fun s ↦ p.1.map fun a ↦ a :: s :=
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
      (Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).to₂).to₂
  have h : Primrec fun L : List (List β) ↦
      L.foldr (fun l acc ↦ acc.flatMap fun s ↦ l.map fun a ↦ a :: s) [[]] :=
    Primrec.list_foldr Primrec.id (Primrec.const [[]]) hstep
  refine h.of_eq fun L ↦ ?_
  induction L with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, ih]; rfl

/-- The tuple enumeration used by bounded search: all length-`n` tuples over a list,
primitive recursive in the length and the list. -/
theorem list_sections_replicate :
    Primrec₂ fun (n : ℕ) (l : List β) ↦ (List.replicate n l).sections :=
  (list_sections.comp (list_replicate.comp Primrec.fst Primrec.snd)).to₂

end Primrec
