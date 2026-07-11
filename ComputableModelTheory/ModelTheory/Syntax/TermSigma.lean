/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.NatStack

/-!
# The uniform sigma of terms is primitively codable

`Primcodable (Σ k, L.Term (α ⊕ Fin k))` for an effective language over a `Primcodable`
variable type, with mathlib's sigma `Encodable` instance: the primitive recursion witness
is `sigmaTermNatP`, computed entirely on codes by canonicalizing the symbol-code list
(`canonAll`) and running the code-level stack machine (`natDecodeStack`), then reassembled
against the fiber decoders through the canonicalization and soundness bridges. This
instance is the gateway to `Primcodable` instances for formulas.
-/

open Encodable

namespace FirstOrder.Language.Term

variable (L : Language) [L.EffectiveLanguage] (α : Type*) [Primcodable α]

variable (L : Language) [L.EffectiveLanguage] (α : Type*) [Primcodable α]

/-- The decode-encode composite of the sigma of terms over all `Fin` variable bounds,
computed entirely on codes. -/
def sigmaTermNatP (n : ℕ) : ℕ :=
  Option.casesOn (motive := fun _ ↦ ℕ)
    ((decode (α := List ℕ) n.unpair.2).bind (canonAll L α n.unpair.1)) 0
    fun ccs ↦ Option.casesOn (motive := fun _ ↦ ℕ) ((natDecodeStack L ccs).head?) 0
      fun tc ↦ (Nat.pair n.unpair.1 (encode tc)) + 1

theorem primrec_sigmaTermNatP : Primrec (sigmaTermNatP L α) := by
  have hk : Primrec fun n : ℕ ↦ n.unpair.1 :=
    Primrec.fst.comp Primrec.unpair
  have hd : Primrec fun n : ℕ ↦
      (decode (α := List ℕ) n.unpair.2).bind (canonAll L α n.unpair.1) :=
    Primrec.option_bind
      (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
      (((primrec₂_canonAll L α).comp Primrec.snd (hk.comp Primrec.fst)).to₂)
  have hinner : Primrec₂ fun (n : ℕ) (ccs : List ℕ) ↦
      Option.casesOn (motive := fun _ ↦ ℕ) ((natDecodeStack L ccs).head?) 0
        fun tc ↦ (Nat.pair n.unpair.1 (encode tc)) + 1 := by
    have hh : Primrec fun q : ℕ × List ℕ ↦ (natDecodeStack L q.2).head? :=
      Primrec.list_head?.comp ((primrec_natDecodeStack L).comp Primrec.snd)
    exact (Primrec.option_casesOn hh (Primrec.const 0)
      ((Primrec.succ.comp (Primrec₂.natPair.comp
        ((Primrec.fst.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.fst))
        (Primrec.encode.comp Primrec.snd))).to₂)).to₂
  exact (Primrec.option_casesOn hd (Primrec.const 0) hinner).of_eq fun n ↦ rfl

/-- The uniform sigma of terms over all `Fin` variable bounds is primitively codable,
with mathlib's sigma `Encodable` instance. This is the gateway to formula codability. -/
instance instPrimcodableSigmaTerm : Primcodable (Σ k, L.Term (α ⊕ Fin k)) where
  toEncodable := inferInstance
  prim := by
    refine Primrec.nat_iff.1 ((primrec_sigmaTermNatP L α).of_eq fun n ↦ ?_)
    rw [sigmaTermNatP, decode_sigma_val]
    have hbindmap : (decode (α := List ℕ) n.unpair.2).bind (canonAll L α n.unpair.1) =
        ((decode (α := List ℕ) n.unpair.2).bind
          (decodeAll ((α ⊕ Fin n.unpair.1) ⊕ (Σ i, L.Functions i)))).map
            (List.map encode) := by
      rcases decode (α := List ℕ) n.unpair.2 with - | cs
      · rfl
      · exact canonAll_eq L α n.unpair.1 cs
    rw [hbindmap, ← decode_list_eq_decodeAll,
      show decode (α := ℕ) n.unpair.1 = some n.unpair.1 from rfl]
    change _ = encode (Option.map
      (Sigma.mk (β := fun k ↦ L.Term (α ⊕ Fin k)) n.unpair.1)
      (decode (α := L.Term (α ⊕ Fin n.unpair.1)) n.unpair.2))
    rcases hfib : decode (α := List ((α ⊕ Fin n.unpair.1) ⊕ (Σ i, L.Functions i)))
        n.unpair.2 with - | l
    · rw [show decode (α := L.Term (α ⊕ Fin n.unpair.1)) n.unpair.2 =
          (decode (α := List ((α ⊕ Fin n.unpair.1) ⊕ (Σ i, L.Functions i)))
            n.unpair.2).bind
            (fun l ↦ ((listDecode l).head?.bind fun a ↦ some (some a)).join) from rfl,
        hfib]
      rfl
    · rw [show decode (α := L.Term (α ⊕ Fin n.unpair.1)) n.unpair.2 =
          (decode (α := List ((α ⊕ Fin n.unpair.1) ⊕ (Σ i, L.Functions i)))
            n.unpair.2).bind
            (fun l ↦ ((listDecode l).head?.bind fun a ↦ some (some a)).join) from rfl,
        hfib]
      simp only [Option.map_some]
      change _ = encode (Option.map
        (Sigma.mk (β := fun k ↦ L.Term (α ⊕ Fin k)) n.unpair.1)
        (((listDecode l).head?.bind fun a ↦ some (some a)).join))
      rw [natDecodeStack_map_encode, decodeStack_eq_map_listEncode, List.head?_map,
        List.head?_map]
      rcases (listDecode l).head? with - | t
      · rfl
      · change Nat.pair n.unpair.1 (encode ((listEncode t).map encode)) + 1 = _
        rw [encode_list_map_encode]
        rfl

end FirstOrder.Language.Term
