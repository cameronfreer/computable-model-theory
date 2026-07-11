/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.ModelTheory.Syntax.TermSigma
import ComputableModelTheory.Util.AssertAxioms

/-!
# Audit module for the uniform term sigma

Named acceptance tests for `Primcodable (Σ k, L.Term (α ⊕ Fin k))`, checked by
`#assert_standard_axioms`. Outside the root import spine; CI checks it explicitly with

```
lake env lean ComputableModelTheory/ModelTheory/Syntax/TermSigmaAudit.lean
```
-/

open Encodable FirstOrder Language Language.Term

section

variable {L : Language} {α : Type*} [Primcodable α] [L.EffectiveLanguage]

/-- The uniform sigma instance typeclass-infers: the PR 4 bottleneck gate. -/
@[reducible] def test_sigmaTerm_primcodable : Primcodable (Σ k, L.Term (α ⊕ Fin k)) :=
  inferInstance

/-- Sigma-packaged terms round-trip through their codes. -/
theorem test_sigmaTerm_encodek (s : Σ k, L.Term (α ⊕ Fin k)) :
    decode (encode s) = some s :=
  Encodable.encodek s

/-- No encoding diamond: the instance encodes by pairing the bound with the term code. -/
theorem test_sigmaTerm_encode_eq (k : ℕ) (t : L.Term (α ⊕ Fin k)) :
    encode (⟨k, t⟩ : Σ k', L.Term (α ⊕ Fin k')) = Nat.pair k (encode t) :=
  rfl

/-- The code-level decode-encode composite of the sigma is primitive recursive. -/
theorem test_primrec_sigmaTermNatP : Primrec (sigmaTermNatP L α) :=
  primrec_sigmaTermNatP L α

/-- Canonicalization agrees with fiber decoding followed by re-encoding. -/
theorem test_canonAll_eq (k : ℕ) (cs : List ℕ) :
    canonAll L α k cs =
      (decodeAll ((α ⊕ Fin k) ⊕ (Σ i, L.Functions i)) cs).map (List.map encode) :=
  canonAll_eq L α k cs

/-- The code-level machine is sound for every fiber. -/
theorem test_natDecodeStack_sound (l : List ((α ⊕ Fin 3) ⊕ (Σ i, L.Functions i))) :
    natDecodeStack L (l.map encode) = (decodeStack l).map (List.map encode) :=
  natDecodeStack_map_encode L l

end

#assert_standard_axioms test_sigmaTerm_primcodable
#assert_standard_axioms test_sigmaTerm_encodek
#assert_standard_axioms test_sigmaTerm_encode_eq
#assert_standard_axioms test_primrec_sigmaTermNatP
#assert_standard_axioms test_canonAll_eq
#assert_standard_axioms test_natDecodeStack_sound
