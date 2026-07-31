/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableModelTheory.Computability.RecursiveIn
import ComputableModelTheory.ModelTheory.Syntax.EffectiveLanguage

/-!
# Assembling application data, relative to an oracle

`ofSymbolArgs?` assembles function or relation application data from a packaged symbol and an
argument list, succeeding exactly when the arity matches. Its primitive recursiveness is proved
in `EffectiveLanguage`; what callers actually need is the *relative, composed* form — assemble
from an oracle-computable symbol/arguments pair.

Every consumer had been writing

```
(FunctionApplicationData.primrec_ofSymbolArgs?.to_comp.computableIn).comp hp
```

by hand: `RankPresentation`, `ChainPresentation`, `ComputableIso`, the satisfaction layer, and
the finite checker. Besides shortening those, taking the pair as a *parameter* moves the `.comp`
out of each caller's expected-type context, which is where composition against a projection
repacking tends to stall.

This lives in its own file rather than in `EffectiveLanguage` so that the *foundational* module
stays independent: importers that need only the primitive-recursive syntax layer do not acquire
the relative-computability substrate. The `Syntax` umbrella does import this module, so anything
importing the umbrella gets both.
-/

open Encodable

namespace FirstOrder.Language

variable {O : Set (ℕ →. ℕ)} {L : Language} [L.EffectiveLanguage]
variable {α : Type*} [Primcodable α] {M : Type*} [Primcodable M]

namespace FunctionApplicationData

/-- Assembling function application data from an oracle-computable symbol/arguments pair. -/
theorem ofSymbolArgs?_computableIn {p : α → L.FunctionSymbol × List M}
    (hp : ComputableIn O p) :
    ComputableIn O fun a ↦ FunctionApplicationData.ofSymbolArgs? (p a) :=
  ComputableIn.comp (primrec_ofSymbolArgs?.to_comp.computableIn (O := O)) hp

end FunctionApplicationData

namespace RelationApplicationData

/-- Assembling relation application data from an oracle-computable symbol/arguments pair. -/
theorem ofSymbolArgs?_computableIn {p : α → L.RelationSymbol × List M}
    (hp : ComputableIn O p) :
    ComputableIn O fun a ↦ RelationApplicationData.ofSymbolArgs? (p a) :=
  ComputableIn.comp (primrec_ofSymbolArgs?.to_comp.computableIn (O := O)) hp

end RelationApplicationData

end FirstOrder.Language
