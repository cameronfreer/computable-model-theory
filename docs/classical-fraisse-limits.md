# Classical Fraïssé interfaces

Three modules under `ComputableModelTheory/ModelTheory/` state the classical, semantic side of
Fraïssé theory that the effective constructions of this library consume. None of them imports an
effective language, a presentation, a coded age, an oracle, or `InfinitaryLogic`; each imports
only Mathlib (and the second below imports the first). Their natural long-term home is Mathlib.

```text
Mathlib.ModelTheory.Fraisse
    ├── RepresentativeAge
    └── ExtensionRichFamily
            └── ExtensionRichDirectLimit
```

## Extension-rich families (`ExtensionRichFamily`)

For a family `U : I → L.Substructure M` of substructures of one structure:

- `FGCofinal U`: every finitely generated substructure lies in some `U i`.
- `ExtensionRich U`: for finitely generated `S ≤ T ≤ U i` and `f : S ↪ U i` there are `j` and
  `g : T ↪ U j` with `g ∘ inclusion = f` in `M`. There is no order on `I`, and the receiving member
  need not contain the original one.

Cofinality and extension richness give the self-extension pair with no countability
(`isExtensionPair_of_extensionRich`), ultrahomogeneity under countable generation, and the converse
without countable generation. The age of `M` is the union of the members' ages
(`age_eq_iUnion_of_fgCofinal`), identified with a hereditary class that contains the members and
covers its own elements (`age_eq_of_fgCofinal`) — coverage is supplied, no joint embedding is
assumed. `isFraisseLimit_of_extensionRich` packages both with Mathlib's `IsFraisseLimit`.

## Representative classes (`RepresentativeAge`)

For an independently universe-polymorphic family `F : I → Bundled L.Structure`,
`representativeClass F` is its isomorphism closure. Finite generation, hereditary closure (it
suffices to recognize finitely generated substructures of representatives), joint embedding and
amalgamation of the representatives transfer to the whole class; the amalgamation premise keeps
the literal commuting square. `isFraisse_representativeClass` assembles Mathlib's `IsFraisse`
from an inhabited countable index. Countability is of isomorphism classes
(`representativeClass_countable_quotient`), not of the bundled class. When the age of `M` lies in the class, every
finite tuple of `M` factors literally through an embedding of a representative
(`exists_factor_tuple_of_age_subset`; repeated coordinates allowed, and
`exists_factor_embedding_of_age_subset` for injective tuples). The choice is classical, not an
effective pullback.

## Direct limits (`ExtensionRichDirectLimit`)

For a directed system of embeddings over a nonempty directed preorder — Mathlib's
`FirstOrder.Language.DirectLimit`, with transition maps that need not be inclusions:

- the canonical stage images are monotone and finitely cofinal (`fgCofinal_directLimit`);
- an embedding of a finitely generated structure factors literally through one stage
  (`exists_factor_directLimit`);
- countably many countable stages give a countable limit, with no assumption on the signature
  (`countable_directLimit`);
- `AmalgamationRich G f` — every embedding of a finitely generated substructure of stage `i` into
  stage `j` extends to the whole of stage `i` at a later target stage `k`, commuting with the
  transition from `j` — gives the self-extension pair (`isExtensionPair_directLimit`), and
  ultrahomogeneity for a countable index and countably generated stages.

For sequences, `SequenceExtension f K` is the whole-stage extension property against a class `K`.
Hereditary closure and amalgamation turn it into `AmalgamationRich`
(`amalgamationRich_of_sequenceExtension`); stage membership and coverage identify the age
separately (`age_directLimit_eq`, which needs no amalgamation); `isFraisseLimit_directLimit`
assembles both. Its countable-limit premise can be supplied by `countable_directLimit`.

## The remaining existence obligation

These are criteria for a *supplied* family or system; none constructs one. A classical existence
theorem must still build, from a countable hereditary class with joint embedding and amalgamation,
a sequence satisfying `SequenceExtension`, stage membership and coverage. The construction must
serve outgoing embeddings from *historical* stages, transported along the literal connecting maps
— serving only the current stage loses requests. One schedule: enumerate the outgoing embeddings
of each representative; at time `Nat.pair n k`, amalgamate outgoing embedding `k` of stage `n`
against the transition from `n` to the current stage, and use joint embedding to take in the next
representative. The Lean obligation is the dependent finite-prefix recursion, its coherence, and
fairness.

**That theorem needs a countability hypothesis on carriers.** The enumeration of outgoing
embeddings uses `Structure.FG.countable_embedding`, which needs *countable target carriers*.
Countably many isomorphism classes does not supply that, and neither does finite generation alone
for an arbitrary signature. So the existence theorem is to be stated under countable
representative carriers, or with that derived from countably many function symbols and finite
generation. This is separate from `isFraisse_representativeClass`, which needs no signature or
carrier hypothesis, and from the criteria above.

## How this library uses them

`FraisseCriterion` routes its semantic Lemma 3.8 (`FraisseChainData.isExtensionPair`,
`isUltrahomogeneous`, `age_eq`, `isFraisseLimit`) through `ExtensionRichFamily`, applied to the
stage images of a Lemma 2.9 limit. `PartialAgeIn.classSet` is the representative class of the
bundled members (`classSet_eq_representativeClass`), so HP, JEP and member amalgamation make it a
Fraïssé class (`isFraisse_classSet`), and CAP supplies that amalgamation
(`PartialCAPIn.memberAmalgamation`). The effective chain of this library is not a Mathlib
`DirectLimit`, so `ExtensionRichDirectLimit` has no in-library consumer yet.

## Checks

`scripts/check-classical-fraisse.sh`, run in CI after the build, builds the three modules and
elaborates each module and its audit with warnings as errors and `autoImplicit=false`. It uses
`lake env lean` on purpose: the ordinary audit sweep elaborates with the package's Lean options,
including project-wide compatibility settings the effective layer may need, while this gate checks
the classical layer without them. Each audit runs `#assert_module_standard_axioms`, which checks
the standard axioms on every declaration of the module by defining module, whatever its namespace.
The audits also check the import boundary and pin regressions: independent universes, empty index
and empty carriers, empty stages, and transitions given by arbitrary automorphisms.
