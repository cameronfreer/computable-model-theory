# computable-model-theory

A Lean 4 / [mathlib](https://github.com/leanprover-community/mathlib4) library that aims
to formalize computable model theory: effective presentations of first-order languages
and structures, computable ages, potential embeddings and embedding information, and
effective Fraïssé constructions. The library is developed as a reusable spine over
mathlib's `FirstOrder` model theory, importing classical infinitary-logic foundations
from [infinitary-logic](https://github.com/cameronfreer/infinitary-logic) as a pinned
dependency.

## Current status

The relative-computability substrate is in place: typed `RecursiveIn`/`ComputableIn`
combinators (composition, pairing, bind, map, conditionals, μ-search), the
oracle-relative predicate layer `ComputablePredIn`/`REPredIn` with Boolean closure,
finite quantifiers, and r.e. closure lemmas, and lightweight reductions with oracle
transport. On the syntax side, `EffectiveLanguage` provides computability data for
first-order languages, terms of effective languages are `Primcodable` — including
uniformly over all `Fin` variable bounds, via a stack machine on natural-number symbol
codes — with computable term operations, and bounded formulas (packaged over all
numbers of free variables), formulas, and sentences are `Primcodable`, via a second
stack machine over the formula alphabet whose primitive recursiveness is proven by
course-of-values recursion on suffix length. ω-presented computable structures are
defined — uniformly over application
data, so a single algorithm interprets every symbol — with the empty language, a graph
language, and a unary-function language on `ℕ` as computable examples. Term evaluation
and atomic and quantifier-free satisfaction in computable structures are computable in
the oracle — quantifier-free satisfaction by a satisfaction stack machine run in
parallel with mathlib's formula decoder — and the partial and total characteristic
oracles are proven interchangeable. The signed atomic and quantifier-free diagram
predicates at fixed width are computable in the oracle. Finite tuples are list-backed
with a fixed-width view, and the central semantic gate identifies membership in a
tuple's closure with term realization over the tuple. Generated computable
presentations bundle a computable structure with a generating tuple behind an
instance-free interface; atomic equivalence of tuples is characterized by
generator-preserving equivalences of tuple closures; closure membership is r.e. by
effective term enumeration; and the failure of atomic equivalence between two fixed
presentations is r.e. Uniform computable ages enumerate structures with single
index-uniform programs, represent isomorphism-closed classes of finitely generated
structures, and carry potential embeddings — pure code data whose actualness is atomic
equivalence of generators with the range tuple, realized as bundled embeddings
extending the tuple assignment. Terms and atomic data over natural-number variables
are evaluated by single programs uniform in the age index and a list environment;
atomic equivalence is exactly agreement on width-valid atomic data; the failure of
actualness of arbitrary potential embedding data is uniformly r.e.; and embedding
information is defined semantically with an r.e. complement.

On top of that base: canonical least-term transport of values along potential embedding
data; total composition of potential data with its identity, associativity, and
realized-embedding laws; `Primcodable` spans and amalgamation diagrams with coded
commutativity matching realized commutativity; the indexed HP/JEP/AP properties with
joint embedding data; effective HP/JEP/AP witness interfaces (total selectors with
computability and conditional soundness); an abstract EI-decision interface; a minimal
oracle jump calculus (`ComputesJumpOf`, with the r.e.-to-decidable bridges and the
displayed `0′`), giving `EI(K) ≤ O′` in interface form; and a thin representation
boundary to `infinitary-logic`'s Scott/back-and-forth and Henkin layers. Witness
extraction and the effective Fraïssé limit are to come.

## Staging

| Stage | Content |
|-------|---------|
| 1 | Syntax computability (effective languages, `Primcodable` syntax, computable operations) |
| 2 | Computable structures and diagrams (ω-presentations, term/qf evaluation, atomic diagrams) |
| 3 | Computable ages and potential embeddings (tuple closures, atomic equivalence, embedding information) |
| 4 | AP/Fraïssé upper bound (effective HP/JEP/AP witnesses, computable Fraïssé construction) |

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (managed by
[elan](https://github.com/leanprover/elan)).

```
lake exe cache get
lake build
```

The audit modules (axiom-policy enforcement and API acceptance tests) are outside the
root import spine and are checked explicitly, as in CI:

```
lake env lean ComputableModelTheory/Computability/OraclePredAudit.lean
```

## License

Released under the Apache 2.0 license, following mathlib convention; see
[LICENSE](LICENSE). Source files carry the corresponding mathlib-style copyright headers.
