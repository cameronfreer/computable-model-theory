# computable-model-theory

A Lean 4 / [mathlib](https://github.com/leanprover-community/mathlib4) library that aims
to formalize computable model theory: effective presentations of first-order languages
and structures, computable ages, potential embeddings and embedding information, and
effective Fraïssé constructions. The library is developed as a reusable spine, with
paper-specific statements kept in wrapper modules under `ComputableModelTheory/Paper/`.

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
presentations is r.e. The remaining model-theoretic layers are import skeletons
awaiting content.

## Staging

| Stage | Content |
|-------|---------|
| 1 | Syntax computability (effective languages, `Primcodable` syntax, computable operations) |
| 2 | Computable structures and diagrams (ω-presentations, term/qf evaluation, atomic diagrams) |
| 3 | Computable ages and potential embeddings (tuple closures, atomic equivalence, embedding information) |
| 4 | AP/Fraïssé upper bound (effective HP/JEP/AP witnesses, computable Fraïssé construction) |
| 5 | CAP/cofinal material (distinguished extensions, cofinal ultrahomogeneity, cofinal limits) |
| 6 | Lower bounds (diagonalization against oracle strength) |

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
