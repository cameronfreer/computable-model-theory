# computable-model-theory

A Lean 4 / [mathlib](https://github.com/leanprover-community/mathlib4) library that aims
to formalize computable model theory: effective presentations of first-order languages
and structures, computable ages, potential embeddings and embedding information, and
effective Fraïssé constructions. The library is developed as a reusable spine, with
paper-specific statements kept in wrapper modules under `ComputableModelTheory/Paper/`.

## Current status

The relative-computability substrate is in place: typed `RecursiveIn`/`ComputableIn`
combinators (composition, pairing, bind, map, conditionals, μ-search) and the
oracle-relative predicate layer `ComputablePredIn`/`REPredIn` with Boolean closure,
finite quantifiers, and r.e. closure lemmas. The model-theoretic layers below are import
skeletons awaiting content.

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
