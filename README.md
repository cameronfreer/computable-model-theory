# computable-model-theory

A Lean 4 / [mathlib](https://github.com/leanprover-community/mathlib4) library for
computable model theory: effective presentations of first-order languages and
structures, computable ages, potential embeddings and embedding information, and
effective Fraïssé constructions. The library is developed as a reusable spine, with
paper-specific statements kept in wrapper modules under `ComputableModelTheory/Paper/`.

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
