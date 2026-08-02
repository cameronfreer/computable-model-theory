# computable-model-theory

[![CI](https://github.com/cameronfreer/computable-model-theory/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/cameronfreer/computable-model-theory/actions/workflows/lean_action_ci.yml)

A Lean 4 library for effective first-order model theory over
[mathlib](https://github.com/leanprover-community/mathlib4). It develops oracle-relative
computability, effective syntax and presentations, and reusable infrastructure for computable
Fraïssé theory, including formalizations guided by Csima–Harizanov–Miller–Montalbán (2011).

## Library at a glance

* **Relative computability.** Oracle-relative computability and partial recursion, relative
  predicates and r.e. predicates, lightweight reductions, c.e. chains, and a
  representation-independent jump interface.
* **Effective syntax.** Effective languages, `Primcodable` terms and formulas, computable
  syntactic operations, term evaluation, atomic and quantifier-free satisfaction, and the signed
  diagram predicates.
* **Presentations.** Computable, c.e.-domain, decidable-domain and partial presentations;
  computable isomorphisms, canonicalization, presentation chains and their limits.
* **Ages and embeddings.** Computable and partial ages, potential embeddings and amalgamation
  diagrams, effective HP/JEP/AP/CAP witness interfaces, and decision procedures for embedding
  data over finite carriers.

## Paper alignment

The current paper-facing development follows Csima–Harizanov–Miller–Montalbán, *Computability of
Fraïssé limits* (JSL 76(1), 2011). When a declaration formalizes or adapts a numbered paper
result, its docstring records the citation and whether the formal statement is exact,
specialized, strengthened, or weaker. Landmarks include the empty-capable form of Theorem 2.8 and
both effective-search routes underlying Observation 2.7.

The coverage map and dependency order live in
[tracking issue #15](https://github.com/cameronfreer/computable-model-theory/issues/15) as the
source of truth, reducing duplication and drift.

## Using the library

```lean
import ComputableModelTheory                        -- everything
import ComputableModelTheory.Computability          -- the relative-computability substrate
import ComputableModelTheory.ModelTheory.Syntax     -- effective languages and coded syntax
import ComputableModelTheory.ModelTheory.Computable -- structures, presentations, diagrams
import ComputableModelTheory.ModelTheory.Age        -- ages, potential embeddings, witnesses
```

The substrate is usable on its own: `ComputableModelTheory.Computability` mentions no model
theory, and `ModelTheory.Syntax` mentions no structures.

The library is pre-1.0 and its API is not yet stable; downstream users should pin a commit.

Computability notions are relative to a set of oracles and named `…In O`; absolute statements are
the specialization, not the primitive. Every module carries a header docstring stating what it
provides and, where the choice was not forced, why it is shaped the way it is.

## Building and verification

Requires the Lean toolchain pinned in `lean-toolchain` (managed by
[elan](https://github.com/leanprover/elan)).

```
lake exe cache get
lake build
scripts/run-audit-modules.sh
```

Audit modules sit outside the root import spine. They pin public API contracts as acceptance
tests — including behavioral gates on concrete fixtures, not type-checking alone — and check the
axiom policy on those contracts. The runner discovers them from the git index, so a new audit
module cannot be silently skipped.

Audited public contracts are checked to use only `propext`, `Classical.choice` and `Quot.sound`;
the library declares no custom axioms.

## Dependencies

Built on mathlib. Classical infinitary-logic foundations — atomic diagrams, back-and-forth, and
Henkin completeness — are imported from
[infinitary-logic](https://github.com/cameronfreer/infinitary-logic) as a pinned dependency rather
than reproved here.

## License

Released under the Apache 2.0 license, following mathlib convention; see [LICENSE](LICENSE).
Source files carry the corresponding mathlib-style copyright headers.
