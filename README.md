# computable-model-theory

A Lean 4 / [mathlib](https://github.com/leanprover-community/mathlib4) library formalizing
computable model theory: effective presentations of first-order languages and structures,
computable ages, potential embeddings and embedding information, and effective Fraïssé
constructions.

The library is a reusable spine over mathlib's `FirstOrder` model theory. Classical
infinitary-logic foundations (Scott sentences, back-and-forth, Henkin construction) are imported
from [infinitary-logic](https://github.com/cameronfreer/infinitary-logic) as a pinned dependency
rather than reproved here.

The formalization target is Csima–Harizanov–Miller–Montalbán, *Computability of Fraïssé limits*
(JSL 76(1), 2011). Paper results are stated with their numbering, and the correspondence to the
paper is maintained deliberately: a definition that specializes a paper notion says so, and a
theorem weaker than its paper counterpart says that too.

## Layout

| Directory | Contents |
|---|---|
| `Computability/` | The oracle-relative substrate: `RecursiveIn` / `ComputableIn` combinators, the predicate layer `ComputablePredIn` / `REPredIn`, partial folds, list operations, reductions and the jump |
| `ModelTheory/Syntax/` | Effective languages, `Primcodable` terms and formulas, computable syntactic operations |
| `ModelTheory/Computable/` | Computable structures and diagrams, tuple closures, computable ages, potential embeddings, partial (possibly-empty) presentation families, effective witness interfaces |
| `ModelTheory/` | Language-independent pieces used by the above (`Age`, `TupleClosure`) |
| `Util/` | The axiom-policy assertion command used by the audit modules |

Roughly: `Computability` knows nothing about model theory, `Syntax` knows nothing about
structures, and `Computable` is where the two meet.

## Orientation

Entry points, depending on what you want:

* **The computability substrate on its own** — `Computability/RecursiveIn.lean` for the
  combinators, `Computability/OraclePred.lean` for the predicate layer. Both are usable
  independently of the model theory and are candidates for upstreaming.
* **How languages become effective** — `ModelTheory/Syntax/EffectiveLanguage.lean`, then the
  `Primcodable` instances for terms and formulas.
* **What a computable age is** — `ModelTheory/Computable/ComputableAge.lean`, then
  `PotentialEmbedding.lean` for embedding data as pure code.
* **The general, possibly-empty-carrier setting** — `ModelTheory/Computable/PartialAge.lean`.
  This is the paper's Definition 2.1; the all-carrier-`ℕ` version is a fragment of it, not the
  other way around.

Every module carries a header docstring stating what it provides and, where the choice was not
forced, why it is shaped the way it is.

## Conventions

**Oracle-relative by default.** Computability notions are relative to a set of oracles and named
`…In O`. Absolute statements are the specialization, not the primitive. Where a result genuinely
needs no oracle it is stated absolutely (`Primrec`, `Computable`) and lifted at the use site.

**Audit modules.** Files named `*Audit.lean` sit outside the root import spine and serve two
purposes: they enforce the axiom policy per declaration via `#assert_standard_axioms`, and they
pin the public API as acceptance tests — including *behavioral* gates on concrete fixtures, not
only type-checking gates. They are checked explicitly:

```
bash scripts/run-audit-modules.sh
```

The script fails if an audit module is untracked, so a new audit cannot be silently skipped.

**Axiom policy.** The spine depends only on `propext`, `Classical.choice` and `Quot.sound`. No
custom axioms and no `sorry` — the audit modules enforce this declaration by declaration rather
than by a global scan.

**Upstreaming.** Generic computability facts here are candidates for mathlib, but they move only
after demonstrated use in this library: a fact with no consumer stays put, however reasonable it
looks. The plan, per-API status, and what is deliberately deferred are tracked in
[#24](https://github.com/cameronfreer/computable-model-theory/issues/24).

## Status and roadmap

Current state and planned work live in the issue tracker rather than in this file, so they cannot
drift out of date:

* [#15](https://github.com/cameronfreer/computable-model-theory/issues/15) — the CHMM
  formalization tracker: what is done, what is next, and in what order.
* [#24](https://github.com/cameronfreer/computable-model-theory/issues/24) — the mathlib
  upstreaming plan.

In broad terms: the computability substrate, effective syntax, computable structures and
diagrams, computable ages with potential embeddings, and the general partial-family setting with
its effective witness interfaces are in place, along with the finite-search decision procedure for
realizability of embedding data. The effective Fraïssé limit itself, and the priority
constructions of the paper's later sections, are the current work.

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (managed by
[elan](https://github.com/leanprover/elan)).

```
lake exe cache get
lake build
bash scripts/run-audit-modules.sh
```

CI does the same, via `leanprover/lean-action` for the build and then the audit sweep.

## License

Released under the Apache 2.0 license, following mathlib convention; see [LICENSE](LICENSE).
Source files carry the corresponding mathlib-style copyright headers.
