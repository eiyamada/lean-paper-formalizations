# Classification of sigma-validity — Lean 4 formalization

This repository contains a Lean 4 formalization accompanying the paper
*Classification of sigma-validity in iterated announcements* (<https://arxiv.org/abs/2607.04685>) It covers the
modal, PAL, and BPAL definitions; believed public announcements; finite and
infinite truth patterns; the collapse, existence, and nonexistence lemmas; and
the K45, single-agent KD45, multi-agent KD45, and S5 classification results.

The root module is `ClassificationSigmaValidity.lean`. A detailed
paper-to-Lean theorem map is in `COVERAGE.md`.

## Build

The project is pinned to Lean 4.22.0 and mathlib 4.22.0.

```text
lake exe cache get
lake build
```

For the strict check used while preparing this repository:

```text
lake --old --wfail build
```

All paper-specific proofs are theorem proofs checked by Lean's kernel; the
development contains no `sorry`, `admit`, or project-specific axioms.

## Organization

- `Syntax`, `Semantics`, `DynamicLanguages`, and `Expressivity` define the
  three languages, their semantics, and the announcement-elimination
  translations proving their equal expressive power.
- `Frames`, `Locality`, `Reduction`, `FiniteDynamics`, and
  `FiniteModelProperty` provide the semantic infrastructure used by the paper.
- `Collapse`, `NonexistenceK45S5`, and `Unravelling` prove the collapse and
  nonexistence results.
- `TypeFormulas`, `TypeDynamics`, `ExistenceZeroOne`, `ExistenceKD45Zero`,
  `ExistenceS5Zero`, and `Examples` construct the witness families.
- `EquivalenceClasses`, `WellDefinedness`, `ClassificationDisjointness`, and
  `Classification` assemble the final classification.

## Source note

Hypotheses used implicitly in the paper are made explicit in theorem
signatures, notably the two distinct agents needed by the KD45 finite-zero
witnesses. The finite-depth unravelling first works over the finite support of
the announcement formula and is then transferred back to an arbitrary
inhabited ambient type of agents.

The cited background statement that the basic modal, PAL, and BPAL languages
have equal expressive power is proved in `Expressivity.lean`, including
arbitrarily nested announcements and correctness relative to intermediate PAL
domains and BPAL accessibility relations.
