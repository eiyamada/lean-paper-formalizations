# Lean formalizations of Eiji Yamada's papers

This repository collects Lean 4 formalizations accompanying multiple research
papers. Each paper has a root Lean module, a directory of supporting modules,
and a coverage map connecting the manuscript to Lean declarations.

| Paper | Lean entry point | Coverage map | Publication status |
| --- | --- | --- | --- |
| [*Classification of sigma-validity in iterated announcements*](https://arxiv.org/abs/2607.04685) | [`ClassificationSigmaValidity.lean`](ClassificationSigmaValidity.lean) | [`ClassificationSigmaValidity/COVERAGE.md`](ClassificationSigmaValidity/COVERAGE.md) | arXiv preprint |
| *Eventual and Strong Eventual Notions in Public Announcements* | [`EventualAndStrongEventualNotionsInPublicAnnouncements.lean`](EventualAndStrongEventualNotionsInPublicAnnouncements.lean) | [`EventualAndStrongEventualNotionsInPublicAnnouncements/COVERAGE.md`](EventualAndStrongEventualNotionsInPublicAnnouncements/COVERAGE.md) | arXiv submission planned |
| *The Sources of Unknowability and Self-refutation in Epistemic and Dynamic Epistemic Logic* | [`SourcesOfUnknowability.lean`](SourcesOfUnknowability.lean) | [`SourcesOfUnknowability/COVERAGE.md`](SourcesOfUnknowability/COVERAGE.md) | Accepted at the 8th Asian Workshop for Philosophical Logic (AWPL 2026); not yet accepted for the proceedings. An arXiv posting is planned. |

## Build

The Lake project is pinned to Lean 4.22.0 and mathlib 4.22.0. From the
repository root, run:

```text
lake exe cache get
lake build
```

`lake build` checks all three paper libraries. To build one paper separately, use
`lake build ClassificationSigmaValidity`,
`lake build SourcesOfUnknowability`, or
`lake build EventualAndStrongEventualNotionsInPublicAnnouncements`.

On Windows, use a short checkout path if Lake or a dependency fails while
creating files under `.lake` because of the path length.

## Reading the formalizations

Start with a paper's root module and its coverage map. The coverage maps list
the corresponding definitions, intermediate results, and main results, and
record any explicit assumptions or departures from the manuscript. The Lean
source is the authoritative statement of each formalized claim.

The sigma-validity development includes the modal, PAL, and BPAL languages,
announcement dynamics, witness constructions, and K45, KD45, and S5
classification results. The unknowability development covers single-agent and
multi-agent epistemic logic, its dynamic notions, and the Brandenburger–Keisler
paradox; its coverage map specifies the exact formalized scope.

The eventual-notions development covers finite and ordinal announcement
iterations, first-order compactness, all four truth-value classifications,
single-agent collapse, explicit infinite countermodels, and the extensions
to believed-announcement and common-belief languages. Its
[manuscript notes](EventualAndStrongEventualNotionsInPublicAnnouncements/MANUSCRIPT_NOTES.md)
record wording issues noticed during formalization.

To audit the proof dependencies of the eventual-notions development after
building, run:

```text
lake env lean scripts/EventualAndStrongEventualNotionsInPublicAnnouncementsAxiomAudit.lean
```

The audit rejects axioms other than Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`.
