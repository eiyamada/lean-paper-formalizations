# Paper-to-Lean correspondence

This development follows **Eventual and Strong Eventual Notions in Public
Announcements**, `main.tex` at source commit
[`49e893b419533ab577dce5424a567a98e58dbd06`](https://github.com/eiyamada/True_lies_and_impossible_lies/blob/49e893b419533ab577dce5424a567a98e58dbd06/True_lies_and_impossible_lies/main.tex).
The source repository retains its earlier name; the Lean directory, namespace,
and entry point use the paper's current title.

The manuscript has twelve definitions, fourteen results sharing the
lemma/proposition/theorem counter, Example 1, and Remark 1. The tables below map
their statements to declarations. Unless qualified otherwise, declaration names
are in `EventualAndStrongEventualNotionsInPublicAnnouncements`; a filename refers
to this directory. Reused declarations are qualified by
`ClassificationSigmaValidity` and remain in the existing development.

## Scope and conventions

- The basic semantic and dynamical results are universe polymorphic in worlds,
  atoms, and agents. The compactness theorem and final classification packages
  quantify over **every `World : Type`**, with `Atom Agent : Type`. This is Lean's
  universe `Type 0`, not a restriction to finite or countable models. The
  classification witnesses use the countably infinite atom type `Nat`.
- The paper assumes a finite nonempty agent group. Most implications hold here
  without finiteness; strictness requires specified agents `a b` with `a ≠ b`.
  Singleton collapse uses `[Nonempty Agent] [Subsingleton Agent]`. The literal
  finite conjunction of all agents' inconsistent beliefs uses `[Fintype Agent]`.
- A model is K45 precisely when every agent's relation is transitive and
  Euclidean. Seriality and reflexivity are not hypotheses. Every pointed-model
  condition quantifies over a world, so allowing an empty ambient world type in
  the definitions does not change those conditions.
- Believed announcement retains all worlds and valuations and removes arrows
  whose **targets** fail the announced formula. Common belief uses positive
  transitive closure; generated submodels use reflexive transitive reachability.
- `Eventual` and `StrongEventual` require positive natural thresholds. The strong
  condition quantifies over all later natural stages. Their ordinal versions
  require positive ordinals and, for the strong version, all later ordinals in
  `Ordinal.{max u w}` for world universe `u` and agent universe `w`.
- `FiniteStageCondition` includes stage zero. `OrdinalStageCondition` includes
  every ordinal, including zero and limits. Their initial-value premise is
  evaluated in the original model, not again at the stage being tested.
- A uniform hitting bound permits a model-dependent hitting time in `1,...,N`.
  `UniformExtinction` is the stronger exact-stage conclusion used for eventual
  self-refutation: at one common stage the formula is false and all arrows are
  absent. These notions are not identified by definition.
- The real trace statements use mathlib's actual `Tendsto`, `limsup`, and
  `liminf`. They are connected to the Boolean trace by proved equivalences.

## Definitions

| Paper | Lean representation |
| --- | --- |
| Definition 1: basic epistemic language | `ClassificationSigmaValidity.Formula` in `Syntax.lean`; derived disjunction, implication, diamond, truth, falsity, and finite atom support are defined there. |
| Definition 2: PAL | `ClassificationSigmaValidity.PALFormula`; `PAL.Satisfies` and `PAL.InitiallySatisfies` in `DynamicLanguages.lean`. |
| Definition 3: BPAL, and the common-belief extensions | `ClassificationSigmaValidity.BPALFormula` and `BPAL.Satisfies`; `CommonFormula` and `BPALCFormula` in [RichLanguage.lean](RichLanguage.lean). The latter allow arbitrary nesting of common belief and announcements. |
| Definition 4: Kripke model | `ClassificationSigmaValidity.Model` in `Semantics.lean`; `IsK45`, `IsKD45`, and `IsS5` in `Frames.lean`. |
| Definition 5: relativized models | `Model.restrict` in the reused `Locality.lean` for world restriction; `Model.update` in `Semantics.lean` for believed-announcement arrow restriction. `PAL` and `BPAL` also give direct recursive dynamic semantics. |
| Definition 6: satisfaction, validity, common belief | `Model.Satisfies`, the `PAL`/`BPAL` semantic functions, and `Common` in [Definitions.lean](Definitions.lean). Validity is written as universal quantification over models and points. Rich common belief is interpreted recursively in `BPALC.Satisfies`. |
| Definition 7: submodel and generated submodel | Reused `Model.IsSubmodel`, `Model.generatedSet`, `Model.generatedSubmodel`, `Model.generatedPoint`, and their locality theorems. `GeneratedUnchanged` records equality of generated domains and agreement of relations and valuations on that domain. |
| Definition 8: ordinal iteration | `ordinalUpdate` in [OrdinalDynamics.lean](OrdinalDynamics.lean), defined by ordinal recursion. Zero, successor, natural-stage, limit-intersection, and ordinal-addition identities are proved. |
| Definition 9: four one-step notions | Reused `ClassificationSigmaValidity.Sigma.Successful`, `SelfRefuting`, `TrueLie`, `ImpossibleLie` in `Patterns.lean`, with the four corresponding two-bit-validity equivalences. |
| Definition 10: eventual notions, always informativeness, stage conditions, trace | `Eventual`, `StrongEventual`, `AlwaysInformative`, `StageCondition`, `FiniteStageCondition` in [Definitions.lean](Definitions.lean); the three ordinal predicates in [OrdinalConditions.lean](OrdinalConditions.lean); reused `Model.trace` and `realTrace` in [NumericTraces.lean](NumericTraces.lean). |
| Definition 11: two-peeling model | `Oscillation.PeelingWorld`, `RA`, `RB`, valuation, and `twoPeeling` in [Oscillation.lean](Oscillation.lean), with K45 and exact finite iteration proofs. |
| Definition 12: one-peeling model | `OnePeeling.World`, `block`, `target`, `alive`, `valuation`, and `modelAt` in [PeelingModels.lean](PeelingModels.lean). `modelAt false 0` supplies the ordinary model; `modelAt true 0` adds the persistent target for Lemma 12. Branch index `m` represents manuscript branch length `m+1`. |

The reusable one-peeling carrier retains a `persistent` constructor in both
versions. With `keep = false` no arrow targets it, so it is outside the root's
generated component. This does not change any root trace. The rank countermodel
for Lemma 7 similarly uses reversed lists as a convenient ambient carrier; its
root-generated component follows the decreasing-sequence construction.

## Foundational results and finite/ordinal implications

| Paper result | Declarations and proof content |
| --- | --- |
| Lemma 1, all six BPAL reduction axioms | `Reduction.atom`, `.neg`, `.conj`, `.box`, `.diamond`, `.composition` in [Reduction.lean](Reduction.lean), for arbitrary BPAL formulas. Reused `BPALFormula.toFormula`, `BPAL.initiallySatisfies_toFormula`, and `BPAL.equiexpressive_with_basic` in `Expressivity.lean` supply actual announcement elimination. |
| Lemma 2, box and diamond agreement | Reused `Model.modalAgreement_box` and `Model.modalAgreement_dia` in `Frames.lean`, from equality of successor sets along a K45 arrow. |
| Proposition 3, ordinal stabilization and common belief | `exists_ordinalUpdate_stableStep_bounded`, `exists_ordinalUpdate_stableStep`, `common_of_update_eq_self`, and `ordinal_stabilization` in [OrdinalDynamics.lean](OrdinalDynamics.lean). The proof bounds strictly decreasing stages by the cardinality of original labelled arrows. No stabilization or compactness premise is assumed, and K45 is not required. |
| Lemma 4(1), generated-model fixedness | `generatedUnchanged_iff_common` in [CommonBelief.lean](CommonBelief.lean). Local agreement and common-belief permanence are proved separately. |
| Lemma 4(2), eventuality and finite stage conditions | `eventual_implies_finiteStageCondition`, `alwaysInformative_iff`, `finiteStageCondition_reversal_iff`, and `alwaysInformative_iff_finiteStageCondition` in [CommonBelief.lean](CommonBelief.lean). |
| Lemma 4(3), compactness and uniform finite bound | `FirstOrderEncoding.compactness_sequence` in [FirstOrder.lean](FirstOrder.lean) translates pointed K45 models to first-order structures and applies mathlib first-order compactness. `eventual_iff_uniformBound` in [Compactness.lean](Compactness.lean) instantiates it using announcement reduction. |
| Lemma 4(4), eventual self-refutation, strong self-refutation, extinction | `uniformBound_self_refuting_iff_extinction`, `uniformExtinction_implies_strongEventual` in [FiniteConditions.lean](FiniteConditions.lean); `eventual_self_refuting_iff_extinction` and `eventual_self_refuting_iff_strongEventual` in [Main.lean](Main.lean). |
| Lemma 5, every implication and equivalence | `strongEventual_implies_eventual` in [FiniteConditions.lean](FiniteConditions.lean); `eventual_implies_ordinalEventual`, `ordinalStrongEventual_implies_ordinalEventual`, `ordinalEventual_implies_finiteStageCondition`, `ordinalStageCondition_iff_ordinalStrongEventual`, and `ordinal_reversal_equivalences` in [OrdinalConditions.lean](OrdinalConditions.lean). The proof uses actual ordinal tails and common-belief permanence. |
| Lemma 6, positive finite stabilization with one agent | `singleAgent_generated_exists_stableStep`, `singleAgent_exists_positive_common`, and `singleAgent_finiteStageCondition_implies_strongEventual` in [SingleAgent.lean](SingleAgent.lean); `singleAgent_classification` in [Main.lean](Main.lean). The proof uses the finitely many valuation patterns of atoms occurring in the formula, with no finiteness assumption on worlds. |

Example 1 is `selfFulfilling_trueLie` in [Reduction.lean](Reduction.lean).
The reused `Examples.pOrBox_trueLie` is another statement of the same example.
The prose observation that the two always-informativeness properties cannot
hold together is `not_alwaysInformative_both` in [CommonBelief.lean](CommonBelief.lean).

## Separation lemmas and actual countermodels

Every separation below consists of a global membership theorem, an explicit
K45 model, semantic iteration or truth calculations on that model, and a
nonmembership theorem. Traces are proved from models rather than postulated.

| Paper result | Witness and final declarations |
| --- | --- |
| Lemma 7: finite-stage self-refutation/true-lie conditions need not imply finite eventuality | `ReversalSeparations.theta10`, `.theta01`; `theta10_finiteStageCondition`, `theta01_finiteStageCondition`, `theta10_not_eventual`, `theta01_not_eventual`, and `reversal_separations` in [ReversalSeparations.lean](ReversalSeparations.lean). Its `RankModel` proves the rank-peeling dynamics. |
| Lemma 8: eventual success and eventual true lies need not be strong | `Oscillation.theta`; `theta_eventual`, `theta_trueLie`, `theta_not_strongEventual`, and `lemma8` in [Oscillation.lean](Oscillation.lean). The same formula witnesses both failures. The two-peeling root alternates, and its stage-one tail supplies the initial-false witness. |
| Lemma 9: eventual impossible lies need not be strong | `FalseOscillation.theta`; `eventual_impossible_lie`, `root_trace_iff`, `not_strongEventual_impossible_lie`, and `impossible_lie_separation` in [FalseOscillation.lean](FalseOscillation.lean). The proof establishes the `D`, `H`, and `X` shift identities and root alternation. |
| Lemma 10: ordinal strong preservation need not be finitely eventual | `OrdinalReturn.theta11`, `.theta00`; `theta11_ordinalStrongEventual`, `theta00_ordinalStrongEventual`, both `not_eventual` theorems, and `ordinal_return_separations` in [OrdinalReturn.lean](OrdinalReturn.lean). Global ordinal membership follows from ordinal stage conditions; the one-peeling model proves failure at every positive finite stage. |
| Lemma 11: true preservation can be lost at the first limit | `TruePreservation.strongFormula`, `.stageFormula`; `strongFormula_strongEventual` and `stageFormula_finiteStageCondition` in [TruePreservation.lean](TruePreservation.lean). [TruePreservationCountermodels.lean](TruePreservationCountermodels.lean) proves the finite two-peeling dynamics, the edgeless model at `omega`, permanence thereafter, and `limit_loss_separations`. |
| Lemma 12: false preservation can be lost at the first limit | `FalsePreservation.theta00SE`, `.theta00fin`; `theta00SE_strongEventual` and `theta00fin_finiteStageCondition` in [FalsePreservation.lean](FalsePreservation.lean). [FalsePreservationModel.lean](FalsePreservationModel.lean) proves finite traces on one-peeling plus a persistent target; [FalsePreservationCountermodels.lean](FalsePreservationCountermodels.lean) proves the model at `omega`, permanence thereafter, and `lemma12`. |

[Renaming.lean](Renaming.lean) proves preservation of satisfaction, finite and
ordinal iterations, and the global conditions under injective atom/agent
renaming. [Classification.lean](Classification.lean) consequently states the
witnesses over `Nat` atoms and **any** `Agent : Type` with distinct `a` and `b`:
`true_oscillation_witnesses`, `false_oscillation_witness`,
`ordinal_return_witnesses`, `true_limit_loss_witnesses`, and
`false_limit_loss_witnesses`.

## Theorem 13: all four finite classifications

| Part | Equivalences and implications |
| --- | --- |
| (1) Success | `strongEventual_iff_conditional_real_limit`, `eventual_success_iff_real_limsup`, `eventual_iff_uniformBound`, and `eventual_implies_finiteStageCondition`. |
| (2) Self-refutation | `eventual_self_refuting_iff_strongEventual`, `eventual_self_refuting_iff_real_limit`, `eventual_self_refuting_iff_real_liminf`, `eventual_self_refuting_iff_extinction`, `eventual_reversal_implies_alwaysInformative`, and the always-informativeness/stage equivalences from Lemma 4(2). The real limit and liminf statements have no initial-value premise. |
| (3) True lies | `strongEventual_true_lie_iff_real_limit`, `eventual_true_lie_iff_real_limsup`, `eventual_true_lie_iff_unconditional_bound`, `eventual_reversal_implies_alwaysInformative`, and the always-informativeness/stage equivalences. The real trace and bound statements are unconditional over pointed models. |
| (4) Impossible lies | `strongEventual_iff_conditional_real_limit`, `eventual_impossible_lie_iff_real_liminf`, `eventual_iff_uniformBound`, and `eventual_implies_finiteStageCondition`. |

The trace statements are assembled in [Main.lean](Main.lean).
[NumericTraces.lean](NumericTraces.lean) proves
`convergesTo_iff_real_limit`, `cofinal_true_iff_real_limsup`, and
`cofinal_false_iff_real_liminf`.

[FixedPointForms.lean](FixedPointForms.lean) gives the displayed logical forms:

- `common_implies_false_iff_mooreFixedPoint` and
  `common_implies_true_iff_selfFulfillingFixedPoint` prove the two propositional
  fixed-point rewrites.
- `stageCondition_iff_fixedPointView`,
  `finiteStageCondition_iff_fixedPointView`, and
  `alwaysInformative_iff_fixedPointView` put them under precisely the paper's
  global and stage quantifiers.
- `uniformBound_iff_finiteDisjunction` and
  `unconditionalUniformBound_iff_finiteDisjunction` identify the bounds with the
  finite disjunction of positive announcement stages.
- `uniformExtinction_iff_announced_formula` identifies extinction with the
  announced conjunction of `¬φ` and every agent's `□⊥`.

`finite_classification_strictness` in [Classification.lean](Classification.lean)
collects **all seven** displayed strict arrows for at least two agents.
`singleAgent_classification`, together with the numerical, bound, and fixed-point
bridges, gives the itemwise equivalence of every displayed condition for one
agent.

## Theorem 14: all four transfinite classifications

`classification_implications` in [Main.lean](Main.lean) supplies, for all four
bit pairs, `SE → E → EOrd → Sfin`, `SEOrd → EOrd`, and `SOrd ↔ SEOrd`.
`ordinal_reversal_equivalences` supplies all reversal equivalences.
`eventual_self_refuting_iff_strongEventual` supplies the additional finite
self-refutation equivalence. The ordinal fixed-point equation is
`ordinalStageCondition_iff_fixedPointView` in [FixedPointForms.lean](FixedPointForms.lean).

| Parts | Strictness and incomparability |
| --- | --- |
| (1) Success | `success_strict_classification` proves every preservation strict arrow and both incomparabilities. |
| (2) Self-refutation | The first component of `reversal_strict_classification` proves `E10 → EOrd10` is strict. |
| (3) True lies | `true_lie_strong_strict` and the second component of `reversal_strict_classification` prove the two strict arrows. |
| (4) Impossible lies | `impossible_lie_strict_classification` proves every preservation strict arrow and both incomparabilities. |

These are in [Classification.lean](Classification.lean).
[Strictness.lean](Strictness.lean) defines `StrictImplication`, `Incomparable`,
and `PreservationComparison`; incomparability includes a witness for each failed
direction. `singleAgent_classification` proves all six conditions equivalent for
one agent.

## Remark 1: richer languages

The remark is formalized for actual richer syntax and semantics:

| Claim | Modules and declarations |
| --- | --- |
| Both classifications transfer to BPAL | [BPALExtension.lean](BPALExtension.lean) defines direct finite and ordinal BPAL iteration, proves equality with iteration of `BPALFormula.toFormula`, and provides all six `bpal_*_iff` transports. Its update and common-belief equalities, with `BPAL.initiallySatisfies_toFormula`, also transport the trace, bound, and fixed-point formulations. Reused `Formula.toBPAL` embeds each basic witness. |
| Common-belief syntax and semantics | [RichLanguage.lean](RichLanguage.lean) defines `CommonFormula`, `BPALCFormula`, `BPALC.Satisfies`, update, finite iteration, and ordinal iteration; [RichLocality.lean](RichLocality.lean) proves locality for arbitrary nested formulas. The static common-belief language is embedded by `CommonFormula.toBPALC`. |
| Noncompact finite implications and trace characterizations | [RichDefinitions.lean](RichDefinitions.lean), [RichFiniteConditions.lean](RichFiniteConditions.lean), and [RichCommonBelief.lean](RichCommonBelief.lean) define and prove the corresponding rich statements. [RichMain.lean](RichMain.lean) assembles `finite_classification_implications`, `self_refutation_implications`, and the real limit/limsup/liminf equivalences. |
| All noncompact ordinal implications and equivalences | [RichOrdinalDynamics.lean](RichOrdinalDynamics.lean) proves stabilization, ordinal tails, locality, and permanence directly for BPALC. [RichOrdinalConditions.lean](RichOrdinalConditions.lean) proves the full analogue of Lemma 5. `Rich.classification_implications` and `Rich.classification_reversals` assemble them. |
| Fixed-point views | [RichFixedPointForms.lean](RichFixedPointForms.lean) proves the same initial, finite-stage, and ordinal-stage propositional bridges for arbitrary BPALC formulas. |
| All previously strict arrows and incomparabilities remain | [RichExtension.lean](RichExtension.lean) transports predicates along truth-preserving equivalence. [RichStrictness.lean](RichStrictness.lean) assembles the BPALC preservation and reversal strictness, `Rich.finite_classification_strictness`, and transport to the static common-belief language through `commonLanguage_strict_of_basic` and `commonLanguage_incomparable_of_basic`. |
| Full single-agent classifications are recovered | `singleAgent_common_iff_box`, `BPALC.satisfies_toFormula`, and `BPALC.singleAgent_equiexpressive_with_basic` in [RichLanguage.lean](RichLanguage.lean); `Rich.singleAgent_classification`, `singleAgent_eventual_iff_uniformBound`, `singleAgent_eventual_self_refuting_iff_extinction`, `singleAgent_eventual_self_refuting_iff_strongEventual`, and `singleAgent_eventual_true_lie_iff_unconditional_bound` in [RichMain.lean](RichMain.lean). |

For the common-belief languages, no compactness converse is inserted: a uniform
bound is sufficient for eventuality, and uniform extinction implies strong
self-refutation, which implies eventual self-refutation. The paper does not
claim strictness for these newly weakened arrows, and none is asserted here.
The remark's wording concerning the self-refutation limit chain requires the
clarification recorded in [MANUSCRIPT_NOTES.md](MANUSCRIPT_NOTES.md).

## Reading and checking the development

The entry point is `EventualAndStrongEventualNotionsInPublicAnnouncements.lean`.
From the repository root, use:

```sh
lake build EventualAndStrongEventualNotionsInPublicAnnouncements
lake env lean scripts/EventualAndStrongEventualNotionsInPublicAnnouncementsAxiomAudit.lean
```

The complete repository `lake build` succeeded, including this development and
the two existing libraries. The namespace audit checked 1,481 declarations and
their transitive dependencies: the only axioms were Lean's standard
`propext`, `Quot.sound`, and `Classical.choice`. A source scan found no admissions,
custom axioms, or unsafe declarations in the new development. The audit script
rejects any additional axiom.

This document maps mathematical statements rather than duplicating proof terms.
Proof organization sometimes differs from the manuscript: for example, global
ordinal membership plus failure at every finite stage establishes Lemma 10
without needing a separate named theorem for its root's entire ordinal trace.
No theorem is replaced by a supplied compactness, stabilization, or countermodel
trace assumption. Background literature summaries and proposed future research
are not additional classification theorems of this development.
