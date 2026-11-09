# Paper-to-Lean correspondence

This development follows **Properties of Public Announcements as Operators:
Commutativity, Monotonicity, Idempotence, Fixed points, and Stabilization**,
`Properties_of_PAL_and_BPAL_Operators/Properties_of_PAL_and_BPAL_Operators.tex`
at manuscript commit
[`3cc277515ae735f55c299d661a219452d7fff4b5`](https://github.com/eiyamada/Properties_of_PAL_and_BPAL_Operators/blob/3cc277515ae735f55c299d661a219452d7fff4b5/Properties_of_PAL_and_BPAL_Operators/Properties_of_PAL_and_BPAL_Operators.tex).
The source SHA-256 is
`C0378A7AE6E9E12DF71BF62E443AEC2F8EAD61AF353090CBE0FA81AC8AB98668`.

The paper uses one counter for its 28 numbered items. Names below are in
`PropertiesOfPublicAnnouncementsAsOperators` unless a namespace is explicitly given.
The root module imports the complete development; the actual Lean statements
are authoritative about quantifiers and hypotheses.

## Semantic conventions

- The reused `ClassificationSigmaValidity.Model`, `Formula`, `PALFormula`, and
  `BPALFormula` give actual Kripke models and syntax. BPAL updates preserve
  worlds and valuations and remove arrows according to their **targets**.
- PAL updates are represented by subsets of a fixed ambient model. Their
  induced relations and valuations are those of `Model.restrict`; equality of
  these subsets is equality of induced models, with world names retained.
  `pal_satisfies_restrict` in `Compatibility.lean` proves the semantic bridge.
- `ArrowSubmodel` compares models on the same world type. The revised general
  BPAL order is `BPALSubmodel N M`, with `N` on an arbitrary subtype and with
  its arrows included in the induced restriction of `M`. Thus the development
  includes both state and arrow deletion as required by the revised Definition
  5. `GeneralSubmodels.lean` proves the operator and fixed-point results for
  that broader order.
- Pointed conditions quantify over an actual world, so allowing empty world
  types does not introduce empty pointed models. Empty PAL domains are allowed.
- Most semantic results are universe polymorphic. The finite-modal-type proof
  of the syntactic preservation characterization uses `Atom Agent World : Type`
  (Lean's universe 0). This permits arbitrary infinite models, not just finite
  or countable ones. Fresh-atom results assume `Infinite Atom`; nonempty-agent
  assumptions are explicit. The paper's `Nat` atoms and finite nonempty agents
  satisfy these requirements.
- Frame-relative algebra is proved pointwise, or for all valuations on one
  arbitrary frame. It therefore applies to arbitrary classes of input frames
  without assuming that BPAL preserves the class. Sequences include the empty
  sequence, whose update and modality prefix are identities.
- Common belief uses positive transitive closure; generated submodels use
  reflexive transitive closure. All rank comparisons use static formulas, as
  the revised Theorem 24 explicitly requires.
- Ordinals live in `Ordinal.{max u w}` for world universe `u` and agent universe
  `w`. Each arbitrary ordinal is realized using its actual `toType` carrier.
  The rank is a least stable ordinal, not a supplied stabilization bound.

## Definitions and algebra

| Paper | Lean declarations and files |
| --- | --- |
| Definitions 1–3: the languages | Reused `Formula`, `PALFormula`, `BPALFormula` in `ClassificationSigmaValidity.Syntax`; their semantics and reduction to the static language are in `DynamicLanguages` and `Expressivity`. |
| Definitions 4–7: models, orders, updates, satisfaction | Reused `Model`, `Model.restrict`, generated-model definitions, and semantic functions; `palUpdate`, `bpalUpdate`, `bpalUpdateModel` in [Algebra.lean](Algebra.lean); `ArrowSubmodel` in [Preservation.lean](Preservation.lean), `BPALSubmodel` in [GeneralSubmodels.lean](GeneralSubmodels.lean). |
| Definition 8: four one-step notions | `PalSuccessful`, `PalSelfRefuting`, `PalTrueLie`, `PalImpossibleLie` and their `Bpal` counterparts in [Notions.lean](Notions.lean) use the full dynamic languages and their actual announcement semantics. `palSuccessful_iff_idempotent` and `palSelfRefuting_iff_square_zero` connect the named notions with operators. |
| Lemma 9: sequential announcements | `palUpdate_sequential`, `bpalUpdate_sequential` in [Algebra.lean](Algebra.lean); `guarded_pal_bpal_equivalent` in [Compatibility.lean](Compatibility.lean). Sequence functions also interpret arbitrary finite lists. |
| Lemma 10: equality and validity | `palUpdate_eq_iff`, `bpalUpdate_eq_iff` in [Algebra.lean](Algebra.lean). BPAL equality tests truth at original arrow targets; it does not falsely equate it with unboxed pointwise equivalence on one model. |
| Lemma 11: equality of sequences and all postconditions | `palSequence_eq_iff` in [Algebra.lean](Algebra.lean), `bpalSequence_eq_iff_observations` in [Observations.lean](Observations.lean). The BPAL converse proves fresh-atom invariance and changes only the valuation of an unused atom to distinguish a retained edge. |
| Theorem 12: commutativity | Algebraic truth and case-split characterizations in [Algebra.lean](Algebra.lean); `pal_commute_iff_postconditions`, `bpal_commute_iff_postconditions`; `pal_bpal_commute_iff` in [Compatibility.lean](Compatibility.lean) supplies the reflexive/static comparison. |
| Theorem 13: strong commutativity | `PalStrongCommute`, `BpalStrongCommute` and their mutual-preservation characterizations in [Algebra.lean](Algebra.lean); both `*_strongCommute_iff_postconditions`; `pal_bpal_strongCommute_iff`. |
| Corollary 14: extra condition for strong commutation | Both `*_strongCommute_iff_commute_preserve` results in [Algebra.lean](Algebra.lean). |
| Proposition 21: deflationarity, success, self-refutation | Domain and arrow deflationarity; `pal_idempotent_iff_success`, `pal_square_zero_iff`, `bpal_idempotent_iff_target_success`, `bpal_square_zero_iff` in [Algebra.lean](Algebra.lean). [AlgebraGlobal.lean](AlgebraGlobal.lean) proves the full unboxed BPAL equivalences over K using a fresh predecessor: `bpal_global_idempotent_iff_success`, `bpal_global_square_zero_iff_selfRefuting`, and the actual-model bridge. `Universal.update_idempotent` and `Universal.pal_update_idempotent` prove part (4). |

The algebra module also proves identity, zero, and the no-nontrivial-inverse
consequence of deflationarity; composition associativity is the ordinary
`Function.comp_assoc`. [Countermodels.lean](Countermodels.lean) contains actual
two-world models for noncommutativity and strictness of the fixed-disjunction
inclusion. [Examples.lean](Examples.lean) supplies both-logics absorption and
monotonicity counterexamples. Its distinct formulas `p ∧ ◇¬p` and
`(p ∧ ◇¬p) ∧ q` commute on every model (`Examples.pal_moore_commute` and
`Examples.bpal_moore_commute`) but fail strong commutation on an explicit
two-world S5 model (`Examples.pal_moore_not_strong` and its BPAL counterpart).

## Preservation and monotonicity

| Paper | Lean declarations and proof content |
| --- | --- |
| Definitions 15–18 | `PALPositive`, `PALNegative`, `BPALPositive`, `BPALNegative` in [AnnouncementMonotonicity.lean](AnnouncementMonotonicity.lean), and `PALMonotone`, `BPALMonotone` in [OperatorCharacterizations.lean](OperatorCharacterizations.lean); deletion predicates, `Bisimulates`, `Simulates`, `Refines`, `Universal`, and `Existential` in [Preservation.lean](Preservation.lean). |
| Theorem 19: semantic preservation equivalences | `deletionMonotone_iff_submodelPreserved`, `submodelPreserved_iff_refinementPreserved`, and their existential duals. The refinement converse uses a concrete covering model and a proved bisimulation, not a preservation axiom. |
| Theorem 19: syntactic characterization | [ModalPreservation.lean](ModalPreservation.lean) constructs finite modal types, a canonical model, genuine refinements, universal characteristic formulas, and their finite disjunction. `submodelPreserved_iff_universalEquivalent`, `deletionMonotone_iff_universalEquivalent`, and `refinementPreserved_iff_universalEquivalent` express the result. [FragmentDuality.lean](FragmentDuality.lean) proves syntactic negation duality. |
| Theorem 19: all eight universal conditions | `pal_universal_characterizations` and `bpal_universal_characterizations` in [Monotonicity.lean](Monotonicity.lean) state the seven equivalences with universal definability, hence the full eight-way equivalence. They include the actual operator comparisons from [OperatorCharacterizations.lean](OperatorCharacterizations.lean). PAL operator monotonicity is `PALOperatorMonotone`; BPAL uses `GeneralBPALOperatorMonotone`, allowing both smaller domains and fewer arrows. |
| Theorem 19: all eight existential conditions | `pal_existential_characterizations` and `bpal_existential_characterizations` in [Monotonicity.lean](Monotonicity.lean) assemble the dual eight-way equivalences. `deletionAntimonotone_iff_existentialEquivalent`, `extensionPreserved_iff_existentialEquivalent`, and `simulationPreserved_iff_existentialEquivalent` provide the syntactic converse, using the proved negation duality. |
| Theorem 19: final distinction between the logics | `palMonotone_iff_valid` and `bpalMonotone_iff_negative` in [OperatorCharacterizations.lean](OperatorCharacterizations.lean) prove the two final displayed equivalences. |
| Theorem 19: arbitrary announcement-language formulas | [DynamicMonotonicity.lean](DynamicMonotonicity.lean) proves `palUpdate_reduction` at every current domain and `bpalUpdateModel_reduction` for actual dynamic updates. `pal_dynamic_announcement` and `bpal_dynamic_announcement` identify dynamic postconditions with their static reductions. The direct characterization theorems are `pal_dynamic_universal_preservation`, `bpal_dynamic_universal_preservation`, `pal_dynamic_operator_characterization`, and `bpal_dynamic_operator_characterization`. These transports justify applying the static packages to formulas with nested announcements. |
| Corollary 20(1) iff (2): propositionality and the two fragments | `propositionalEquivalent_iff_both_fragments` in [Propositional.lean](Propositional.lean). The supporting `propositionalEquivalent_iff_both_deletion` constructs a propositional equivalent by evaluating boxes in an edgeless model; propositional negation normal forms belong to both syntactic fragments. |
| Corollary 20(1) iff (3) and (4): composition and atom commutation | `propositional_iff_pal_composition`, `propositional_iff_bpal_composition`, `propositional_iff_pal_atom_commutation`, and `propositional_iff_bpal_atom_commutation` in [OperatorCharacterizations.lean](OperatorCharacterizations.lean). The converse uses a fresh atom to test an arbitrary induced domain and, for BPAL, a fresh predecessor to detect worlds without an initial incoming arrow. The dynamic update reductions above transport these operator equalities to the relevant announcement language. |

## Fixed points and transfinite dynamics

| Paper | Lean declarations and proof content |
| --- | --- |
| Definition 22: iteration, least rank, terminal model | [AbstractIteration.lean](AbstractIteration.lean) defines `AbstractIteration.iterate` for arbitrary deflationary set operators, proves zero/successor/limit equations, existence and leastness of `rank`, permanence, and terminal fixedness; monotonicity additionally gives `terminal_eq_union_fixed`. Sets represent surviving worlds for PAL and retained labelled arrows for BPAL. Reused `EventualAndStrongEventualNotionsInPublicAnnouncements.ordinalUpdate` specializes to actual BPAL models. [Dynamics.lean](Dynamics.lean) supplies `palDomain`, its induced-model semantics, `PALStable`, `BPALStable`, `palRank`, `bpalRank`, `palTerminal`, and `bpalTerminal`. [FiniteRank.lean](FiniteRank.lean) defines the finite ranks `palFiniteRank` and `bpalFiniteRank` in `WithTop Nat`, proves the least-finite-stage characterization, and equates finiteness with ordinal rank below omega. |
| Theorem 23(1)–(2): fixed-point laws | `pal_fixed_iff`, `bpal_fixed_iff`, both `*_fixed_neg_iff_zero`, `*_fixed_composition_iff`, and `*_fixed_conj_iff`, plus the disjunction inclusions in [Algebra.lean](Algebra.lean). These are local model equalities, without commutativity hypotheses. |
| Theorem 23(3): universal formulas | `Universal.fixed_downward`, `.absorption`, `.composition_idempotent` in [Preservation.lean](Preservation.lean); `.general_fixed_downward` in [GeneralSubmodels.lean](GeneralSubmodels.lean); PAL counterparts in [PALFixedPoints.lean](PALFixedPoints.lean). `Universal.pal_terminal_eq_update`, `.pal_terminal_composition`, and `.terminal_composition` identify terminal values with the corresponding first updates, also for sequential composition. |
| Theorem 23(4): existential formulas | [FixedPoints.lean](FixedPoints.lean) proves `bpalTerminal_greatest`, `bpalTerminal_rel_iff_exists_fixed`, and `Existential.terminal_order_independent`. [PALFixedPoints.lean](PALFixedPoints.lean) proves `palTerminal_eq_union_fixed` and `Existential.pal_terminal_order_independent`. The composite formula `sequentialFormula` is proved to implement actual sequential updates. The broader-domain BPAL greatest-fixed-point property is `Existential.general_terminal_greatest`. |
| Theorem 24(1): rank comparison | `stabilization_rank_comparison`, `stabilization_rank_eq_of_incoming`, and `stabilization_rank_eq_of_s5` in [Dynamics.lean](Dynamics.lean). The proof establishes the PAL/BPAL orbit correspondence, including limits and permanence after a stable step. |
| Theorem 24(2): finite bound | `palRank_le_card`, `bpalRank_le_card`. A strictly decreasing finite chain consumes a different world at each step, proving the bound by the number of worlds rather than by the number of arrows. |
| Theorem 24(3): image-finite bound | `eventually_omega_satisfies`, `palStable_omega_of_imageFinite`, and `imageFinite_stabilization` in [ImageFinite.lean](ImageFinite.lean). The proof is by structural induction with finite successor thresholds. It even permits infinitely many agents because each formula uses only finitely many modalities. |
| Theorem 24(4): arbitrary positive ordinals | [OrdinalWitness.lean](OrdinalWitness.lean) uses the fixed formula `p ∧ ◇(p ∧ □¬p)` and an actual ordinal-order model with a predecessor; `OrdinalWitness.ranks_eq` proves both ranks exactly equal to each positive ordinal. [S5OrdinalWitness.lean](S5OrdinalWitness.lean) proves the two-agent S5 construction for `L¬L⊤`, its exact stage models, strictness at every earlier stage, and equality of ranks. Both namespaces supply `formulaMany` and `ranks_eq_many`, transporting the constructions to any atom/agent alphabet with the required chosen atom and one or two agents. |
| Footnote to Theorem 24: single-agent S5 bound | `singleAgent_s5_rank_bound` in [SingleAgentBound.lean](SingleAgentBound.lean) proves equality of PAL/BPAL ranks and the bound `2^k`, where `k` is the number of atoms in the formula. The supporting BPAL bound even holds on K45 models. |
| Theorem 25: finite stabilization | [FiniteStabilization.lean](FiniteStabilization.lean) proves both `*_finite_stabilization_iff_uniform` using an actual dependent disjoint union, then `theta_truth` and `pal_stable_iff_theta_equivalent`. [Stabilization.lean](Stabilization.lean) proves both `*_finite_stable_iff_idempotent`; [Incoming.lean](Incoming.lean) transfers uniform bounds between PAL and BPAL. `theorem25_pal` and `theorem25_bpal` in [DynamicsMain.lean](DynamicsMain.lean) assemble all four conditions. No compactness premise is supplied. |
| Theorem 26: omega stabilization | Both `*_omega_stable_iff_idempotent` and `*_omega_stable_iff_commutes` in [Stabilization.lean](Stabilization.lean), with ordinal restart and `1 + ω = ω`. `global_palStable_iff_bpalStable` and `global_palRank_le_iff_bpalRank_le` in [Incoming.lean](Incoming.lean) prove the cross-logic equivalence via fresh predecessors. `theorem26_pal`, `theorem26_bpal`, and `theorem26_pal_iff_bpal` in [DynamicsMain.lean](DynamicsMain.lean) package the results. |

The S5 ordinal witness uses nonempty finite histories of ordinal elements. A
history can be a child only when its new ordinal is smaller than its parent's;
other histories are separate roots. This gives additional copies of the same
rank components, retains S5 equivalence relations, and has the same exact
peeling ranks as the manuscript's strictly decreasing sequences.

## Common belief and extinction

| Paper | Lean declarations and proof content |
| --- | --- |
| Definition 27 | `Extinction.CommonlyUnknowable`, `CommonlyUnbelievable`, `InformativeWhenTrue`; the frame-relative `UnknowableOn`, `UnbelievableOn`, `InformativeOn`, and `InformativeWhenTrueOn`. These use the existing actual `Common` and `GeneratedUnchanged` predicates. |
| Theorem 28 over K, BPAL | `Extinction.theorem28_K` in [Extinction.lean](Extinction.lean) assembles all seven conditions. `OnlyZeroFixed`, `FiniteExtinction`, and `OrdinalExtinction` are independently defined, and the equivalences are proved. |
| Theorem 28 over K, PAL | `Extinction.theorem28_K_pal` in [ExtinctionS5.lean](ExtinctionS5.lean), together with the common-belief/informativeness/Moore equivalences in [Extinction.lean](Extinction.lean). |
| Finite-model step | [Filtration.lean](Filtration.lean) constructs minimal filtration over arbitrary K frames and proves its truth lemma and preservation of original edges. For S5 the existing transitive-Euclidean filtration supplies an actual finite S5 model. |
| Serial classes | `serial_unknowable_iff_unbelievable` and `unbelievableOn_iff_informativeOn` in [ExtinctionOnClasses.lean](ExtinctionOnClasses.lean). A serial successor is used explicitly; no serial assumption is silently applied to K. |
| Theorem 28 over S5 | `theorem28_S5_dynamics` and `theorem28_S5_logical` in [ExtinctionS5.lean](ExtinctionS5.lean). Terminal BPAL models are handled through their surviving induced S5 submodel; BPAL is not assumed to preserve reflexivity. |
| Theorem 28(6)–(7), arbitrary frame classes | `unknowableOn_iff_common_implies_neg` and `unknowableOn_iff_moore` in [ExtinctionOnClasses.lean](ExtinctionOnClasses.lean) give the class-relative common-belief implication and generalized Moore equivalence. |
| Closing remark and abstract: informativeness with unbounded ranks | [InformativeWitnesses.lean](InformativeWitnesses.lean) proves common unknowability and informativeness of both ordinal-witness formulas. `informative_K_unbounded_ranks_many` realizes every positive ordinal using the same always-informative formula in any language with a chosen atom and agent. `informative_s5_unbounded_ranks_many` does so on S5 for any language with a chosen atom and two distinct agents. |

## Reproducing verification

The project pins Lean and mathlib 4.22.0. From the repository root:

```text
lake exe cache get
lake --wfail build
lake env lean scripts/PropertiesOfPublicAnnouncementsAsOperatorsAxiomAudit.lean
```

The audit traverses every declaration in the paper namespace and all transitive
dependencies. It rejects any axiom other than `propext`, `Classical.choice`, and
`Quot.sound`, including `sorryAx`. A source scan additionally checks for
admissions, custom axioms, and unsafe declarations. The development does not
replace a preservation theorem, stabilization theorem, finite-model property,
or countermodel trace by an assumed premise.

Verification completed with all four paper libraries passing the build with
warnings treated as errors. The namespace audit checked 1,024 declarations
and found only the three standard axioms listed above. All 34 paper modules
are imported by the root module.

See [MANUSCRIPT_NOTES.md](MANUSCRIPT_NOTES.md) for the interpretation of the
revised source and the distinction between pointwise and uniform bounds.
