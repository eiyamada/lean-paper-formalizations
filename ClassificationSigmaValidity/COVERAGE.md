# Formalization coverage

This file maps the mathematical content of the latest local TeX source of
*Classification of sigma-validity in iterated announcements* to the Lean 4
development. Every item listed as complete has a kernel-checked proof and uses
neither `sorry` nor a project-specific axiom.

## Main definitions and infrastructure

| Paper content | Lean module | Status |
|---|---|---|
| Basic modal, PAL, and BPAL syntax | `Syntax.lean` | complete |
| Kripke semantics and believed-announcement update | `Semantics.lean` | complete |
| Recursive PAL and BPAL semantics | `DynamicLanguages.lean` | complete |
| PAL/BPAL elimination and equal expressive power with the basic language | `Expressivity.lean` | complete |
| Frame conditions and modal agreement | `Frames.lean` | complete |
| K45, KD45, and S5 model classes | `FrameClass.lean` | complete |
| Generated submodels, restrictions, and update locality | `Locality.lean` | complete |
| Finite/infinite bit patterns and sigma-validity | `Patterns.lean` | complete |
| Prefix lemmas for validity and satisfiability | `PatternLemmas.lean` | complete |
| Reduction of iterated basic-modal BPAL announcements to basic modal formulas | `Reduction.lean` | complete |
| Finite survivor-set dynamics and stabilization | `FiniteDynamics.lean` | complete |
| Finite-model property for K45, KD45, and S5 | `FiniteModelProperty.lean` | complete |

## Paper lemmas

| TeX item | Lean module | Status |
|---|---|---|
| Modal agreement lemma | `Frames.lean` | complete |
| `00`-validity collapse | `Collapse.lean`, `SingleAgentKD45.lean` | complete |
| `11`-validity collapse | `Collapse.lean` | complete |
| `10^k`-validity collapse | `Collapse.lean` | complete |
| `101`-validity collapse | `Collapse.lean` | complete |
| K45 nonexistence of nontrivial `01^k0` | `NonexistenceK45S5.lean` | complete |
| Single-agent KD45 nonexistence of nontrivial `01^k0` | `NonexistenceK45S5.lean` | complete |
| S5 nonexistence of nontrivial `0^k1` and `01^k0` | `NonexistenceK45S5.lean` | complete |
| Finite-depth multi-agent KD45 unravelling | `Unravelling.lean` | complete |
| Unravelling truth lemma | `Unravelling.lean` | complete |
| Diagonal-model equivalence and update commutation | `Diagonal.lean`, `Unravelling.lean` | complete |
| Multi-agent KD45 nonexistence of nontrivial `0^k1` and `01^k0` | `Unravelling.lean`, `AgentSupport.lean` | complete (arbitrary inhabited ambient agent type) |
| Exact type formulas `chi_t` and successor descriptions `E_X` | `TypeFormulas.lean`, `TypeDynamics.lean` | complete |
| KD45 `0^k` witness hierarchy (`k >= 2`, two distinct agents) | `ExistenceKD45Zero.lean` | complete (universe-polymorphic finite countermodel) |
| K45/KD45/S5 `01^k` witness hierarchy (`k >= 1`) | `ExistenceZeroOne.lean` | complete |
| S5 `0^k` witness hierarchy (`k >= 2`) | `ExistenceS5Zero.lean` | complete |
| Constant, Moore, true-lie, and `101` examples | `Examples.lean` | complete |

## Classification theorem

| Component | Lean module | Status |
|---|---|---|
| Equality of validity classes | `EquivalenceClasses.lean` | complete |
| Admissibility of all displayed representatives | `WellDefinedness.lean` | complete |
| Pairwise separation of displayed classes and parametric hierarchies | `ClassificationDisjointness.lean` | complete |
| Exhaustive K45 normal form | `Classification.lean` | complete |
| Exhaustive single-agent KD45 normal form | `Classification.lean` | complete |
| Exhaustive S5 normal form | `Classification.lean` | complete |
| Exhaustive multi-agent KD45 normal form | `Classification.lean` | complete (arbitrary inhabited ambient agent type) |

## Explicit proof repairs

The Lean statements expose conditions that are used implicitly in the prose:

- the multi-agent KD45 `0^k` witness requires two distinct agents;
- the finite unravelling is supplied with finite worlds and a finite set of
  relevant agents (the set of agents occurring in a formula is finite);
- modal-depth-zero announcements are handled separately;
- the least index in the KD45 witness is chosen among actually accessible
  typed worlds, and the first-stage case uses seriality.
- the type assignment in TeX line 1095 is read at the world `w` (the displayed
  `M,t` is a variable typo), and successor-set agreement in line 1107 is used
  only for the fixed modality whose arrow connects the worlds, as warranted
  by transitivity and Euclideanness.

The paper's displayed `01^k` witness contains a connective mismatch: the
displayed `chi_(a_0) or E_(Y_0)` makes the advertised transition false, while
the following prose, cases, and figures use `chi_(a_0) and E_(Y_0)`. The Lean
development formalizes and proves the latter, proof-intended formula. The TeX
source is not changed.

## Scope notes

- TeX line 140's cited equal-expressive-power result is proved by translations
  for arbitrarily nested PAL and BPAL announcements in `Expressivity.lean`.
- The paper builds nonemptiness into the definition of a model. Lean's
  `Model` leaves the world type unrestricted, while every pointed semantic
  claim and every satisfiability witness explicitly supplies a world. The
  theorem `Sigma.valid_iff_validOnNonemptyModels` proves that this does not
  change validity; all concrete witnesses are nonempty.
- The paper's definition of infinite sigma-validity via all finite prefixes is
  proved equivalent to the direct all-coordinate trace formulation by
  `Sigma.valid_infinite_iff_all_finitePrefixes`.
- The exhaustive normal-form equivalences are packaged separately from
  representative admissibility and pairwise inequality. `WellDefinedness`
  specializes to `Atom := Nat`, matching the paper's countably infinite atom
  stock; modal witnesses require a chosen agent, and the KD45 finite-zero
  hierarchy requires two distinct agents. `ClassificationDisjointness`
  records the corresponding explicit `Not (ValEq ...)` statements.
