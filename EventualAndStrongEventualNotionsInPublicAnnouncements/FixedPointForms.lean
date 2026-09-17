import EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalConditions
import EventualAndStrongEventualNotionsInPublicAnnouncements.Compactness
import ClassificationSigmaValidity.TypeFormulas

/-!
# The displayed fixed-point and finite-disjunction formulas

These bridges identify the semantic conditions with the explicit logical forms
printed in the main theorems. Finite announcement modalities are represented by
their proved reduction into the basic epistemic language.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- The generalized Moore fixed-point view. -/
def MooreFixedPoint (M : Model World Atom Agent) (x : World)
    (φ : Formula Atom Agent) : Prop :=
  M.Satisfies x φ ↔ (M.Satisfies x φ ∧ ¬ Common M x φ)

/-- The generalized self-fulfilling fixed-point view. -/
def SelfFulfillingFixedPoint (M : Model World Atom Agent) (x : World)
    (φ : Formula Atom Agent) : Prop :=
  M.Satisfies x φ ↔ (M.Satisfies x φ ∨ Common M x φ)

theorem common_implies_false_iff_mooreFixedPoint (M : Model World Atom Agent)
    (x : World) (φ : Formula Atom Agent) :
    (Common M x φ → ¬ M.Satisfies x φ) ↔ MooreFixedPoint M x φ := by
  constructor
  · intro h
    exact ⟨fun hp => ⟨hp, fun hc => h hc hp⟩, And.left⟩
  · intro h hc hp
    exact (h.mp hp).2 hc

theorem common_implies_true_iff_selfFulfillingFixedPoint (M : Model World Atom Agent)
    (x : World) (φ : Formula Atom Agent) :
    (Common M x φ → M.Satisfies x φ) ↔ SelfFulfillingFixedPoint M x φ := by
  constructor
  · intro h
    exact ⟨Or.inl, fun hp => hp.elim id h⟩
  · intro h hc
    exact h.mpr (Or.inr hc)

/-- The target bit selects the fixed-point form used in the manuscript. -/
def FixedPointView (j : Bool) (M : Model World Atom Agent) (x : World)
    (φ : Formula Atom Agent) : Prop :=
  if j then SelfFulfillingFixedPoint M x φ else MooreFixedPoint M x φ

theorem common_imp_holdsBit_iff_fixedPointView (j : Bool)
    (M : Model World Atom Agent) (x : World) (φ : Formula Atom Agent) :
    (Common M x φ → HoldsBit j (M.Satisfies x φ)) ↔ FixedPointView j M x φ := by
  cases j
  · exact common_implies_false_iff_mooreFixedPoint M x φ
  · exact common_implies_true_iff_selfFulfillingFixedPoint M x φ

theorem stageCondition_iff_fixedPointView (i j : Bool) (k : Nat)
    (φ : Formula Atom Agent) :
    StageCondition.{u} i j k φ ↔
      ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
        HoldsBit i (M.Satisfies x φ) → FixedPointView j (M.iterateUpdate φ k) x φ := by
  constructor
  · intro h W M hM x hx
    exact (common_imp_holdsBit_iff_fixedPointView j (M.iterateUpdate φ k) x φ).mp
      (h M hM x hx)
  · intro h W M hM x hx
    exact (common_imp_holdsBit_iff_fixedPointView j (M.iterateUpdate φ k) x φ).mpr
      (h M hM x hx)

theorem finiteStageCondition_iff_fixedPointView (i j : Bool) (φ : Formula Atom Agent) :
    FiniteStageCondition.{u} i j φ ↔
      ∀ k, ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
        HoldsBit i (M.Satisfies x φ) → FixedPointView j (M.iterateUpdate φ k) x φ :=
  forall_congr' fun k => stageCondition_iff_fixedPointView i j k φ

theorem ordinalStageCondition_iff_fixedPointView (i j : Bool) (φ : Formula Atom Agent) :
    OrdinalStageCondition.{u} i j φ ↔
      ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
        HoldsBit i (M.Satisfies x φ) → ∀ α : Ordinal.{max u w},
          FixedPointView j (ordinalUpdate M φ α) x φ := by
  constructor
  · intro h W M hM x hx α
    exact (common_imp_holdsBit_iff_fixedPointView j (ordinalUpdate M φ α) x φ).mp
      (h M hM x hx α)
  · intro h W M hM x hx α
    exact (common_imp_holdsBit_iff_fixedPointView j (ordinalUpdate M φ α) x φ).mpr
      (h M hM x hx α)

theorem alwaysInformative_iff_fixedPointView (i : Bool) (φ : Formula Atom Agent) :
    AlwaysInformative.{u} i φ ↔
      ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
        FixedPointView (!i) M x φ := by
  rw [alwaysInformative_iff]
  constructor
  · intro h W M hM x
    exact (common_imp_holdsBit_iff_fixedPointView (!i) M x φ).mp (h M hM x)
  · intro h W M hM x
    exact (common_imp_holdsBit_iff_fixedPointView (!i) M x φ).mpr (h M hM x)

section FiniteFormulas

variable {A G : Type} [Inhabited A]

/-- The finite disjunction over positive stages 1,...,N in Theorem 13. -/
def finiteHittingFormula (φ : Formula A G) (j : Bool) (N : Nat) : Formula A G :=
  Formula.disjList ((List.range N).map fun k =>
    signedFormula j (Formula.iteratedAnnouncementReduce φ (k + 1) φ))

theorem satisfies_finiteHittingFormula (M : Model World A G) (x : World)
    (φ : Formula A G) (j : Bool) (N : Nat) :
    M.Satisfies x (finiteHittingFormula φ j N) ↔
      ∃ n : Nat, 1 ≤ n ∧ n ≤ N ∧ HoldsBit j (M.trace x φ n) := by
  rw [finiteHittingFormula, Model.satisfies_disjList]
  constructor
  · rintro ⟨ψ, hψ, hsat⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hψ
    have hkN := List.mem_range.mp hk
    refine ⟨k + 1, by omega, by omega, ?_⟩
    have hv := (satisfies_signedFormula M x j _).mp hsat
    exact (holdsBit_congr j (M.trace_iff_satisfies_iteratedAnnouncementReduce x φ (k + 1))).mpr hv
  · rintro ⟨n, hn, hnN, hv⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine ⟨signedFormula j (Formula.iteratedAnnouncementReduce φ (k + 1) φ), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩
    · apply (satisfies_signedFormula M x j _).mpr
      exact (holdsBit_congr j (M.trace_iff_satisfies_iteratedAnnouncementReduce x φ (k + 1))).mp hv

/-- Exact syntactic validity form of the uniform-bound condition. -/
theorem uniformBound_iff_finiteDisjunction (i j : Bool) (φ : Formula A G) :
    UniformBound.{u} i j φ ↔
      ∃ N : Nat, 1 ≤ N ∧
        ∀ {W : Type u} (M : Model W A G), IsK45 M → ∀ x,
          M.Satisfies x (Formula.imp (signedFormula i φ) (finiteHittingFormula φ j N)) := by
  simp only [UniformBound, Model.satisfies_imp, satisfies_signedFormula,
    satisfies_finiteHittingFormula]

/-- Exact syntactic form of the true-lie bound without an initial precondition. -/
theorem unconditionalUniformBound_iff_finiteDisjunction (j : Bool) (φ : Formula A G) :
    UnconditionalUniformBound.{u} j φ ↔
      ∃ N : Nat, 1 ≤ N ∧
        ∀ {W : Type u} (M : Model W A G), IsK45 M → ∀ x,
          M.Satisfies x (finiteHittingFormula φ j N) := by
  simp only [UnconditionalUniformBound, satisfies_finiteHittingFormula]

/-- The finite conjunction of all agents' beliefs in contradiction. -/
noncomputable def beliefInconsistency [Fintype G] : Formula A G :=
  Formula.conjList (Finset.univ.toList.map fun a => .box a Formula.falsum)

theorem satisfies_beliefInconsistency [Fintype G] (M : Model World A G) (x : World) :
    M.Satisfies x (beliefInconsistency (A := A) (G := G)) ↔
      ∀ a y, ¬ M.rel a x y := by
  classical
  simp [beliefInconsistency, Model.satisfies_conjList, Model.satisfies_box]

/-- Exact announced modal formula in the uniform extinction characterization. -/
theorem uniformExtinction_iff_announced_formula [Fintype G] (φ : Formula A G) :
    UniformExtinction.{u} φ ↔
      ∃ N : Nat, 1 ≤ N ∧
        ∀ {W : Type u} (M : Model W A G), IsK45 M → ∀ x,
          M.Satisfies x (Formula.iteratedAnnouncementReduce φ N
            (.conj (.neg φ) beliefInconsistency)) := by
  constructor
  · rintro ⟨N, hN, h⟩
    refine ⟨N, hN, ?_⟩
    intro W M hM x
    apply (M.satisfies_iteratedAnnouncementReduce x φ _ N).mp
    exact ⟨(h M hM).1 x,
      (satisfies_beliefInconsistency (M.iterateUpdate φ N) x).mpr
        (fun a y => (h M hM).2 a x y)⟩
  · rintro ⟨N, hN, h⟩
    refine ⟨N, hN, ?_⟩
    intro W M hM
    have hs (x : W) := (M.satisfies_iteratedAnnouncementReduce x φ _ N).mpr (h M hM x)
    exact ⟨fun x => (hs x).1,
      fun a x y => (satisfies_beliefInconsistency (M.iterateUpdate φ N) x).mp (hs x).2 a y⟩

end FiniteFormulas

end EventualAndStrongEventualNotionsInPublicAnnouncements
