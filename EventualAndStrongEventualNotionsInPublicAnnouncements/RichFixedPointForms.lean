import EventualAndStrongEventualNotionsInPublicAnnouncements.RichOrdinalConditions

/-!
# Fixed-point views in the languages with common belief

The displayed Moore and self-fulfilling equations also characterize the finite
and ordinal stage conditions for arbitrary BPALC formulas, as used in Remark 1.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements.Rich

open ClassificationSigmaValidity

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- The generalized Moore fixed-point view. -/
def MooreFixedPoint (M : Model World Atom Agent) (x : World)
    (φ : BPALCFormula Atom Agent) : Prop :=
  M.rSatisfies x φ ↔ (M.rSatisfies x φ ∧ ¬ Common M x φ)

/-- The generalized self-fulfilling fixed-point view. -/
def SelfFulfillingFixedPoint (M : Model World Atom Agent) (x : World)
    (φ : BPALCFormula Atom Agent) : Prop :=
  M.rSatisfies x φ ↔ (M.rSatisfies x φ ∨ Common M x φ)

theorem common_implies_false_iff_mooreFixedPoint (M : Model World Atom Agent)
    (x : World) (φ : BPALCFormula Atom Agent) :
    (Common M x φ → ¬ M.rSatisfies x φ) ↔ MooreFixedPoint M x φ := by
  constructor
  · intro h
    exact ⟨fun hp => ⟨hp, fun hc => h hc hp⟩, And.left⟩
  · intro h hc hp
    exact (h.mp hp).2 hc

theorem common_implies_true_iff_selfFulfillingFixedPoint (M : Model World Atom Agent)
    (x : World) (φ : BPALCFormula Atom Agent) :
    (Common M x φ → M.rSatisfies x φ) ↔ SelfFulfillingFixedPoint M x φ := by
  constructor
  · intro h
    exact ⟨Or.inl, fun hp => hp.elim id h⟩
  · intro h hc
    exact h.mpr (Or.inr hc)

/-- The target bit selects the fixed-point form used in the manuscript. -/
def FixedPointView (j : Bool) (M : Model World Atom Agent) (x : World)
    (φ : BPALCFormula Atom Agent) : Prop :=
  if j then SelfFulfillingFixedPoint M x φ else MooreFixedPoint M x φ

theorem common_imp_holdsBit_iff_fixedPointView (j : Bool)
    (M : Model World Atom Agent) (x : World) (φ : BPALCFormula Atom Agent) :
    (Common M x φ → HoldsBit j (M.rSatisfies x φ)) ↔ FixedPointView j M x φ := by
  cases j
  · exact common_implies_false_iff_mooreFixedPoint M x φ
  · exact common_implies_true_iff_selfFulfillingFixedPoint M x φ

theorem stageCondition_iff_fixedPointView (i j : Bool) (k : Nat)
    (φ : BPALCFormula Atom Agent) :
    StageCondition.{u} i j k φ ↔
      ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
        HoldsBit i (M.rSatisfies x φ) → FixedPointView j (M.rIterateUpdate φ k) x φ := by
  constructor
  · intro h W M hM x hx
    exact (common_imp_holdsBit_iff_fixedPointView j (M.rIterateUpdate φ k) x φ).mp
      (h M hM x hx)
  · intro h W M hM x hx
    exact (common_imp_holdsBit_iff_fixedPointView j (M.rIterateUpdate φ k) x φ).mpr
      (h M hM x hx)

theorem finiteStageCondition_iff_fixedPointView (i j : Bool) (φ : BPALCFormula Atom Agent) :
    FiniteStageCondition.{u} i j φ ↔
      ∀ k, ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
        HoldsBit i (M.rSatisfies x φ) → FixedPointView j (M.rIterateUpdate φ k) x φ :=
  forall_congr' fun k => stageCondition_iff_fixedPointView i j k φ

theorem ordinalStageCondition_iff_fixedPointView (i j : Bool) (φ : BPALCFormula Atom Agent) :
    OrdinalStageCondition.{u} i j φ ↔
      ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
        HoldsBit i (M.rSatisfies x φ) → ∀ α : Ordinal.{max u w},
          FixedPointView j (ordinalUpdate M φ α) x φ := by
  constructor
  · intro h W M hM x hx α
    exact (common_imp_holdsBit_iff_fixedPointView j (ordinalUpdate M φ α) x φ).mp
      (h M hM x hx α)
  · intro h W M hM x hx α
    exact (common_imp_holdsBit_iff_fixedPointView j (ordinalUpdate M φ α) x φ).mpr
      (h M hM x hx α)

theorem alwaysInformative_iff_fixedPointView (i : Bool) (φ : BPALCFormula Atom Agent) :
    AlwaysInformative.{u} i φ ↔
      ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
        FixedPointView (!i) M x φ := by
  rw [alwaysInformative_iff]
  constructor
  · intro h W M hM x
    exact (common_imp_holdsBit_iff_fixedPointView (!i) M x φ).mp (h M hM x)
  · intro h W M hM x
    exact (common_imp_holdsBit_iff_fixedPointView (!i) M x φ).mpr (h M hM x)

end EventualAndStrongEventualNotionsInPublicAnnouncements.Rich
