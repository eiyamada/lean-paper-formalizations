import EventualAndStrongEventualNotionsInPublicAnnouncements.Compactness
import EventualAndStrongEventualNotionsInPublicAnnouncements.NumericTraces
import EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalConditions
import EventualAndStrongEventualNotionsInPublicAnnouncements.SingleAgent

/-!
# Main classification implications and equivalences

These declarations assemble the general parts of Theorems 13 and 14.
The strictness and incomparability statements require the separate explicit
two-agent constructions identified in the coverage map.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity
open Filter
open scoped Topology

variable {Atom Agent : Type} (φ : Formula Atom Agent)

/-- Theorem 13(2), including the exact uniform extinction condition. -/
theorem eventual_self_refuting_iff_extinction :
    Eventual.{0} true false φ ↔ UniformExtinction.{0} φ :=
  (eventual_iff_uniformBound true false φ).trans
    uniformBound_self_refuting_iff_extinction

theorem eventual_self_refuting_iff_strongEventual :
    Eventual.{0} true false φ ↔ StrongEventual.{0} true false φ :=
  ⟨fun h => uniformExtinction_implies_strongEventual
      ((eventual_self_refuting_iff_extinction φ).mp h),
    strongEventual_implies_eventual⟩

/-- The true-lie bound has no initial-value precondition. -/
theorem eventual_true_lie_iff_unconditional_bound :
    Eventual.{0} false true φ ↔ UnconditionalUniformBound.{0} true φ :=
  (eventual_iff_uniformBound false true φ).trans
    (uniformBound_reversal_iff_unconditional (j := true) (φ := φ))

theorem eventual_reversal_implies_alwaysInformative (i : Bool)
    (h : Eventual.{0} i (!i) φ) : AlwaysInformative.{0} i φ :=
  (alwaysInformative_iff_finiteStageCondition i φ).mpr
    (eventual_implies_finiteStageCondition h)

/-- The real limit characterization for both preservation cases. -/
theorem strongEventual_iff_conditional_real_limit (i j : Bool) :
    StrongEventual.{0} i j φ ↔
      ∀ {W : Type} (M : Model W Atom Agent), IsK45 M → ∀ x,
        HoldsBit i (M.Satisfies x φ) →
          Tendsto (realTrace (M.trace x φ)) atTop (𝓝 (if j then 1 else 0)) := by
  simp_rw [← convergesTo_iff_real_limit]
  exact strongEventual_iff_conditional_convergence

theorem eventual_success_iff_real_limsup :
    Eventual.{0} true true φ ↔
      ∀ {W : Type} (M : Model W Atom Agent), IsK45 M → ∀ x,
        M.Satisfies x φ → limsup (realTrace (M.trace x φ)) atTop = 1 := by
  simp_rw [← cofinal_true_iff_real_limsup]
  exact eventual_same_iff_cofinal

theorem eventual_impossible_lie_iff_real_liminf :
    Eventual.{0} false false φ ↔
      ∀ {W : Type} (M : Model W Atom Agent), IsK45 M → ∀ x,
        ¬ M.Satisfies x φ → liminf (realTrace (M.trace x φ)) atTop = 0 := by
  simp_rw [← cofinal_false_iff_real_liminf]
  exact eventual_same_iff_cofinal

theorem eventual_true_lie_iff_real_limsup :
    Eventual.{0} false true φ ↔
      ∀ {W : Type} (M : Model W Atom Agent), IsK45 M → ∀ x,
        limsup (realTrace (M.trace x φ)) atTop = 1 := by
  simp_rw [← cofinal_true_iff_real_limsup]
  exact eventual_true_lie_iff_cofinal_true

theorem eventual_self_refuting_iff_real_liminf :
    Eventual.{0} true false φ ↔
      ∀ {W : Type} (M : Model W Atom Agent), IsK45 M → ∀ x,
        liminf (realTrace (M.trace x φ)) atTop = 0 := by
  simp_rw [← cofinal_false_iff_real_liminf]
  exact eventual_self_refuting_iff_cofinal_false

theorem eventual_self_refuting_iff_real_limit :
    Eventual.{0} true false φ ↔
      ∀ {W : Type} (M : Model W Atom Agent), IsK45 M → ∀ x,
        Tendsto (realTrace (M.trace x φ)) atTop (𝓝 0) := by
  have hlim (t : Nat → Prop) : ConvergesTo false t ↔
      Tendsto (realTrace t) atTop (𝓝 0) := by
    simpa using convergesTo_iff_real_limit false t
  simp_rw [← hlim]
  exact (eventual_self_refuting_iff_strongEventual φ).trans
    strongEventual_self_refuting_iff_convergence_false

theorem strongEventual_true_lie_iff_real_limit :
    StrongEventual.{0} false true φ ↔
      ∀ {W : Type} (M : Model W Atom Agent), IsK45 M → ∀ x,
        Tendsto (realTrace (M.trace x φ)) atTop (𝓝 1) := by
  have hlim (t : Nat → Prop) : ConvergesTo true t ↔
      Tendsto (realTrace t) atTop (𝓝 1) := by
    simpa using convergesTo_iff_real_limit true t
  simp_rw [← hlim]
  exact strongEventual_true_lie_iff_convergence_true

/-- Theorem 14: the common implication chain for all four pairs. -/
theorem classification_implications (i j : Bool) :
    (StrongEventual.{0} i j φ → Eventual.{0} i j φ) ∧
    (Eventual.{0} i j φ → OrdinalEventual.{0} i j φ) ∧
    (OrdinalEventual.{0} i j φ → FiniteStageCondition.{0} i j φ) ∧
    (OrdinalStageCondition.{0} i j φ ↔ OrdinalStrongEventual.{0} i j φ) ∧
    (OrdinalStrongEventual.{0} i j φ → OrdinalEventual.{0} i j φ) :=
  ⟨strongEventual_implies_eventual, eventual_implies_ordinalEventual,
    ordinalEventual_implies_finiteStageCondition,
    ordinalStageCondition_iff_ordinalStrongEventual,
    ordinalStrongEventual_implies_ordinalEventual⟩

/-- The single-agent collapse in both main theorems. -/
theorem singleAgent_classification [Nonempty Agent] [Subsingleton Agent] (i j : Bool) :
    (StrongEventual.{0} i j φ ↔ Eventual.{0} i j φ) ∧
    (Eventual.{0} i j φ ↔ OrdinalEventual.{0} i j φ) ∧
    (OrdinalEventual.{0} i j φ ↔ FiniteStageCondition.{0} i j φ) ∧
    (FiniteStageCondition.{0} i j φ ↔ OrdinalStrongEventual.{0} i j φ) ∧
    (OrdinalStrongEventual.{0} i j φ ↔ OrdinalStageCondition.{0} i j φ) := by
  have hfin : FiniteStageCondition.{0} i j φ → StrongEventual.{0} i j φ :=
    singleAgent_finiteStageCondition_implies_strongEventual i j φ
  have hord : FiniteStageCondition.{0} i j φ → OrdinalStrongEventual.{0} i j φ := by
    intro h W M hM x hx
    obtain ⟨N, hN, hC⟩ := singleAgent_exists_positive_common M hM φ x
    refine ⟨(N : Ordinal), by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN), ?_⟩
    intro β hβ
    have hC' : Common (ordinalUpdate M φ (N : Ordinal)) x φ := by simpa using hC
    have hv := h N M hM x hx hC
    exact (holdsBit_congr j (common_ordinal_stage_permanent M φ hC' hβ φ)).mpr
      (by simpa [Model.trace] using hv)
  refine ⟨⟨strongEventual_implies_eventual,
    fun h => hfin (eventual_implies_finiteStageCondition h)⟩,
    ⟨eventual_implies_ordinalEventual, fun h => strongEventual_implies_eventual
      (hfin (ordinalEventual_implies_finiteStageCondition h))⟩,
    ⟨ordinalEventual_implies_finiteStageCondition, fun h =>
      eventual_implies_ordinalEventual (strongEventual_implies_eventual (hfin h))⟩,
    ⟨hord, fun h => ordinalStageCondition_implies_finiteStageCondition
      (ordinalStageCondition_iff_ordinalStrongEventual.mpr h)⟩,
    ordinalStageCondition_iff_ordinalStrongEventual.symm⟩

end EventualAndStrongEventualNotionsInPublicAnnouncements
