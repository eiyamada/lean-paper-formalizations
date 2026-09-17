import EventualAndStrongEventualNotionsInPublicAnnouncements.RichExtension

/-!
# Classification in the languages with common belief

Remark `rem:extension-to-richer-languages`: finite trace characterizations and
all ordinal implications survive for arbitrary nesting of common belief and
announcements. Uniform bounds remain sufficient. Compactness equivalences and
finite eventual self-refutation implying its strong version are recovered here
only in the single-agent case, through elimination to the basic language.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements.Rich

open ClassificationSigmaValidity
open Filter
open scoped Topology

variable {Atom Agent : Type} (φ : BPALCFormula Atom Agent)

theorem finite_classification_implications (i j : Bool) :
    (UniformBound.{0} i j φ → Eventual.{0} i j φ) ∧
    (StrongEventual.{0} i j φ → Eventual.{0} i j φ) ∧
    (Eventual.{0} i j φ → FiniteStageCondition.{0} i j φ) :=
  ⟨uniformBound_implies_eventual, strongEventual_implies_eventual,
    eventual_implies_finiteStageCondition⟩

/-- The self-refutation chain asserted for the noncompact languages. -/
theorem self_refutation_implications :
    (UniformExtinction.{0} φ → StrongEventual.{0} true false φ) ∧
    (StrongEventual.{0} true false φ → Eventual.{0} true false φ) :=
  ⟨uniformExtinction_implies_strongEventual, strongEventual_implies_eventual⟩

theorem eventual_reversal_implies_alwaysInformative (i : Bool)
    (h : Eventual.{0} i (!i) φ) : AlwaysInformative.{0} i φ :=
  (alwaysInformative_iff_finiteStageCondition i φ).mpr
    (eventual_implies_finiteStageCondition h)

theorem strongEventual_iff_conditional_real_limit (i j : Bool) :
    StrongEventual.{0} i j φ ↔
      ∀ {W : Type} (M : Model W Atom Agent), IsK45 M → ∀ x,
        HoldsBit i (M.rSatisfies x φ) →
          Tendsto (realTrace (M.rTrace x φ)) atTop (𝓝 (if j then 1 else 0)) := by
  simp_rw [← convergesTo_iff_real_limit]
  exact strongEventual_iff_conditional_convergence

theorem eventual_success_iff_real_limsup :
    Eventual.{0} true true φ ↔
      ∀ {W : Type} (M : Model W Atom Agent), IsK45 M → ∀ x,
        M.rSatisfies x φ → limsup (realTrace (M.rTrace x φ)) atTop = 1 := by
  simp_rw [← cofinal_true_iff_real_limsup]
  exact eventual_same_iff_cofinal

theorem eventual_impossible_lie_iff_real_liminf :
    Eventual.{0} false false φ ↔
      ∀ {W : Type} (M : Model W Atom Agent), IsK45 M → ∀ x,
        ¬ M.rSatisfies x φ → liminf (realTrace (M.rTrace x φ)) atTop = 0 := by
  simp_rw [← cofinal_false_iff_real_liminf]
  exact eventual_same_iff_cofinal

theorem eventual_true_lie_iff_real_limsup :
    Eventual.{0} false true φ ↔
      ∀ {W : Type} (M : Model W Atom Agent), IsK45 M → ∀ x,
        limsup (realTrace (M.rTrace x φ)) atTop = 1 := by
  simp_rw [← cofinal_true_iff_real_limsup]
  exact eventual_true_lie_iff_cofinal_true

theorem eventual_self_refuting_iff_real_liminf :
    Eventual.{0} true false φ ↔
      ∀ {W : Type} (M : Model W Atom Agent), IsK45 M → ∀ x,
        liminf (realTrace (M.rTrace x φ)) atTop = 0 := by
  simp_rw [← cofinal_false_iff_real_liminf]
  exact eventual_self_refuting_iff_cofinal_false

theorem strongEventual_self_refuting_iff_real_limit :
    StrongEventual.{0} true false φ ↔
      ∀ {W : Type} (M : Model W Atom Agent), IsK45 M → ∀ x,
        Tendsto (realTrace (M.rTrace x φ)) atTop (𝓝 0) := by
  have hlim (t : Nat → Prop) : ConvergesTo false t ↔
      Tendsto (realTrace t) atTop (𝓝 0) := by
    simpa using convergesTo_iff_real_limit false t
  simp_rw [← hlim]
  exact strongEventual_self_refuting_iff_convergence_false

theorem strongEventual_true_lie_iff_real_limit :
    StrongEventual.{0} false true φ ↔
      ∀ {W : Type} (M : Model W Atom Agent), IsK45 M → ∀ x,
        Tendsto (realTrace (M.rTrace x φ)) atTop (𝓝 1) := by
  have hlim (t : Nat → Prop) : ConvergesTo true t ↔
      Tendsto (realTrace t) atTop (𝓝 1) := by
    simpa using convergesTo_iff_real_limit true t
  simp_rw [← hlim]
  exact strongEventual_true_lie_iff_convergence_true

/-- The common ordinal implication chain holds for all four pairs. -/
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

theorem classification_reversals (i : Bool) :
    (OrdinalEventual.{0} i (!i) φ ↔ OrdinalStrongEventual.{0} i (!i) φ) ∧
    (OrdinalStrongEventual.{0} i (!i) φ ↔ OrdinalStageCondition.{0} i (!i) φ) ∧
    (OrdinalStageCondition.{0} i (!i) φ ↔ FiniteStageCondition.{0} i (!i) φ) :=
  ordinal_reversal_equivalences

/-- With one agent, common belief and nested announcements eliminate to a
basic modal formula, so all six notions coincide. -/
theorem singleAgent_classification [Nonempty Agent] [Subsingleton Agent] (i j : Bool) :
    (StrongEventual.{0} i j φ ↔ Eventual.{0} i j φ) ∧
    (Eventual.{0} i j φ ↔ OrdinalEventual.{0} i j φ) ∧
    (OrdinalEventual.{0} i j φ ↔ FiniteStageCondition.{0} i j φ) ∧
    (FiniteStageCondition.{0} i j φ ↔ OrdinalStrongEventual.{0} i j φ) ∧
    (OrdinalStrongEventual.{0} i j φ ↔ OrdinalStageCondition.{0} i j φ) := by
  classical
  let a : Agent := Classical.choice inferInstance
  have h : Equivalent.{0} φ (φ.toFormula a) := singleAgent_equivalent a φ
  simp only [equivalent_strongEventual h i j, equivalent_eventual h i j,
    equivalent_ordinalEventual h i j, equivalent_finiteStageCondition h i j,
    equivalent_ordinalStrongEventual h i j, equivalent_ordinalStageCondition h i j]
  exact EventualAndStrongEventualNotionsInPublicAnnouncements.singleAgent_classification
    (φ.toFormula a) i j

/-- The single-agent elimination also recovers uniform finite bounds. -/
theorem singleAgent_eventual_iff_uniformBound [Nonempty Agent] [Subsingleton Agent]
    (i j : Bool) : Eventual.{0} i j φ ↔ UniformBound.{0} i j φ := by
  classical
  let a : Agent := Classical.choice inferInstance
  have h : Equivalent.{0} φ (φ.toFormula a) := singleAgent_equivalent a φ
  exact (equivalent_eventual h i j).trans
    ((EventualAndStrongEventualNotionsInPublicAnnouncements.eventual_iff_uniformBound
      i j (φ.toFormula a)).trans (equivalent_uniformBound h i j).symm)

theorem singleAgent_eventual_self_refuting_iff_extinction
    [Nonempty Agent] [Subsingleton Agent] :
    Eventual.{0} true false φ ↔ UniformExtinction.{0} φ :=
  (singleAgent_eventual_iff_uniformBound φ true false).trans
    uniformBound_self_refuting_iff_extinction

theorem singleAgent_eventual_self_refuting_iff_strongEventual
    [Nonempty Agent] [Subsingleton Agent] :
    Eventual.{0} true false φ ↔ StrongEventual.{0} true false φ :=
  ((singleAgent_classification φ true false).1).symm

theorem singleAgent_eventual_true_lie_iff_unconditional_bound
    [Nonempty Agent] [Subsingleton Agent] :
    Eventual.{0} false true φ ↔ UnconditionalUniformBound.{0} true φ :=
  (singleAgent_eventual_iff_uniformBound φ false true).trans
    (uniformBound_reversal_iff_unconditional (j := true) (φ := φ))

end EventualAndStrongEventualNotionsInPublicAnnouncements.Rich
