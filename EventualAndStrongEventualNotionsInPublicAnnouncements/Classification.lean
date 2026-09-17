import EventualAndStrongEventualNotionsInPublicAnnouncements.Strictness
import EventualAndStrongEventualNotionsInPublicAnnouncements.Renaming
import EventualAndStrongEventualNotionsInPublicAnnouncements.Oscillation
import EventualAndStrongEventualNotionsInPublicAnnouncements.FalseOscillation
import EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalReturn
import EventualAndStrongEventualNotionsInPublicAnnouncements.TruePreservationCountermodels
import EventualAndStrongEventualNotionsInPublicAnnouncements.FalsePreservationCountermodels
import EventualAndStrongEventualNotionsInPublicAnnouncements.ReversalSeparations

/-! Concrete strictness results for every agent type with two distinct members. -/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity

variable {Agent : Type} (a b : Agent) (hab : a ≠ b)

def twoAgentMap (a b : Agent) : Bool → Agent
  | false => a
  | true => b

include a b hab

theorem twoAgentMap_injective : Function.Injective (twoAgentMap a b) := by
  intro x y h
  cases x <;> cases y <;> simp_all [twoAgentMap]

theorem true_oscillation_witnesses :
    ∃ φ : Formula Nat Agent,
      (Eventual.{0} true true φ ∧ ¬ StrongEventual.{0} true true φ) ∧
      (Eventual.{0} false true φ ∧ ¬ StrongEventual.{0} false true φ) := by
  letI : Nonempty Agent := ⟨a⟩
  obtain ⟨φ, h₁, h₀⟩ := Oscillation.lemma8 a b hab
  have e₁ := renaming_condition_equivalences (fun p : Fin 5 => p.val) (id : Agent → Agent)
    Fin.val_injective Function.injective_id true true φ
  have e₀ := renaming_condition_equivalences (fun p : Fin 5 => p.val) (id : Agent → Agent)
    Fin.val_injective Function.injective_id false true φ
  exact ⟨φ.map Fin.val id, ⟨e₁.1.mpr h₁.1, fun h => h₁.2 (e₁.2.1.mp h)⟩,
    ⟨e₀.1.mpr h₀.1, fun h => h₀.2 (e₀.2.1.mp h)⟩⟩

theorem false_oscillation_witness :
    ∃ φ : Formula Nat Agent, Eventual.{0} false false φ ∧
      ¬ StrongEventual.{0} false false φ := by
  obtain ⟨φ, he, hn⟩ := FalseOscillation.impossible_lie_separation
  have e := renaming_condition_equivalences (id : Nat → Nat) (twoAgentMap a b)
    Function.injective_id (twoAgentMap_injective a b hab) false false φ
  exact ⟨φ.map id (twoAgentMap a b), e.1.mpr he, fun h => hn (e.2.1.mp h)⟩

theorem ordinal_return_witnesses :
    (∃ φ : Formula Nat Agent, OrdinalStrongEventual.{0} true true φ ∧
      ¬ Eventual.{0} true true φ) ∧
    (∃ φ : Formula Nat Agent, OrdinalStrongEventual.{0} false false φ ∧
      ¬ Eventual.{0} false false φ) := by
  obtain ⟨h₁, h₀⟩ := OrdinalReturn.ordinal_return_separations
  constructor
  · obtain ⟨φ, he, hn⟩ := h₁
    have e := renaming_condition_equivalences (id : Nat → Nat) (twoAgentMap a b)
      Function.injective_id (twoAgentMap_injective a b hab) true true φ
    exact ⟨φ.map id (twoAgentMap a b), e.2.2.2.2.1.mpr he, fun h => hn (e.1.mp h)⟩
  · obtain ⟨φ, he, hn⟩ := h₀
    have e := renaming_condition_equivalences (id : Nat → Nat) (twoAgentMap a b)
      Function.injective_id (twoAgentMap_injective a b hab) false false φ
    exact ⟨φ.map id (twoAgentMap a b), e.2.2.2.2.1.mpr he, fun h => hn (e.1.mp h)⟩

theorem true_limit_loss_witnesses :
    (∃ φ : Formula Nat Agent, StrongEventual.{0} true true φ ∧
      ¬ OrdinalStrongEventual.{0} true true φ) ∧
    (∃ φ : Formula Nat Agent, FiniteStageCondition.{0} true true φ ∧
      ¬ OrdinalEventual.{0} true true φ) := by
  letI : Nonempty Agent := ⟨a⟩
  obtain ⟨h₁, h₂⟩ := TruePreservation.limit_loss_separations a b hab
  constructor
  · let φ := TruePreservation.strongFormula (0 : Fin 5) 1 3 a b
    have e := renaming_condition_equivalences (fun p : Fin 5 => p.val) (id : Agent → Agent)
      Fin.val_injective Function.injective_id true true φ
    exact ⟨φ.map Fin.val id, e.2.1.mpr h₁.1, fun h => h₁.2 (e.2.2.2.2.1.mp h)⟩
  · let φ := TruePreservation.stageFormula (0 : Fin 5) 1 3 4 a b
    have e := renaming_condition_equivalences (fun p : Fin 5 => p.val) (id : Agent → Agent)
      Fin.val_injective Function.injective_id true true φ
    exact ⟨φ.map Fin.val id, e.2.2.1.mpr h₂.1, fun h => h₂.2 (e.2.2.2.1.mp h)⟩

/-- The two loss-at-limit witnesses of Lemma 12. -/
theorem false_limit_loss_witnesses :
    (∃ φ : Formula Nat Agent, StrongEventual.{0} false false φ ∧
      ¬ OrdinalStrongEventual.{0} false false φ) ∧
    (∃ φ : Formula Nat Agent, FiniteStageCondition.{0} false false φ ∧
      ¬ OrdinalEventual.{0} false false φ) :=
  FalsePreservationCountermodels.lemma12 a b hab

/-- Theorems 13(1) and 14(1), all strict arrows and both incomparabilities. -/
theorem success_strict_classification : PreservationComparison Nat Agent true := by
  obtain ⟨φ, h₁, _⟩ := true_oscillation_witnesses a b hab
  exact preservation_strictness_of_witnesses true ⟨φ, h₁⟩
    (ordinal_return_witnesses a b hab).1
    (true_limit_loss_witnesses a b hab).1 (true_limit_loss_witnesses a b hab).2

/-- Theorems 13(4) and 14(4), all strict arrows and both incomparabilities. -/
theorem impossible_lie_strict_classification : PreservationComparison Nat Agent false := by
  exact preservation_strictness_of_witnesses false
    (false_oscillation_witness a b hab)
    (ordinal_return_witnesses a b hab).2
    (false_limit_loss_witnesses a b hab).1 (false_limit_loss_witnesses a b hab).2

/-- The strict finite/transfinite reversal arrows in Theorem 14(2),(3). -/
theorem reversal_strict_classification :
    StrictImplication (Eventual.{0} true false (Atom := Nat) (Agent := Agent))
      (OrdinalEventual.{0} true false) ∧
    StrictImplication (Eventual.{0} false true (Atom := Nat) (Agent := Agent))
      (OrdinalEventual.{0} false true) := by
  obtain ⟨h₁, h₀⟩ := ReversalSeparations.reversal_separations a b hab
  exact ⟨reversal_strictness_of_witness true h₁,
    reversal_strictness_of_witness false h₀⟩

/-- The strict strong/eventual true-lie arrow in both main theorems. -/
theorem true_lie_strong_strict :
    StrictImplication (StrongEventual.{0} false true (Atom := Nat) (Agent := Agent))
      (Eventual.{0} false true) := by
  obtain ⟨φ, _, h⟩ := true_oscillation_witnesses a b hab
  exact ⟨fun _ => strongEventual_implies_eventual, φ, h⟩

/-- The final strict arrow in each preservation item of Theorem 13. -/
theorem preservation_finite_stage_strict (i : Bool) :
    StrictImplication (Eventual.{0} i i (Atom := Nat) (Agent := Agent))
      (FiniteStageCondition.{0} i i) := by
  have hc : PreservationComparison Nat Agent i := by
    cases i
    · exact impossible_lie_strict_classification a b hab
    · exact success_strict_classification a b hab
  obtain ⟨φ, hstage, hnotOrdinal⟩ := hc.2.2.1.2
  exact ⟨fun _ => eventual_implies_finiteStageCondition, φ, hstage,
    fun he => hnotOrdinal (eventual_implies_ordinalEventual he)⟩

/-- The final strict arrows in the reversal items of Theorem 13. -/
theorem reversal_alwaysInformative_strict (i : Bool) :
    StrictImplication (Eventual.{0} i (!i) (Atom := Nat) (Agent := Agent))
      (AlwaysInformative.{0} i) := by
  have hw : ∃ φ : Formula Nat Agent, FiniteStageCondition.{0} i (!i) φ ∧
      ¬ Eventual.{0} i (!i) φ := by
    cases i
    · exact (ReversalSeparations.reversal_separations a b hab).2
    · exact (ReversalSeparations.reversal_separations a b hab).1
  obtain ⟨φ, hstage, hnot⟩ := hw
  exact ⟨fun ψ => eventual_reversal_implies_alwaysInformative ψ i, φ,
    (alwaysInformative_iff_finiteStageCondition i φ).mpr hstage, hnot⟩

/-- Every displayed strict arrow in Theorem 13, with actual modal witnesses. -/
theorem finite_classification_strictness :
    StrictImplication (StrongEventual.{0} true true (Atom := Nat) (Agent := Agent))
      (Eventual.{0} true true) ∧
    StrictImplication (Eventual.{0} true true (Atom := Nat) (Agent := Agent))
      (FiniteStageCondition.{0} true true) ∧
    StrictImplication (Eventual.{0} true false (Atom := Nat) (Agent := Agent))
      (AlwaysInformative.{0} true) ∧
    StrictImplication (StrongEventual.{0} false true (Atom := Nat) (Agent := Agent))
      (Eventual.{0} false true) ∧
    StrictImplication (Eventual.{0} false true (Atom := Nat) (Agent := Agent))
      (AlwaysInformative.{0} false) ∧
    StrictImplication (StrongEventual.{0} false false (Atom := Nat) (Agent := Agent))
      (Eventual.{0} false false) ∧
    StrictImplication (Eventual.{0} false false (Atom := Nat) (Agent := Agent))
      (FiniteStageCondition.{0} false false) :=
  ⟨(success_strict_classification a b hab).1,
    preservation_finite_stage_strict a b hab true,
    reversal_alwaysInformative_strict a b hab true,
    true_lie_strong_strict a b hab,
    reversal_alwaysInformative_strict a b hab false,
    (impossible_lie_strict_classification a b hab).1,
    preservation_finite_stage_strict a b hab false⟩

end EventualAndStrongEventualNotionsInPublicAnnouncements
