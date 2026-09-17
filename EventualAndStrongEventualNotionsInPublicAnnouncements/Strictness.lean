import EventualAndStrongEventualNotionsInPublicAnnouncements.Main

/-! Logical assembly of the strict implications and incomparabilities. -/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity

variable {Atom Agent : Type}

def StrictImplication {α : Type*} (P Q : α → Prop) : Prop :=
  (∀ x, P x → Q x) ∧ ∃ x, Q x ∧ ¬ P x

def Incomparable {α : Type*} (P Q : α → Prop) : Prop :=
  (∃ x, P x ∧ ¬ Q x) ∧ (∃ x, Q x ∧ ¬ P x)

/-- All strict arrows and incomparabilities for a preservation pair. -/
def PreservationComparison (Atom Agent : Type) (i : Bool) : Prop :=
    StrictImplication (StrongEventual.{0} i i (Atom := Atom) (Agent := Agent)) (Eventual.{0} i i) ∧
    StrictImplication (Eventual.{0} i i (Atom := Atom) (Agent := Agent)) (OrdinalEventual.{0} i i) ∧
    StrictImplication (OrdinalEventual.{0} i i (Atom := Atom) (Agent := Agent)) (FiniteStageCondition.{0} i i) ∧
    StrictImplication (OrdinalStrongEventual.{0} i i (Atom := Atom) (Agent := Agent)) (OrdinalEventual.{0} i i) ∧
    Incomparable (Eventual.{0} i i (Atom := Atom) (Agent := Agent)) (OrdinalStrongEventual.{0} i i) ∧
    Incomparable (StrongEventual.{0} i i (Atom := Atom) (Agent := Agent)) (OrdinalStrongEventual.{0} i i)

/-- The four independent preservation witnesses entail all the displayed
strict arrows and both incomparabilities in Theorem 14(1) or 14(4). -/
theorem preservation_strictness_of_witnesses (i : Bool)
    (h₁ : ∃ φ : Formula Atom Agent, Eventual.{0} i i φ ∧ ¬ StrongEventual.{0} i i φ)
    (h₂ : ∃ φ : Formula Atom Agent, OrdinalStrongEventual.{0} i i φ ∧ ¬ Eventual.{0} i i φ)
    (h₃ : ∃ φ : Formula Atom Agent, StrongEventual.{0} i i φ ∧ ¬ OrdinalStrongEventual.{0} i i φ)
    (h₄ : ∃ φ : Formula Atom Agent, FiniteStageCondition.{0} i i φ ∧ ¬ OrdinalEventual.{0} i i φ) :
    StrictImplication (StrongEventual.{0} i i (Atom := Atom) (Agent := Agent)) (Eventual.{0} i i) ∧
    StrictImplication (Eventual.{0} i i (Atom := Atom) (Agent := Agent)) (OrdinalEventual.{0} i i) ∧
    StrictImplication (OrdinalEventual.{0} i i (Atom := Atom) (Agent := Agent)) (FiniteStageCondition.{0} i i) ∧
    StrictImplication (OrdinalStrongEventual.{0} i i (Atom := Atom) (Agent := Agent)) (OrdinalEventual.{0} i i) ∧
    Incomparable (Eventual.{0} i i (Atom := Atom) (Agent := Agent)) (OrdinalStrongEventual.{0} i i) ∧
    Incomparable (StrongEventual.{0} i i (Atom := Atom) (Agent := Agent)) (OrdinalStrongEventual.{0} i i) := by
  obtain ⟨φ₁, he₁, hn₁⟩ := h₁
  obtain ⟨φ₂, ho₂, hn₂⟩ := h₂
  obtain ⟨φ₃, hs₃, hn₃⟩ := h₃
  obtain ⟨φ₄, hf₄, hn₄⟩ := h₄
  have he₃ : Eventual.{0} i i φ₃ := strongEventual_implies_eventual hs₃
  refine ⟨⟨fun _ => strongEventual_implies_eventual, φ₁, he₁, hn₁⟩,
    ⟨fun _ => eventual_implies_ordinalEventual, φ₂,
      ordinalStrongEventual_implies_ordinalEventual ho₂, hn₂⟩,
    ⟨fun _ => ordinalEventual_implies_finiteStageCondition, φ₄, hf₄, hn₄⟩,
    ⟨fun _ => ordinalStrongEventual_implies_ordinalEventual, φ₃,
      eventual_implies_ordinalEventual he₃, hn₃⟩,
    ⟨⟨φ₃, he₃, hn₃⟩, φ₂, ho₂, hn₂⟩,
    ⟨⟨φ₃, hs₃, hn₃⟩, φ₂, ho₂, ?_⟩⟩
  exact fun h => hn₂ (strongEventual_implies_eventual h)

theorem reversal_strictness_of_witness (i : Bool)
    (h : ∃ φ : Formula Atom Agent,
      FiniteStageCondition.{0} i (!i) φ ∧ ¬ Eventual.{0} i (!i) φ) :
    StrictImplication (Eventual.{0} i (!i) (Atom := Atom) (Agent := Agent))
      (OrdinalEventual.{0} i (!i)) := by
  obtain ⟨φ, hs, hn⟩ := h
  exact ⟨fun _ => eventual_implies_ordinalEventual, φ,
    ordinalStrongEventual_implies_ordinalEventual
      (finiteStageCondition_reversal_implies_ordinalStrongEventual hs), hn⟩

end EventualAndStrongEventualNotionsInPublicAnnouncements
