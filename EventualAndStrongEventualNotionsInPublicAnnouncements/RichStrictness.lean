import EventualAndStrongEventualNotionsInPublicAnnouncements.Classification
import EventualAndStrongEventualNotionsInPublicAnnouncements.RichExtension

/-!
# Strictness in public-announcement logic with common belief

Every strict arrow and incomparability retains a basic epistemic witness under
the embedding into BPALC. The same witnesses also belong to the static language
with common belief. All forward implications quantify over the full language.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity

namespace CommonFormula

/-- Embed a basic modal formula in the static common-belief language. -/
def ofFormula {Atom Agent : Type*} : Formula Atom Agent → CommonFormula Atom Agent
  | .atom p => .atom p
  | .neg φ => .neg (ofFormula φ)
  | .conj φ ψ => .conj (ofFormula φ) (ofFormula ψ)
  | .box a φ => .box a (ofFormula φ)

@[simp] theorem toBPALC_ofFormula {Atom Agent : Type*} (φ : Formula Atom Agent) :
    (ofFormula φ).toBPALC = BPALCFormula.ofFormula φ := by
  induction φ with
  | atom p => rfl
  | neg φ ih => simp only [ofFormula, toBPALC, BPALCFormula.ofFormula, ih]
  | conj φ ψ ihφ ihψ => simp only [ofFormula, toBPALC, BPALCFormula.ofFormula, ihφ, ihψ]
  | box a φ ih => simp only [ofFormula, toBPALC, BPALCFormula.ofFormula, ih]

end CommonFormula

namespace Rich

/-- A strict implication transports when the target implication is valid
throughout the larger language and both predicates agree on embedded formulas. -/
theorem transport_strict {α β : Type*} (f : α → β)
    {P Q : α → Prop} {R S : β → Prop}
    (hR : ∀ x, R (f x) ↔ P x) (hS : ∀ x, S (f x) ↔ Q x)
    (hforward : ∀ y, R y → S y) (h : StrictImplication P Q) :
    StrictImplication R S := by
  obtain ⟨x, hxQ, hxP⟩ := h.2
  exact ⟨hforward, f x, (hS x).mpr hxQ, fun hr => hxP ((hR x).mp hr)⟩

/-- Incomparability transports through a truth-preserving embedding. -/
theorem transport_incomparable {α β : Type*} (f : α → β)
    {P Q : α → Prop} {R S : β → Prop}
    (hR : ∀ x, R (f x) ↔ P x) (hS : ∀ x, S (f x) ↔ Q x)
    (h : Incomparable P Q) : Incomparable R S := by
  obtain ⟨⟨x, hxP, hxQ⟩, y, hyQ, hyP⟩ := h
  exact ⟨⟨f x, (hR x).mpr hxP, fun hs => hxQ ((hS x).mp hs)⟩,
    f y, (hS y).mpr hyQ, fun hr => hyP ((hR y).mp hr)⟩

variable {Atom Agent : Type}

theorem ofFormula_eventual_iff (i j : Bool) (φ : Formula Atom Agent) :
    Eventual.{0} i j (BPALCFormula.ofFormula φ) ↔
      EventualAndStrongEventualNotionsInPublicAnnouncements.Eventual.{0} i j φ :=
  equivalent_eventual (ofFormula_equivalent φ) i j

theorem ofFormula_strongEventual_iff (i j : Bool) (φ : Formula Atom Agent) :
    StrongEventual.{0} i j (BPALCFormula.ofFormula φ) ↔
      EventualAndStrongEventualNotionsInPublicAnnouncements.StrongEventual.{0} i j φ :=
  equivalent_strongEventual (ofFormula_equivalent φ) i j

theorem ofFormula_finiteStageCondition_iff (i j : Bool) (φ : Formula Atom Agent) :
    FiniteStageCondition.{0} i j (BPALCFormula.ofFormula φ) ↔
      EventualAndStrongEventualNotionsInPublicAnnouncements.FiniteStageCondition.{0} i j φ :=
  equivalent_finiteStageCondition (ofFormula_equivalent φ) i j

theorem ofFormula_ordinalEventual_iff (i j : Bool) (φ : Formula Atom Agent) :
    OrdinalEventual.{0} i j (BPALCFormula.ofFormula φ) ↔
      EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalEventual.{0} i j φ :=
  equivalent_ordinalEventual (ofFormula_equivalent φ) i j

theorem ofFormula_ordinalStrongEventual_iff (i j : Bool) (φ : Formula Atom Agent) :
    OrdinalStrongEventual.{0} i j (BPALCFormula.ofFormula φ) ↔
      EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalStrongEventual.{0} i j φ :=
  equivalent_ordinalStrongEventual (ofFormula_equivalent φ) i j

theorem ofFormula_alwaysInformative_iff (i : Bool) (φ : Formula Atom Agent) :
    AlwaysInformative.{0} i (BPALCFormula.ofFormula φ) ↔
      EventualAndStrongEventualNotionsInPublicAnnouncements.AlwaysInformative.{0} i φ := by
  rw [alwaysInformative_iff_finiteStageCondition,
    EventualAndStrongEventualNotionsInPublicAnnouncements.alwaysInformative_iff_finiteStageCondition]
  exact ofFormula_finiteStageCondition_iff i (!i) φ

/-- All strict arrows and incomparabilities for a rich preservation pair. -/
def PreservationComparison (Atom Agent : Type) (i : Bool) : Prop :=
    StrictImplication (StrongEventual.{0} i i (Atom := Atom) (Agent := Agent)) (Eventual.{0} i i) ∧
    StrictImplication (Eventual.{0} i i (Atom := Atom) (Agent := Agent)) (OrdinalEventual.{0} i i) ∧
    StrictImplication (OrdinalEventual.{0} i i (Atom := Atom) (Agent := Agent)) (FiniteStageCondition.{0} i i) ∧
    StrictImplication (OrdinalStrongEventual.{0} i i (Atom := Atom) (Agent := Agent)) (OrdinalEventual.{0} i i) ∧
    Incomparable (Eventual.{0} i i (Atom := Atom) (Agent := Agent)) (OrdinalStrongEventual.{0} i i) ∧
    Incomparable (StrongEventual.{0} i i (Atom := Atom) (Agent := Agent)) (OrdinalStrongEventual.{0} i i)

/-- The complete preservation comparison transports from basic to rich formulas. -/
theorem preservationComparison_of_basic (i : Bool)
    (h : EventualAndStrongEventualNotionsInPublicAnnouncements.PreservationComparison Atom Agent i) :
    PreservationComparison Atom Agent i := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨
    transport_strict BPALCFormula.ofFormula (ofFormula_strongEventual_iff i i)
      (ofFormula_eventual_iff i i) (fun _ => strongEventual_implies_eventual) h₁,
    transport_strict BPALCFormula.ofFormula (ofFormula_eventual_iff i i)
      (ofFormula_ordinalEventual_iff i i) (fun _ => eventual_implies_ordinalEventual) h₂,
    transport_strict BPALCFormula.ofFormula (ofFormula_ordinalEventual_iff i i)
      (ofFormula_finiteStageCondition_iff i i) (fun _ => ordinalEventual_implies_finiteStageCondition) h₃,
    transport_strict BPALCFormula.ofFormula (ofFormula_ordinalStrongEventual_iff i i)
      (ofFormula_ordinalEventual_iff i i) (fun _ => ordinalStrongEventual_implies_ordinalEventual) h₄,
    transport_incomparable BPALCFormula.ofFormula (ofFormula_eventual_iff i i)
      (ofFormula_ordinalStrongEventual_iff i i) h₅,
    transport_incomparable BPALCFormula.ofFormula (ofFormula_strongEventual_iff i i)
      (ofFormula_ordinalStrongEventual_iff i i) h₆⟩

variable (a b : Agent) (hab : a ≠ b)
include a b hab

/-- Success preserves all strict arrows and both incomparabilities in BPALC. -/
theorem success_strict_classification : PreservationComparison Nat Agent true :=
  preservationComparison_of_basic true
    (EventualAndStrongEventualNotionsInPublicAnnouncements.success_strict_classification a b hab)

/-- Impossible lies preserve all strict arrows and both incomparabilities in BPALC. -/
theorem impossible_lie_strict_classification : PreservationComparison Nat Agent false :=
  preservationComparison_of_basic false
    (EventualAndStrongEventualNotionsInPublicAnnouncements.impossible_lie_strict_classification a b hab)

/-- The two finite/ordinal reversal implications remain strict in BPALC. -/
theorem reversal_strict_classification :
    StrictImplication (Eventual.{0} true false (Atom := Nat) (Agent := Agent))
      (OrdinalEventual.{0} true false) ∧
    StrictImplication (Eventual.{0} false true (Atom := Nat) (Agent := Agent))
      (OrdinalEventual.{0} false true) := by
  obtain ⟨h₁, h₀⟩ :=
    EventualAndStrongEventualNotionsInPublicAnnouncements.reversal_strict_classification a b hab
  exact ⟨transport_strict BPALCFormula.ofFormula (ofFormula_eventual_iff true false)
    (ofFormula_ordinalEventual_iff true false) (fun _ => eventual_implies_ordinalEventual) h₁,
    transport_strict BPALCFormula.ofFormula (ofFormula_eventual_iff false true)
    (ofFormula_ordinalEventual_iff false true) (fun _ => eventual_implies_ordinalEventual) h₀⟩

/-- The strong/eventual true-lie implication remains strict in BPALC. -/
theorem true_lie_strong_strict :
    StrictImplication (StrongEventual.{0} false true (Atom := Nat) (Agent := Agent))
      (Eventual.{0} false true) :=
  transport_strict BPALCFormula.ofFormula (ofFormula_strongEventual_iff false true)
    (ofFormula_eventual_iff false true) (fun _ => strongEventual_implies_eventual)
    (EventualAndStrongEventualNotionsInPublicAnnouncements.true_lie_strong_strict a b hab)

theorem preservation_finite_stage_strict (i : Bool) :
    StrictImplication (Eventual.{0} i i (Atom := Nat) (Agent := Agent))
      (FiniteStageCondition.{0} i i) :=
  transport_strict BPALCFormula.ofFormula (ofFormula_eventual_iff i i)
    (ofFormula_finiteStageCondition_iff i i)
    (fun _ h => ordinalEventual_implies_finiteStageCondition (eventual_implies_ordinalEventual h))
    (EventualAndStrongEventualNotionsInPublicAnnouncements.preservation_finite_stage_strict a b hab i)

theorem reversal_alwaysInformative_strict (i : Bool) :
    StrictImplication (Eventual.{0} i (!i) (Atom := Nat) (Agent := Agent))
      (AlwaysInformative.{0} i) :=
  transport_strict BPALCFormula.ofFormula (ofFormula_eventual_iff i (!i))
    (ofFormula_alwaysInformative_iff i)
    (fun φ h => (alwaysInformative_iff_finiteStageCondition i φ).mpr
      (ordinalEventual_implies_finiteStageCondition (eventual_implies_ordinalEventual h)))
    (EventualAndStrongEventualNotionsInPublicAnnouncements.reversal_alwaysInformative_strict a b hab i)

/-- All seven strict arrows in the finite classification, for BPALC formulas. -/
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

omit a b hab

/-- The same embedded witnesses lie in the static common-belief sublanguage.
This transports any basic strict pair whose forward implication holds in BPALC. -/
theorem commonLanguage_strict_of_basic
    {P Q : Formula Atom Agent → Prop} {R S : BPALCFormula Atom Agent → Prop}
    (hR : ∀ φ, R (BPALCFormula.ofFormula φ) ↔ P φ)
    (hS : ∀ φ, S (BPALCFormula.ofFormula φ) ↔ Q φ)
    (hforward : ∀ φ, R φ → S φ) (h : StrictImplication P Q) :
    StrictImplication (fun φ : CommonFormula Atom Agent => R φ.toBPALC)
      (fun φ : CommonFormula Atom Agent => S φ.toBPALC) :=
  transport_strict CommonFormula.ofFormula
    (fun φ => by simpa only [CommonFormula.toBPALC_ofFormula] using hR φ)
    (fun φ => by simpa only [CommonFormula.toBPALC_ofFormula] using hS φ)
    (fun φ => hforward φ.toBPALC) h

/-- The incomparability witnesses also belong to the static common-belief language. -/
theorem commonLanguage_incomparable_of_basic
    {P Q : Formula Atom Agent → Prop} {R S : BPALCFormula Atom Agent → Prop}
    (hR : ∀ φ, R (BPALCFormula.ofFormula φ) ↔ P φ)
    (hS : ∀ φ, S (BPALCFormula.ofFormula φ) ↔ Q φ)
    (h : Incomparable P Q) :
    Incomparable (fun φ : CommonFormula Atom Agent => R φ.toBPALC)
      (fun φ : CommonFormula Atom Agent => S φ.toBPALC) :=
  transport_incomparable CommonFormula.ofFormula
    (fun φ => by simpa only [CommonFormula.toBPALC_ofFormula] using hR φ)
    (fun φ => by simpa only [CommonFormula.toBPALC_ofFormula] using hS φ) h

end Rich
end EventualAndStrongEventualNotionsInPublicAnnouncements
