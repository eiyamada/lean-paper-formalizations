import PropertiesOfPublicAnnouncementsAsOperators.ModalPreservation
import PropertiesOfPublicAnnouncementsAsOperators.FragmentDuality
import PropertiesOfPublicAnnouncementsAsOperators.GeneralSubmodels
import PropertiesOfPublicAnnouncementsAsOperators.OperatorCharacterizations

/-! # Theorem 19: the two eight-way characterizations -/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity

universe u v w

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- Monotonicity of a PAL operator between arbitrary induced domains. -/
def PALOperatorMonotone (φ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent) (S T : Set World),
    S ⊆ T → palUpdate M φ.toPAL S ⊆ palUpdate M φ.toPAL T

theorem domainModel_eq_targetCut (M : Model World Atom Agent) (S : Set World) :
    PAL.domainModel M S = targetCut M S := by
  apply Model.ext'
  · intro i x y
    exact and_comm
  · intro p x
    rfl

theorem palOperatorMonotone_iff_deletionAntimonotone (φ : Formula Atom Agent) :
    PALOperatorMonotone.{u} φ ↔ DeletionAntimonotone.{u} φ := by
  constructor
  · intro h
    apply (deletionAntimonotone_iff_extensionPreserved φ).mpr
    intro W M S x hx
    have hcut := (targetCut_satisfies_restrict M S x φ).mpr hx
    have hpal : PAL.Satisfies M S x.val φ.toPAL := by
      rw [PAL.satisfies_toPAL,domainModel_eq_targetCut]
      exact hcut
    have hret := h M S Set.univ (Set.subset_univ S) ⟨x.property,hpal⟩
    have hsat := (PAL.satisfies_toPAL M Set.univ x.val φ).mp hret.2
    rw [show PAL.domainModel M Set.univ = M from PAL.domainModel_true M] at hsat
    exact hsat
  · intro h W M S T hST
    exact palUpdate_monotone M φ h hST

theorem pal_neg_operatorMonotone_iff_deletionMonotone (φ : Formula Atom Agent) :
    PALOperatorMonotone.{u} (.neg φ) ↔ DeletionMonotone.{u} φ :=
  (palOperatorMonotone_iff_deletionAntimonotone (.neg φ)).trans
    (deletionAntimonotone_neg_iff φ)

def AnnouncementReflected (φ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent) (ψ : Formula Atom Agent) x,
    M.Satisfies x ψ → (M.update ψ).Satisfies x φ → M.Satisfies x φ

def BPALAnnouncementReflected (φ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent) (ψ : Formula Atom Agent) x,
    (M.update ψ).Satisfies x φ → M.Satisfies x φ

theorem announcementPreserved_neg_iff_reflected (φ : Formula Atom Agent) :
    AnnouncementPreserved.{u} (.neg φ) ↔ AnnouncementReflected.{u} φ := by
  classical
  constructor
  · intro h W M ψ x hψ hφ
    by_contra hn
    exact h M ψ x hn hψ hφ
  · intro h W M ψ x hn hψ hφ
    exact hn (h M ψ x hψ hφ)

theorem bpalAnnouncementPreserved_neg_iff_reflected (φ : Formula Atom Agent) :
    BPALAnnouncementPreserved.{u} (.neg φ) ↔ BPALAnnouncementReflected.{u} φ := by
  classical
  constructor
  · intro h W M ψ x hφ
    by_contra hn
    exact h M ψ x hn hφ
  · intro h W M ψ x hn hφ
    exact hn (h M ψ x hφ)

section Main

variable {Atom Agent : Type} [Inhabited Atom]

theorem deletionAntimonotone_iff_existentialEquivalent (φ : Formula Atom Agent) :
    DeletionAntimonotone.{0} φ ↔ ExistentialEquivalent.{0} φ :=
  (deletionMonotone_neg_iff φ).symm.trans
    ((deletionMonotone_iff_universalEquivalent (.neg φ)).trans
      (universalEquivalent_neg_iff_existentialEquivalent φ))

theorem extensionPreserved_iff_existentialEquivalent (φ : Formula Atom Agent) :
    ExtensionPreserved.{0} φ ↔ ExistentialEquivalent.{0} φ :=
  (deletionAntimonotone_iff_extensionPreserved φ).symm.trans
    (deletionAntimonotone_iff_existentialEquivalent φ)

theorem simulationPreserved_iff_existentialEquivalent (φ : Formula Atom Agent) :
    SimulationPreserved.{0} φ ↔ ExistentialEquivalent.{0} φ :=
  (extensionPreserved_iff_simulationPreserved φ).symm.trans
    (extensionPreserved_iff_existentialEquivalent φ)

variable [Infinite Atom] [Nonempty Agent]

omit [Nonempty Agent] in
/-- Every condition of the universal PAL list is equivalent to condition (4).
This states all seven equivalences, hence all eight conditions are equivalent. -/
theorem pal_universal_characterizations (φ : Formula Atom Agent) :
    (DeletionMonotone.{0} φ ↔ UniversalEquivalent.{0} φ) ∧
    (SubmodelPreserved.{0} φ ↔ UniversalEquivalent.{0} φ) ∧
    (RefinementPreserved.{0} φ ↔ UniversalEquivalent.{0} φ) ∧
    (PALPositive.{0} φ ↔ UniversalEquivalent.{0} φ) ∧
    (PALOperatorMonotone.{0} (.neg φ) ↔ UniversalEquivalent.{0} φ) ∧
    (PALComparisonUp.{0} φ ↔ UniversalEquivalent.{0} φ) ∧
    (AnnouncementPreserved.{0} φ ↔ UniversalEquivalent.{0} φ) := by
  have h := deletionMonotone_iff_universalEquivalent φ
  exact ⟨h,submodelPreserved_iff_universalEquivalent φ,
    refinementPreserved_iff_universalEquivalent φ,
    (palPositive_iff_deletionMonotone φ).trans h,
    (pal_neg_operatorMonotone_iff_deletionMonotone φ).trans h,
    (palComparisonUp_iff_deletionMonotone φ).trans h,
    (announcementPreserved_iff_submodelPreserved φ).trans
      (submodelPreserved_iff_universalEquivalent φ)⟩

/-- The BPAL list uses the revised order allowing both state and arrow deletion. -/
theorem bpal_universal_characterizations (φ : Formula Atom Agent) :
    (DeletionMonotone.{0} φ ↔ UniversalEquivalent.{0} φ) ∧
    (SubmodelPreserved.{0} φ ↔ UniversalEquivalent.{0} φ) ∧
    (RefinementPreserved.{0} φ ↔ UniversalEquivalent.{0} φ) ∧
    (BPALPositive.{0} φ ↔ UniversalEquivalent.{0} φ) ∧
    (GeneralBPALOperatorMonotone.{0} (.neg φ) ↔ UniversalEquivalent.{0} φ) ∧
    (BPALComparisonUp.{0} φ ↔ UniversalEquivalent.{0} φ) ∧
    (BPALAnnouncementPreserved.{0} φ ↔ UniversalEquivalent.{0} φ) := by
  have h := deletionMonotone_iff_universalEquivalent φ
  exact ⟨h,submodelPreserved_iff_universalEquivalent φ,
    refinementPreserved_iff_universalEquivalent φ,
    (bpalPositive_iff_deletionMonotone φ).trans h,
    (general_neg_operatorMonotone_iff_deletionMonotone φ).trans h,
    (bpalComparisonUp_iff_deletionMonotone φ).trans h,
    (bpalAnnouncementPreserved_iff_submodelPreserved φ).trans
      (submodelPreserved_iff_universalEquivalent φ)⟩

omit [Nonempty Agent] in
theorem pal_existential_characterizations (φ : Formula Atom Agent) :
    (DeletionAntimonotone.{0} φ ↔ ExistentialEquivalent.{0} φ) ∧
    (ExtensionPreserved.{0} φ ↔ ExistentialEquivalent.{0} φ) ∧
    (SimulationPreserved.{0} φ ↔ ExistentialEquivalent.{0} φ) ∧
    (PALNegative.{0} φ ↔ ExistentialEquivalent.{0} φ) ∧
    (PALOperatorMonotone.{0} φ ↔ ExistentialEquivalent.{0} φ) ∧
    (PALComparisonDown.{0} φ ↔ ExistentialEquivalent.{0} φ) ∧
    (AnnouncementReflected.{0} φ ↔ ExistentialEquivalent.{0} φ) := by
  have h := deletionAntimonotone_iff_existentialEquivalent φ
  exact ⟨h,extensionPreserved_iff_existentialEquivalent φ,
    simulationPreserved_iff_existentialEquivalent φ,
    (palNegative_iff_deletionAntimonotone φ).trans h,
    (palOperatorMonotone_iff_deletionAntimonotone φ).trans h,
    (palComparisonDown_iff_deletionAntimonotone φ).trans h,
    (announcementPreserved_neg_iff_reflected φ).symm.trans
      (((announcementPreserved_iff_submodelPreserved (.neg φ)).trans
        (submodelPreserved_iff_universalEquivalent (.neg φ))).trans
          (universalEquivalent_neg_iff_existentialEquivalent φ))⟩

theorem bpal_existential_characterizations (φ : Formula Atom Agent) :
    (DeletionAntimonotone.{0} φ ↔ ExistentialEquivalent.{0} φ) ∧
    (ExtensionPreserved.{0} φ ↔ ExistentialEquivalent.{0} φ) ∧
    (SimulationPreserved.{0} φ ↔ ExistentialEquivalent.{0} φ) ∧
    (BPALNegative.{0} φ ↔ ExistentialEquivalent.{0} φ) ∧
    (GeneralBPALOperatorMonotone.{0} φ ↔ ExistentialEquivalent.{0} φ) ∧
    (BPALComparisonDown.{0} φ ↔ ExistentialEquivalent.{0} φ) ∧
    (BPALAnnouncementReflected.{0} φ ↔ ExistentialEquivalent.{0} φ) := by
  have h := deletionAntimonotone_iff_existentialEquivalent φ
  exact ⟨h,extensionPreserved_iff_existentialEquivalent φ,
    simulationPreserved_iff_existentialEquivalent φ,
    (bpalNegative_iff_deletionAntimonotone φ).trans h,
    (general_operatorMonotone_iff_deletionAntimonotone φ).trans h,
    (bpalComparisonDown_iff_deletionAntimonotone φ).trans h,
    (bpalAnnouncementPreserved_neg_iff_reflected φ).symm.trans
      (((bpalAnnouncementPreserved_iff_submodelPreserved (.neg φ)).trans
        (submodelPreserved_iff_universalEquivalent (.neg φ))).trans
          (universalEquivalent_neg_iff_existentialEquivalent φ))⟩

end Main

end PropertiesOfPublicAnnouncementsAsOperators
