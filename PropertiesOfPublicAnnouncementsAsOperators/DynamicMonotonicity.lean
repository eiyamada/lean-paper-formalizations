import PropertiesOfPublicAnnouncementsAsOperators.Monotonicity

/-!
# Reduction transports for arbitrary PAL and BPAL formulas

Theorem 19 admits formulas containing nested announcements. These bridges use
the already proved announcement-elimination translations and identify the
actual dynamic operators with their static reductions. They apply at every
current PAL domain, not only at the initial model.
-/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity

universe u v w

variable {World : Type u} {Atom : Type v} {Agent : Type w}

theorem palUpdate_reduction (M : Model World Atom Agent) (ξ : PALFormula Atom Agent)
    (S : Set World) : palUpdate M ξ S = palUpdate M ξ.toFormula.toPAL S := by
  apply Set.ext
  intro x
  exact and_congr Iff.rfl ((PAL.satisfies_toFormula M S x ξ).trans
    (PAL.satisfies_toPAL M S x ξ.toFormula).symm)

theorem bpalUpdateModel_reduction (M : Model World Atom Agent)
    (ξ : BPALFormula Atom Agent) : bpalUpdateModel M ξ = M.update ξ.toFormula := by
  apply Model.ext'
  · intro i x y
    exact and_congr Iff.rfl (BPAL.initiallySatisfies_toFormula M y ξ)
  · intro p x
    rfl

theorem pal_dynamic_restriction (M : Model World Atom Agent) (S : Set World)
    (x : S) (ξ : PALFormula Atom Agent) :
    PAL.Satisfies M S x.val ξ ↔ PAL.InitiallySatisfies (M.restrict S) x ξ := by
  rw [PAL.satisfies_toFormula,PAL.initiallySatisfies_toFormula,domainModel_eq_targetCut]
  exact targetCut_satisfies_restrict M S x ξ.toFormula

theorem pal_dynamic_announcement (M : Model World Atom Agent) (x : World)
    (α ξ : PALFormula Atom Agent) :
    PAL.InitiallySatisfies M x (.announce α ξ) ↔
      (M.Satisfies x α.toFormula → (M.update α.toFormula).Satisfies x ξ.toFormula) := by
  simp only [PAL.initiallySatisfies_toFormula,PALFormula.toFormula,
    Model.satisfies_imp,Model.satisfies_announcementReduce]

theorem bpal_dynamic_announcement (M : Model World Atom Agent) (x : World)
    (α ξ : BPALFormula Atom Agent) :
    BPAL.InitiallySatisfies M x (.announce α ξ) ↔
      (M.update α.toFormula).Satisfies x ξ.toFormula := by
  simp only [BPAL.initiallySatisfies_toFormula,BPALFormula.toFormula,
    Model.satisfies_announcementReduce]

section TypeZero

variable {Atom Agent : Type}

theorem pal_dynamic_deletionMonotone_iff (ξ : PALFormula Atom Agent) :
    (∀ {W : Type} (M N : Model W Atom Agent), ArrowSubmodel N M → ∀ x,
      PAL.InitiallySatisfies M x ξ → PAL.InitiallySatisfies N x ξ) ↔
      DeletionMonotone.{0} ξ.toFormula := by
  simp only [PAL.initiallySatisfies_toFormula,DeletionMonotone]

theorem bpal_dynamic_deletionMonotone_iff (ξ : BPALFormula Atom Agent) :
    (∀ {W : Type} (M N : Model W Atom Agent), ArrowSubmodel N M → ∀ x,
      BPAL.InitiallySatisfies M x ξ → BPAL.InitiallySatisfies N x ξ) ↔
      DeletionMonotone.{0} ξ.toFormula := by
  simp only [BPAL.initiallySatisfies_toFormula,DeletionMonotone]

theorem pal_dynamic_universalEquivalent_iff (ξ : PALFormula Atom Agent) :
    (∃ ψ, Universal ψ ∧ ∀ {W : Type} (M : Model W Atom Agent) x,
      PAL.InitiallySatisfies M x ξ ↔ M.Satisfies x ψ) ↔
      UniversalEquivalent.{0} ξ.toFormula := by
  simp only [PAL.initiallySatisfies_toFormula,UniversalEquivalent,Equivalent]

theorem bpal_dynamic_universalEquivalent_iff (ξ : BPALFormula Atom Agent) :
    (∃ ψ, Universal ψ ∧ ∀ {W : Type} (M : Model W Atom Agent) x,
      BPAL.InitiallySatisfies M x ξ ↔ M.Satisfies x ψ) ↔
      UniversalEquivalent.{0} ξ.toFormula := by
  simp only [BPAL.initiallySatisfies_toFormula,UniversalEquivalent,Equivalent]

theorem pal_dynamic_existentialEquivalent_iff (ξ : PALFormula Atom Agent) :
    (∃ ψ, Existential ψ ∧ ∀ {W : Type} (M : Model W Atom Agent) x,
      PAL.InitiallySatisfies M x ξ ↔ M.Satisfies x ψ) ↔
      ExistentialEquivalent.{0} ξ.toFormula := by
  simp only [PAL.initiallySatisfies_toFormula,ExistentialEquivalent,Equivalent]

theorem bpal_dynamic_existentialEquivalent_iff (ξ : BPALFormula Atom Agent) :
    (∃ ψ, Existential ψ ∧ ∀ {W : Type} (M : Model W Atom Agent) x,
      BPAL.InitiallySatisfies M x ξ ↔ M.Satisfies x ψ) ↔
      ExistentialEquivalent.{0} ξ.toFormula := by
  simp only [BPAL.initiallySatisfies_toFormula,ExistentialEquivalent,Equivalent]

theorem pal_dynamic_operatorMonotone_iff (ξ : PALFormula Atom Agent) :
    (∀ {W : Type} (M : Model W Atom Agent) (S T : Set W),
      S ⊆ T → palUpdate M ξ S ⊆ palUpdate M ξ T) ↔
      PALOperatorMonotone.{0} ξ.toFormula := by
  constructor
  · intro h W M S T hST
    rw [← palUpdate_reduction M ξ S,← palUpdate_reduction M ξ T]
    exact h M S T hST
  · intro h W M S T hST
    rw [palUpdate_reduction M ξ S,palUpdate_reduction M ξ T]
    exact h M S T hST

theorem bpal_dynamic_operatorMonotone_iff (ξ : BPALFormula Atom Agent) :
    (∀ (W : Type) (M : Model W Atom Agent) (S : Set W) (N : Model S Atom Agent),
      BPALSubmodel N M → BPALSubmodel (bpalUpdateModel N ξ) (bpalUpdateModel M ξ)) ↔
      GeneralBPALOperatorMonotone.{0} ξ.toFormula := by
  simp only [bpalUpdateModel_reduction,GeneralBPALOperatorMonotone]

variable [Inhabited Atom]

theorem pal_dynamic_universal_preservation (ξ : PALFormula Atom Agent) :
    (∀ {W : Type} (M N : Model W Atom Agent), ArrowSubmodel N M → ∀ x,
      PAL.InitiallySatisfies M x ξ → PAL.InitiallySatisfies N x ξ) ↔
    (∃ ψ, Universal ψ ∧ ∀ {W : Type} (M : Model W Atom Agent) x,
      PAL.InitiallySatisfies M x ξ ↔ M.Satisfies x ψ) :=
  (pal_dynamic_deletionMonotone_iff ξ).trans
    ((deletionMonotone_iff_universalEquivalent ξ.toFormula).trans
      (pal_dynamic_universalEquivalent_iff ξ).symm)

theorem bpal_dynamic_universal_preservation (ξ : BPALFormula Atom Agent) :
    (∀ {W : Type} (M N : Model W Atom Agent), ArrowSubmodel N M → ∀ x,
      BPAL.InitiallySatisfies M x ξ → BPAL.InitiallySatisfies N x ξ) ↔
    (∃ ψ, Universal ψ ∧ ∀ {W : Type} (M : Model W Atom Agent) x,
      BPAL.InitiallySatisfies M x ξ ↔ M.Satisfies x ψ) :=
  (bpal_dynamic_deletionMonotone_iff ξ).trans
    ((deletionMonotone_iff_universalEquivalent ξ.toFormula).trans
      (bpal_dynamic_universalEquivalent_iff ξ).symm)

theorem pal_dynamic_operator_characterization (ξ : PALFormula Atom Agent) :
    (∀ {W : Type} (M : Model W Atom Agent) (S T : Set W),
      S ⊆ T → palUpdate M ξ S ⊆ palUpdate M ξ T) ↔
    (∃ ψ, Existential ψ ∧ ∀ {W : Type} (M : Model W Atom Agent) x,
      PAL.InitiallySatisfies M x ξ ↔ M.Satisfies x ψ) :=
  (pal_dynamic_operatorMonotone_iff ξ).trans
    (((palOperatorMonotone_iff_deletionAntimonotone ξ.toFormula).trans
      (deletionAntimonotone_iff_existentialEquivalent ξ.toFormula)).trans
        (pal_dynamic_existentialEquivalent_iff ξ).symm)

theorem bpal_dynamic_operator_characterization [Nonempty Agent]
    (ξ : BPALFormula Atom Agent) :
    (∀ (W : Type) (M : Model W Atom Agent) (S : Set W) (N : Model S Atom Agent),
      BPALSubmodel N M → BPALSubmodel (bpalUpdateModel N ξ) (bpalUpdateModel M ξ)) ↔
    (∃ ψ, Existential ψ ∧ ∀ {W : Type} (M : Model W Atom Agent) x,
      BPAL.InitiallySatisfies M x ξ ↔ M.Satisfies x ψ) :=
  (bpal_dynamic_operatorMonotone_iff ξ).trans
    (((general_operatorMonotone_iff_deletionAntimonotone ξ.toFormula).trans
      (deletionAntimonotone_iff_existentialEquivalent ξ.toFormula)).trans
        (bpal_dynamic_existentialEquivalent_iff ξ).symm)

end TypeZero

end PropertiesOfPublicAnnouncementsAsOperators
