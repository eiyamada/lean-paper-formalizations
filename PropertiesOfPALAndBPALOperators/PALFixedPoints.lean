import PropertiesOfPALAndBPALOperators.FixedPoints
import PropertiesOfPALAndBPALOperators.Algebra

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u v w

variable {World : Type u} {Atom : Type v} {Agent : Type w}

noncomputable def palTerminal (M : Model World Atom Agent) (φ : Formula Atom Agent) : Set World :=
  palDomain M φ (palRank M φ)

theorem palTerminal_fixed (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    palUpdate M φ.toPAL (palTerminal M φ) = palTerminal M φ := by
  change {x | x ∈ palDomain M φ (palRank M φ) ∧
    PAL.Satisfies M (palDomain M φ (palRank M φ)) x φ.toPAL} = _
  rw [← palDomain_succ_pal]
  exact palRank_stable M φ

theorem domainModel_arrowSubmodel (M : Model World Atom Agent) {S T : Set World}
    (hST : S ⊆ T) : ArrowSubmodel (PAL.domainModel M S) (PAL.domainModel M T) :=
  ⟨rfl, fun _ _ _ h => ⟨hST h.1, h.2⟩⟩

theorem palUpdate_monotone (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (hφ : DeletionAntimonotone.{u} φ) {S T : Set World} (hST : S ⊆ T) :
    palUpdate M φ.toPAL S ⊆ palUpdate M φ.toPAL T := by
  intro x hx
  refine ⟨hST hx.1, ?_⟩
  exact (PAL.satisfies_toPAL M T x φ).mpr
    (hφ _ _ (domainModel_arrowSubmodel M hST) x ((PAL.satisfies_toPAL M S x φ).mp hx.2))

theorem pal_fixed_below_ordinalDomain (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (hφ : DeletionAntimonotone.{u} φ)
    (S : Set World) (hS : palUpdate M φ.toPAL S = S) (α : Ordinal.{max u w}) :
    S ⊆ palDomain M φ α := by
  induction α using Ordinal.induction with
  | h α ih =>
      intro x hx β hβ
      have hST : S ⊆ palDomain M φ β := ih β hβ
      have hsub := domainModel_arrowSubmodel M hST
      rw [palDomain_domainModel] at hsub
      apply hφ _ _ hsub x
      rw [← PAL.satisfies_toPAL]
      exact (pal_fixed_iff M φ.toPAL S).mp hS x hx

/-- The PAL terminal domain is the union of all fixed induced submodels. -/
theorem palTerminal_eq_union_fixed (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (hφ : DeletionAntimonotone.{u} φ) :
    palTerminal M φ = ⋃₀ {S | palUpdate M φ.toPAL S = S} := by
  ext x
  constructor
  · intro hx
    exact ⟨palTerminal M φ, palTerminal_fixed M φ, hx⟩
  · rintro ⟨S, hS, hx⟩
    exact pal_fixed_below_ordinalDomain M φ hφ S hS _ hx

theorem Universal.pal_fixed_downward {φ : Formula Atom Agent} (hφ : Universal φ)
    (M : Model World Atom Agent) {S T : Set World} (hST : S ⊆ T)
    (hT : palUpdate M φ.toPAL T = T) : palUpdate M φ.toPAL S = S := by
  apply (pal_fixed_iff M φ.toPAL S).mpr
  intro x hx
  rw [PAL.satisfies_toPAL]
  apply hφ.preserved_arrowSubmodel (domainModel_arrowSubmodel M hST)
  exact (PAL.satisfies_toPAL M T x φ).mp ((pal_fixed_iff M φ.toPAL T).mp hT x (hST hx))

theorem Universal.pal_update_idempotent {φ : Formula Atom Agent} (hφ : Universal φ)
    (M : Model World Atom Agent) (S : Set World) :
    palUpdate M φ.toPAL (palUpdate M φ.toPAL S) = palUpdate M φ.toPAL S := by
  apply (pal_fixed_iff M φ.toPAL _).mpr
  intro x hx
  rw [PAL.satisfies_toPAL]
  apply hφ.preserved_arrowSubmodel
    (domainModel_arrowSubmodel M (palUpdate_deflationary M φ.toPAL S))
  exact (PAL.satisfies_toPAL M S x φ).mp hx.2

theorem Universal.pal_absorption {φ : Formula Atom Agent} (hφ : Universal φ)
    (M : Model World Atom Agent) (ψ : PALFormula Atom Agent) (S : Set World) :
    palUpdate M φ.toPAL (palUpdate M ψ (palUpdate M φ.toPAL S)) =
      palUpdate M ψ (palUpdate M φ.toPAL S) :=
  hφ.pal_fixed_downward M (palUpdate_deflationary M ψ _) (hφ.pal_update_idempotent M S)

theorem Universal.pal_composition_idempotent {φ ψ : Formula Atom Agent}
    (hφ : Universal φ) (hψ : Universal ψ) (M : Model World Atom Agent) (S : Set World) :
    palUpdate M ψ.toPAL (palUpdate M φ.toPAL
      (palUpdate M ψ.toPAL (palUpdate M φ.toPAL S))) =
      palUpdate M ψ.toPAL (palUpdate M φ.toPAL S) := by
  rw [hφ.pal_absorption, hψ.pal_update_idempotent]

theorem palTerminal_eq_update_of_idempotent (M : Model World Atom Agent)
    (φ : Formula Atom Agent)
    (hid : palUpdate M φ.toPAL (palUpdate M φ.toPAL Set.univ) =
      palUpdate M φ.toPAL Set.univ) :
    palTerminal M φ = palUpdate M φ.toPAL Set.univ := by
  have hone : palDomain M φ 1 = palUpdate M φ.toPAL Set.univ := by
    rw [← Ordinal.succ_zero, palDomain_succ_pal, palDomain_zero]
    rfl
  have hstable : PALStable M φ 1 := by
    rw [PALStable, palDomain_succ_pal]
    change palUpdate M φ.toPAL (palDomain M φ 1) = palDomain M φ 1
    rw [hone]
    exact hid
  have hle := palRank_le_of_stable M φ hstable
  exact (palDomain_eq_of_ge_of_stable M φ (palRank_stable M φ) hle).symm.trans hone

theorem Universal.pal_terminal_eq_update {φ : Formula Atom Agent} (hφ : Universal φ)
    (M : Model World Atom Agent) : palTerminal M φ = palUpdate M φ.toPAL Set.univ :=
  palTerminal_eq_update_of_idempotent M φ (hφ.pal_update_idempotent M Set.univ)

theorem domainModel_palUpdate (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (S : Set World) :
    PAL.domainModel M (palUpdate M φ.toPAL S) = (PAL.domainModel M S).update φ := by
  apply Model.ext'
  · intro i x y
    simp only [PAL.domainModel_rel, palUpdate, PAL.satisfies_toPAL,
      Model.update_rel]
    tauto
  · intro p x
    rfl

theorem sequentialFormula_palUpdate (M : Model World Atom Agent)
    (φ ψ : Formula Atom Agent) (S : Set World) :
    palUpdate M (sequentialFormula φ ψ).toPAL S =
      palUpdate M ψ.toPAL (palUpdate M φ.toPAL S) := by
  ext x
  change (S x ∧ PAL.Satisfies M S x (sequentialFormula φ ψ).toPAL) ↔
    ((S x ∧ PAL.Satisfies M S x φ.toPAL) ∧
      PAL.Satisfies M (palUpdate M φ.toPAL S) x ψ.toPAL)
  simp only [PAL.satisfies_toPAL, sequentialFormula, Model.satisfies_and,
    Model.satisfies_announcementReduce, domainModel_palUpdate]
  tauto

theorem Universal.pal_terminal_composition {φ ψ : Formula Atom Agent}
    (hφ : Universal φ) (hψ : Universal ψ) (M : Model World Atom Agent) :
    palTerminal M (sequentialFormula φ ψ) =
      palUpdate M ψ.toPAL (palUpdate M φ.toPAL Set.univ) := by
  rw [← sequentialFormula_palUpdate]
  apply palTerminal_eq_update_of_idempotent
  simp only [sequentialFormula_palUpdate]
  exact hφ.pal_composition_idempotent hψ M Set.univ

theorem palTerminal_eq_of_same_fixed (φ ψ : Formula Atom Agent)
    (hφ : DeletionAntimonotone.{u} φ) (hψ : DeletionAntimonotone.{u} ψ)
    (M : Model World Atom Agent)
    (hfix : ∀ S, palUpdate M φ.toPAL S = S ↔ palUpdate M ψ.toPAL S = S) :
    palTerminal M φ = palTerminal M ψ := by
  exact Set.Subset.antisymm
    (pal_fixed_below_ordinalDomain M ψ hψ (palTerminal M φ)
      ((hfix _).mp (palTerminal_fixed M φ)) _)
    (pal_fixed_below_ordinalDomain M φ hφ (palTerminal M ψ)
      ((hfix _).mpr (palTerminal_fixed M ψ)) _)

/-- The PAL half of Theorem 23(4), including the stabilized composite. -/
theorem Existential.pal_terminal_order_independent [Nonempty Agent]
    {φ ψ : Formula Atom Agent} (hφ : Existential φ) (hψ : Existential ψ)
    (M : Model World Atom Agent) :
    palTerminal M (sequentialFormula φ ψ) = palTerminal M (sequentialFormula ψ φ) ∧
    palTerminal M (sequentialFormula φ ψ) = palTerminal M (.conj φ ψ) := by
  have hseq : DeletionAntimonotone.{u} (sequentialFormula φ ψ) :=
    (operatorMonotone_iff_deletionAntimonotone (sequentialFormula φ ψ)).mp
      (sequentialFormula_monotone φ ψ hφ.operatorMonotone hψ.operatorMonotone)
  constructor
  · apply palTerminal_eq_of_same_fixed _ _ hseq
      ((operatorMonotone_iff_deletionAntimonotone (sequentialFormula ψ φ)).mp
        (sequentialFormula_monotone ψ φ hψ.operatorMonotone hφ.operatorMonotone)) M
    intro S
    rw [sequentialFormula_palUpdate, sequentialFormula_palUpdate,
      pal_fixed_composition_iff, pal_fixed_composition_iff]
    exact and_comm
  · apply palTerminal_eq_of_same_fixed _ _ hseq (Existential.conj hφ hψ).deletionAntimonotone M
    intro S
    rw [sequentialFormula_palUpdate, pal_fixed_composition_iff]
    exact (pal_fixed_conj_iff M φ.toPAL ψ.toPAL S).symm

end PropertiesOfPALAndBPALOperators
