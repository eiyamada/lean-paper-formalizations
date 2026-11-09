import PropertiesOfPALAndBPALOperators.Preservation
import PropertiesOfPALAndBPALOperators.Dynamics
import PropertiesOfPALAndBPALOperators.Extinction

/-! # Greatest fixed points and order independence (Theorem 23) -/

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u v w

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- The stabilized actual BPAL model. -/
noncomputable def bpalTerminal (M : Model World Atom Agent) (φ : Formula Atom Agent) :=
  ordinalUpdate M φ (bpalRank M φ)

theorem bpalTerminal_fixed (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    (bpalTerminal M φ).update φ = bpalTerminal M φ := by
  exact (ordinalUpdate_succ M φ _).symm.trans (bpalRank_stable M φ)

theorem ordinalUpdate_submodel (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) : ArrowSubmodel (ordinalUpdate M φ α) M := by
  constructor
  · funext p x
    exact propext (ordinalUpdate_val M φ α p x)
  · intro i x y h
    exact ((ordinalUpdate_rel_iff M φ α i x y).mp h).1

/-- Every fixed point below the initial model survives every ordinal stage. -/
theorem fixed_below_ordinalUpdate (φ : Formula Atom Agent)
    (hmono : BPALOperatorMonotone.{u} φ) (M N : Model World Atom Agent)
    (hNM : ArrowSubmodel N M) (hfix : N.update φ = N) (α : Ordinal.{max u w}) :
    ArrowSubmodel N (ordinalUpdate M φ α) := by
  induction α using Ordinal.induction with
  | h α ih =>
      constructor
      · exact hNM.val_eq.trans (ordinalUpdate_submodel M φ α).val_eq.symm
      · intro i x y hxy
        apply (ordinalUpdate_rel_iff M φ α i x y).mpr
        refine ⟨hNM.rel_le i x y hxy, fun β hβ => ?_⟩
        have h := hmono (ordinalUpdate M φ β) N (ih β hβ)
        have he : (N.update φ).rel i x y := by rw [hfix]; exact hxy
        exact (h.rel_le i x y he).2

/-- The stabilized operator is the greatest fixed point below its input. -/
theorem bpalTerminal_greatest (φ : Formula Atom Agent)
    (hmono : BPALOperatorMonotone.{u} φ) (M : Model World Atom Agent) :
    ArrowSubmodel (bpalTerminal M φ) M ∧ (bpalTerminal M φ).update φ = bpalTerminal M φ ∧
    ∀ N, ArrowSubmodel N M → N.update φ = N → ArrowSubmodel N (bpalTerminal M φ) :=
  ⟨ordinalUpdate_submodel M φ _, bpalTerminal_fixed M φ,
    fun N hNM hfix => fixed_below_ordinalUpdate φ hmono M N hNM hfix _⟩

theorem bpalTerminal_rel_iff_exists_fixed (φ : Formula Atom Agent)
    (hmono : BPALOperatorMonotone.{u} φ) (M : Model World Atom Agent)
    (i : Agent) (x y : World) :
    (bpalTerminal M φ).rel i x y ↔
      ∃ N, ArrowSubmodel N M ∧ N.update φ = N ∧ N.rel i x y := by
  have h := bpalTerminal_greatest φ hmono M
  constructor
  · intro hxy
    exact ⟨bpalTerminal M φ, h.1, h.2.1, hxy⟩
  · rintro ⟨N, hNM, hfix, hxy⟩
    exact (h.2.2 N hNM hfix).rel_le i x y hxy

theorem Existential.terminal_greatest {φ : Formula Atom Agent} (hφ : Existential φ)
    (M : Model World Atom Agent) :
    ∀ N, ArrowSubmodel N M → N.update φ = N → ArrowSubmodel N (bpalTerminal M φ) :=
  (bpalTerminal_greatest φ hφ.operatorMonotone M).2.2

theorem Universal.terminal_eq_update {φ : Formula Atom Agent} (hφ : Universal φ)
    (M : Model World Atom Agent) : bpalTerminal M φ = M.update φ := by
  have hone : ordinalUpdate M φ 1 = M.update φ := by
    simpa only [Order.succ_eq_add_one, zero_add, ordinalUpdate_zero]
      using ordinalUpdate_succ M φ 0
  have hstable : BPALStable M φ 1 := by
    rw [BPALStable, ordinalUpdate_succ, hone]
    exact hφ.update_idempotent M
  have hle : bpalRank M φ ≤ 1 := bpalRank_le_of_stable M φ hstable
  have he := ordinalUpdate_eq_of_ge_of_step M φ (bpalRank_stable M φ) hle
  exact he.symm.trans hone

/-- Static formula implementing first φ, then ψ. -/
def sequentialFormula (φ ψ : Formula Atom Agent) : Formula Atom Agent :=
  .conj φ (Formula.announcementReduce φ ψ)

theorem sequentialFormula_update (M : Model World Atom Agent) (φ ψ : Formula Atom Agent) :
    M.update (sequentialFormula φ ψ) = (M.update φ).update ψ := by
  apply Model.ext'
  · intro i x y
    simp only [Model.update_rel, sequentialFormula, Model.satisfies_and,
      Model.satisfies_announcementReduce]
    exact and_assoc.symm
  · intro p x
    rfl

theorem sequentialFormula_monotone (φ ψ : Formula Atom Agent)
    (hφ : BPALOperatorMonotone.{u} φ) (hψ : BPALOperatorMonotone.{u} ψ) :
    BPALOperatorMonotone.{u} (sequentialFormula φ ψ) := by
  intro W M N hNM
  rw [sequentialFormula_update, sequentialFormula_update]
  exact hψ _ _ (hφ M N hNM)

theorem sequentialFormula_fixed (M : Model World Atom Agent) (φ ψ : Formula Atom Agent) :
    M.update (sequentialFormula φ ψ) = M ↔ M.update φ = M ∧ M.update ψ = M := by
  rw [sequentialFormula_update]
  constructor
  · intro h
    have hp : M.update φ = M := ArrowSubmodel.antisymm (update_arrowSubmodel M φ)
      (by simpa only [h] using update_arrowSubmodel (M.update φ) ψ)
    exact ⟨hp, by simpa only [hp] using h⟩
  · rintro ⟨hp, hq⟩
    rw [hp, hq]

theorem bpalTerminal_eq_update_of_idempotent (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (hid : (M.update φ).update φ = M.update φ) :
    bpalTerminal M φ = M.update φ := by
  have hone : ordinalUpdate M φ 1 = M.update φ := by
    simpa only [Ordinal.succ_zero, ordinalUpdate_zero] using ordinalUpdate_succ M φ 0
  have hs : BPALStable M φ 1 := by
    rw [BPALStable, ordinalUpdate_succ, hone]
    exact hid
  exact (ordinalUpdate_eq_of_ge_of_step M φ (bpalRank_stable M φ)
    (bpalRank_le_of_stable M φ hs)).symm.trans hone

theorem Universal.terminal_composition {φ ψ : Formula Atom Agent}
    (hφ : Universal φ) (hψ : Universal ψ) (M : Model World Atom Agent) :
    bpalTerminal M (sequentialFormula φ ψ) = (M.update φ).update ψ := by
  rw [← sequentialFormula_update]
  apply bpalTerminal_eq_update_of_idempotent
  simp only [sequentialFormula_update]
  exact hφ.composition_idempotent hψ M

theorem conjunctiveFormula_fixed (M : Model World Atom Agent) (φ ψ : Formula Atom Agent) :
    M.update (.conj φ ψ) = M ↔ M.update φ = M ∧ M.update ψ = M := by
  simp only [Extinction.fixed_iff_targets, Model.satisfies_and, forall_and]

/-- Monotone announcements with the same fixed points have the same terminal value. -/
theorem bpalTerminal_eq_of_same_fixed (φ ψ : Formula Atom Agent)
    (hφ : BPALOperatorMonotone.{u} φ) (hψ : BPALOperatorMonotone.{u} ψ)
    (hfix : ∀ (W : Type u) (N : Model W Atom Agent), N.update φ = N ↔ N.update ψ = N)
    (M : Model World Atom Agent) : bpalTerminal M φ = bpalTerminal M ψ := by
  have hp := bpalTerminal_greatest φ hφ M
  have hq := bpalTerminal_greatest ψ hψ M
  exact ArrowSubmodel.antisymm
    (hq.2.2 _ hp.1 ((hfix _ _).mp hp.2.1))
    (hp.2.2 _ hq.1 ((hfix _ _).mpr hq.2.1))

/-- Theorem 23(4): the stabilized composite is independent of announcement order. -/
theorem Existential.terminal_order_independent {φ ψ : Formula Atom Agent}
    (hφ : Existential φ) (hψ : Existential ψ) (M : Model World Atom Agent) :
    bpalTerminal M (sequentialFormula φ ψ) = bpalTerminal M (sequentialFormula ψ φ) ∧
    bpalTerminal M (sequentialFormula φ ψ) = bpalTerminal M (.conj φ ψ) := by
  constructor
  · apply bpalTerminal_eq_of_same_fixed _ _
      (sequentialFormula_monotone φ ψ hφ.operatorMonotone hψ.operatorMonotone)
      (sequentialFormula_monotone ψ φ hψ.operatorMonotone hφ.operatorMonotone)
    intro W N
    rw [sequentialFormula_fixed, sequentialFormula_fixed]
    exact and_comm
  · apply bpalTerminal_eq_of_same_fixed _ _
      (sequentialFormula_monotone φ ψ hφ.operatorMonotone hψ.operatorMonotone)
      (Existential.conj hφ hψ).operatorMonotone
    intro W N
    rw [sequentialFormula_fixed, conjunctiveFormula_fixed]

end PropertiesOfPALAndBPALOperators
