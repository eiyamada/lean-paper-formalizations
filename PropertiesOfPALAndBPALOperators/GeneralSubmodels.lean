import PropertiesOfPALAndBPALOperators.FixedPoints

/-!
# The revised BPAL order

Definition 5 in source commit `3cc2775` permits both deletion of states and
deletion of arrows. `ArrowSubmodel` is its same-domain special case. Here a
model on a subtype may also delete arrows from the induced restriction.
-/

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u v w

variable {World : Type u} {Atom : Type v} {Agent : Type w}

abbrev BPALSubmodel {S : Set World} (N : Model S Atom Agent)
    (M : Model World Atom Agent) : Prop := ArrowSubmodel N (M.restrict S)

def GeneralBPALOperatorMonotone (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent) (S : Set W) (N : Model S Atom Agent),
    BPALSubmodel N M → BPALSubmodel (N.update φ) (M.update φ)

theorem DeletionAntimonotone.general_operatorMonotone {φ : Formula Atom Agent}
    (hφ : DeletionAntimonotone.{u} φ) : GeneralBPALOperatorMonotone.{u} φ := by
  intro W M S N hNM
  constructor
  · exact hNM.val_eq
  · intro i x y hxy
    refine ⟨hNM.rel_le i x y hxy.1, ?_⟩
    have ht := hφ (M.restrict S) N hNM y hxy.2
    exact ((deletionAntimonotone_iff_extensionPreserved φ).mp hφ) M S y ht

/-- Quantifying over arbitrary subtypes includes the same-domain operator order. -/
theorem general_operatorMonotone_implies_same_domain (φ : Formula Atom Agent)
    (hφ : GeneralBPALOperatorMonotone.{u} φ) : BPALOperatorMonotone.{u} φ := by
  intro W M N hNM
  let S : Set W := Set.univ
  have hsub : BPALSubmodel (N.restrict S) M := by
    constructor
    · funext p x
      exact congrFun (congrFun hNM.val_eq p) x.val
    · intro i x y hxy
      exact hNM.rel_le i x.val y.val hxy
  have h := hφ W M S (N.restrict S) hsub
  constructor
  · exact hNM.val_eq
  · intro i x y hxy
    have hy : (N.restrict S).Satisfies ⟨y, trivial⟩ φ :=
      (N.restrict_satisfies_iff S N.forwardClosed_univ ⟨y, trivial⟩ φ).mpr hxy.2
    exact h.rel_le i ⟨x, trivial⟩ ⟨y, trivial⟩ ⟨hxy.1, hy⟩

/-- Theorem 19(6) for the revised order, including smaller domains. -/
theorem general_operatorMonotone_iff_deletionAntimonotone [Nonempty Agent]
    (φ : Formula Atom Agent) :
    GeneralBPALOperatorMonotone.{u} φ ↔ DeletionAntimonotone.{u} φ :=
  ⟨fun h => (operatorMonotone_iff_deletionAntimonotone φ).mp
    (general_operatorMonotone_implies_same_domain φ h),
    DeletionAntimonotone.general_operatorMonotone⟩

theorem general_neg_operatorMonotone_iff_deletionMonotone [Nonempty Agent]
    (φ : Formula Atom Agent) :
    GeneralBPALOperatorMonotone.{u} (.neg φ) ↔ DeletionMonotone.{u} φ :=
  (general_operatorMonotone_iff_deletionAntimonotone (.neg φ)).trans
    (deletionAntimonotone_neg_iff φ)

theorem Universal.general_fixed_downward {φ : Formula Atom Agent} (hφ : Universal φ)
    (M : Model World Atom Agent) {S : Set World} (N : Model S Atom Agent)
    (hNM : BPALSubmodel N M) (hM : M.update φ = M) : N.update φ = N := by
  apply (Extinction.fixed_iff_targets N φ).mpr
  intro i x y hxy
  apply hφ.preserved_arrowSubmodel hNM
  apply hφ.preserved_submodel M S y
  exact (Extinction.fixed_iff_targets M φ).mp hM i x.val y.val (hNM.rel_le i x y hxy)

theorem Existential.general_fixed_below_update {φ : Formula Atom Agent}
    (hφ : Existential φ) (M : Model World Atom Agent) {S : Set World}
    (N : Model S Atom Agent) (hNM : BPALSubmodel N M) (hN : N.update φ = N) :
    BPALSubmodel N (M.update φ) := by
  have hmono : GeneralBPALOperatorMonotone.{u} φ :=
    DeletionAntimonotone.general_operatorMonotone hφ.deletionAntimonotone
  have h := hmono World M S N hNM
  simpa only [hN] using h

theorem general_fixed_below_ordinalUpdate (φ : Formula Atom Agent)
    (hmono : GeneralBPALOperatorMonotone.{u} φ)
    (M : Model World Atom Agent) {S : Set World} (N : Model S Atom Agent)
    (hNM : BPALSubmodel N M) (hfix : N.update φ = N) (α : Ordinal.{max u w}) :
    BPALSubmodel N (ordinalUpdate M φ α) := by
  induction α using Ordinal.induction with
  | h α ih =>
      constructor
      · funext p x
        exact (congrFun (congrFun hNM.val_eq p) x).trans
          (propext (ordinalUpdate_val M φ α p x.val)).symm
      · intro i x y hxy
        apply (ordinalUpdate_rel_iff M φ α i x.val y.val).mpr
        refine ⟨hNM.rel_le i x y hxy, fun β hβ => ?_⟩
        have h := hmono World (ordinalUpdate M φ β) S N (ih β hβ)
        have he : (N.update φ).rel i x y := by rw [hfix]; exact hxy
        exact (h.rel_le i x y he).2

/-- Greatest fixedness quantifies over both smaller domains and fewer arrows. -/
theorem Existential.general_terminal_greatest {φ : Formula Atom Agent}
    (hφ : Existential φ) (M : Model World Atom Agent) (S : Set World)
    (N : Model S Atom Agent) (hNM : BPALSubmodel N M) (hfix : N.update φ = N) :
    BPALSubmodel N (bpalTerminal M φ) :=
  general_fixed_below_ordinalUpdate φ
    (DeletionAntimonotone.general_operatorMonotone hφ.deletionAntimonotone)
    M N hNM hfix _

end PropertiesOfPALAndBPALOperators
