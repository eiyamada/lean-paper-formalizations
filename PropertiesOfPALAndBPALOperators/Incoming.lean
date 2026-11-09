import PropertiesOfPALAndBPALOperators.Dynamics
import PropertiesOfPALAndBPALOperators.Extinction

/-! # Global PAL/BPAL stabilization bounds

A fresh predecessor turns every surviving world into a detectable BPAL target.
This proves that uniform bounds over all models coincide, even though individual
models may have PAL and BPAL ranks differing by one.
-/

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u v w

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- Adding a predecessor does not change truth at any old world at any ordinal
stage, for arbitrary static postconditions. -/
theorem predecessor_ordinal_truth (M : Model World Atom Agent) (root : World)
    (agent : Agent) (φ : Formula Atom Agent) (α : Ordinal.{max u w})
    (x : World) (ψ : Formula Atom Agent) :
    (ordinalUpdate (Extinction.predecessor M root agent) φ α).Satisfies (some x) ψ ↔
      (ordinalUpdate M φ α).Satisfies x ψ := by
  induction α using Ordinal.induction generalizing x ψ with
  | h α ih =>
      have hrel (i : Agent) (x y : World) :
          (ordinalUpdate (Extinction.predecessor M root agent) φ α).rel i (some x) (some y) ↔
            (ordinalUpdate M φ α).rel i x y := by
        rw [ordinalUpdate_rel_iff, ordinalUpdate_rel_iff]
        apply and_congr Iff.rfl
        apply forall_congr'
        intro β
        apply forall_congr'
        intro hβ
        exact ih β hβ y φ
      have hnone (i : Agent) (x : World) :
          ¬(ordinalUpdate (Extinction.predecessor M root agent) φ α).rel i (some x) none := by
        intro h
        exact ((ordinalUpdate_rel_iff _ _ _ _ _ _).mp h).1
      induction ψ generalizing x with
      | atom p => simp [ordinalUpdate_val, Extinction.predecessor, Model.Satisfies]
      | neg ψ ihψ => exact not_congr (ihψ x)
      | conj ψ χ ihψ ihχ => exact and_congr (ihψ x) (ihχ x)
      | box i ψ ihψ =>
          constructor
          · intro h y hxy
            exact (ihψ y).mp (h (some y) ((hrel i x y).mpr hxy))
          · intro h y hxy
            cases y with
            | none => exact (hnone i x hxy).elim
            | some y => exact (ihψ y).mpr (h y ((hrel i x y).mp hxy))

theorem predecessor_palDomain (M : Model World Atom Agent) (root : World)
    (agent : Agent) (φ : Formula Atom Agent) (α : Ordinal.{max u w}) (x : World) :
    some x ∈ palDomain (Extinction.predecessor M root agent) φ α ↔ x ∈ palDomain M φ α := by
  apply forall_congr'
  intro β
  apply forall_congr'
  intro _hβ
  exact predecessor_ordinal_truth M root agent φ β x φ

/-- Uniform ordinal stabilization bounds over K agree in the two logics.
Theorem 26's final PAL/BPAL assertion is the case `α = omega`. -/
theorem global_palStable_iff_bpalStable [Nonempty Agent] (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) :
    (∀ {W : Type u} (M : Model W Atom Agent), PALStable M φ α) ↔
      (∀ {W : Type u} (M : Model W Atom Agent), BPALStable M φ α) := by
  classical
  constructor
  · intro h W M
    exact bpalStable_of_palStable M φ (h M)
  · intro h W M
    apply (palStable_iff M φ α).mpr
    intro x hx
    let a := Classical.arbitrary Agent
    let P := Extinction.predecessor M x a
    have hP : BPALStable P φ α := h P
    have hsurv : some x ∈ palDomain P φ α :=
      (predecessor_palDomain M x a φ α x).mpr hx
    have harrow : (ordinalUpdate P φ α).rel a none (some x) :=
      (ordinalUpdate_rel_iff P φ α a none (some x)).mpr ⟨⟨rfl, rfl⟩, hsurv⟩
    have harrow' : (ordinalUpdate P φ (Order.succ α)).rel a none (some x) := by
      rw [hP]
      exact harrow
    rw [ordinalUpdate_succ, Model.update_rel] at harrow'
    exact (predecessor_ordinal_truth M x a φ α x φ).mp harrow'.2

theorem global_palRank_le_iff_bpalRank_le [Nonempty Agent] (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) :
    (∀ {W : Type u} (M : Model W Atom Agent), palRank M φ ≤ α) ↔
      (∀ {W : Type u} (M : Model W Atom Agent), bpalRank M φ ≤ α) := by
  simp only [palRank_le_iff, bpalRank_le_iff]
  exact global_palStable_iff_bpalStable φ α

end PropertiesOfPALAndBPALOperators
