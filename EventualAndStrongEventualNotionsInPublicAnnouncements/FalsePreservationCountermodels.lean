import EventualAndStrongEventualNotionsInPublicAnnouncements.FalsePreservationModel
import EventualAndStrongEventualNotionsInPublicAnnouncements.Renaming

/-! The ordinal counterexamples in Lemma 12. -/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements
namespace FalsePreservationCountermodels

open ClassificationSigmaValidity FalsePreservation

theorem omega_eq_limit (finite : Bool) :
    ordinalUpdate (model 0) (witness finite) Ordinal.omega0 = limitModel := by
  apply Model.ext'
  · intro a x y
    rw [ordinalUpdate_limit_rel_iff _ _ Ordinal.isSuccLimit_omega0]
    rw [← OnePeeling.rel_allStages_iff_limit true a x y]
    constructor
    · intro h n
      simpa only [ordinalUpdate_natCast, finite_iterate] using h n (Ordinal.nat_lt_omega0 n)
    · intro h β hβ
      obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hβ
      simpa only [ordinalUpdate_natCast, finite_iterate] using h n
  · intro p x
    exact ordinalUpdate_val _ _ _ _ _

theorem ordinal_ge_omega (finite : Bool) (α : Ordinal) (hα : Ordinal.omega0 ≤ α) :
    ordinalUpdate (model 0) (witness finite) α = limitModel := by
  have hstep : ordinalUpdate (model 0) (witness finite) (Order.succ Ordinal.omega0) =
      ordinalUpdate (model 0) (witness finite) Ordinal.omega0 := by
    rw [ordinalUpdate_succ, omega_eq_limit, limit_fixed]
  rw [ordinalUpdate_eq_of_ge_of_step _ _ hstep hα, omega_eq_limit]

theorem not_ordinalStrongEventual :
    ¬ OrdinalStrongEventual.{0} false false (theta00SE false true) := by
  intro h
  obtain ⟨α, _, htail⟩ := h (model 0) (OnePeeling.modelAt_isK45 true 0) .root
    (root_strong_false 0)
  have hv := htail (max α Ordinal.omega0) (le_max_left _ _)
  change ¬ (ordinalUpdate (model 0) (witness false) _).Satisfies .root (witness false)
    at hv
  rw [ordinal_ge_omega false _ (le_max_right _ _)] at hv
  exact hv (limit_root_witness false)

theorem not_ordinalEventual :
    ¬ OrdinalEventual.{0} false false (theta00fin false true) := by
  intro h
  have hzero : ¬ (model 0).Satisfies .root (witness true) := by
    rw [root_finite_iff]
    exact Nat.lt_irrefl 0
  obtain ⟨α, hα, hfalse⟩ := h (model 0) (OnePeeling.modelAt_isK45 true 0) .root hzero
  change ¬ (ordinalUpdate (model 0) (witness true) α).Satisfies .root (witness true)
    at hfalse
  by_cases hω : α < Ordinal.omega0
  · obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hω
    have hn : 0 < n := by exact_mod_cast hα
    rw [ordinalUpdate_natCast, finite_iterate] at hfalse
    exact hfalse ((root_finite_iff n).mpr hn)
  · rw [ordinal_ge_omega true α (le_of_not_gt hω)] at hfalse
    exact hfalse (limit_root_witness true)

theorem lemma12_twoAgents :
    (∃ φ : Formula Nat Bool, StrongEventual.{0} false false φ ∧
      ¬ OrdinalStrongEventual.{0} false false φ) ∧
    (∃ φ : Formula Nat Bool, FiniteStageCondition.{0} false false φ ∧
      ¬ OrdinalEventual.{0} false false φ) := by
  exact ⟨⟨theta00SE false true, theta00SE_strongEventual false true,
    not_ordinalStrongEventual⟩,
    ⟨theta00fin false true, theta00fin_finiteStageCondition false true,
      not_ordinalEventual⟩⟩

/-- Lemma 12 in every agent language containing two distinct agents. -/
theorem lemma12 {Agent : Type} (a b : Agent) (hab : a ≠ b) :
    (∃ φ : Formula Nat Agent, StrongEventual.{0} false false φ ∧
      ¬ OrdinalStrongEventual.{0} false false φ) ∧
    (∃ φ : Formula Nat Agent, FiniteStageCondition.{0} false false φ ∧
      ¬ OrdinalEventual.{0} false false φ) := by
  classical
  let g : Bool → Agent := fun q => if q then b else a
  have hg : Function.Injective g := by
    intro x y h
    cases x <;> cases y
    · rfl
    · exact (hab h).elim
    · exact (hab h.symm).elim
    · rfl
  have hf : Function.LeftInverse (id : Nat → Nat) id := fun _ => rfl
  have hg' := Function.leftInverse_invFun hg
  obtain ⟨⟨φ, hφ, hnφ⟩, ⟨ψ, hψ, hnψ⟩⟩ := lemma12_twoAgents
  refine ⟨⟨φ.map id g, strongEventual_map hφ id g, ?_⟩,
    ⟨ψ.map id g, finiteStageCondition_map hψ id g, ?_⟩⟩
  · intro h
    exact hnφ ((ordinalStrongEventual_map_iff id g id (Function.invFun g)
      hf hg' false false φ).mp h)
  · intro h
    exact hnψ ((ordinalEventual_map_iff id g id (Function.invFun g)
      hf hg' false false ψ).mp h)

end FalsePreservationCountermodels
end EventualAndStrongEventualNotionsInPublicAnnouncements
