import PropertiesOfPublicAnnouncementsAsOperators.Dynamics

/-! # Idempotence and commutativity characterizations of stabilization -/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u v w

variable {World : Type u} {Atom : Type v} {Agent : Type w}

theorem bpalStable_of_eq_later (M : Model World Atom Agent) (φ : Formula Atom Agent)
    {α β : Ordinal.{max u w}} (hαβ : Order.succ α ≤ β)
    (heq : ordinalUpdate M φ β = ordinalUpdate M φ α) : BPALStable M φ α := by
  apply Model.ext'
  · intro i x y
    constructor
    · exact ordinalUpdate_rel_antitone M φ (Order.le_succ α)
    · intro h
      have hβ : (ordinalUpdate M φ β).rel i x y := by rw [heq]; exact h
      exact ordinalUpdate_rel_antitone M φ hαβ hβ
  · intro p x
    simp

theorem palStable_of_eq_later (M : Model World Atom Agent) (φ : Formula Atom Agent)
    {α β : Ordinal.{max u w}} (hαβ : Order.succ α ≤ β)
    (heq : palDomain M φ β = palDomain M φ α) : PALStable M φ α := by
  apply Set.Subset.antisymm (palDomain_antitone M φ (Order.le_succ α))
  intro x hx
  have hβ : x ∈ palDomain M φ β := by rw [heq]; exact hx
  exact palDomain_antitone M φ hαβ hβ

/-- Restarting the PAL orbit at its surviving domain gives the ordinal tail. -/
theorem palDomain_add (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α β : Ordinal.{max u w}) :
    palDomain M φ (α + β) =
      palDomain M φ α ∩ palDomain (ordinalUpdate M φ α) φ β := by
  ext x
  constructor
  · intro h
    refine ⟨palDomain_antitone M φ (Ordinal.le_add_right α β) h, ?_⟩
    intro γ hγ
    rw [← ordinalUpdate_add]
    exact h (α + γ) ((add_lt_add_iff_left α).mpr hγ)
  · rintro ⟨hα, hβ⟩ γ hγ
    by_cases hγα : γ < α
    · exact hα γ hγα
    · have heq : α + (γ - α) = γ := Ordinal.add_sub_cancel_of_le (le_of_not_gt hγα)
      have hsub : γ - α < β := (add_lt_add_iff_left α).mp (by rw [heq]; exact hγ)
      have ht := hβ (γ - α) hsub
      rw [← ordinalUpdate_add, heq] at ht
      exact ht

/-- Iteration starting with a public domain `S`, still expressed in the original
ambient carrier. The initial `S` factor ensures deleted worlds never return. -/
def palRestart (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (S : Set World) (α : Ordinal.{max u w}) : Set World :=
  S ∩ palDomain (PAL.domainModel M S) φ α

theorem palRestart_at_stage (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α β : Ordinal.{max u w}) :
    palRestart M φ (palDomain M φ α) β = palDomain M φ (α + β) := by
  rw [palRestart, palDomain_domainModel, palDomain_add]

theorem ordinalUpdate_one (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    ordinalUpdate M φ 1 = M.update φ := by
  simpa using ordinalUpdate_succ M φ 0

/-- At omega, doing one announcement before the omega run changes nothing. -/
theorem omega_after_update (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    ordinalUpdate (M.update φ) φ Ordinal.omega0 = ordinalUpdate M φ Ordinal.omega0 := by
  rw [← ordinalUpdate_one, ← ordinalUpdate_add, Ordinal.one_add_omega0]

/-- Theorem 26(1) iff (2), pointwise BPAL form. -/
theorem bpal_omega_stable_iff_idempotent (M : Model World Atom Agent)
    (φ : Formula Atom Agent) :
    bpalRank M φ ≤ Ordinal.omega0 ↔
      ordinalUpdate (ordinalUpdate M φ Ordinal.omega0) φ Ordinal.omega0 =
        ordinalUpdate M φ Ordinal.omega0 := by
  rw [bpalRank_le_iff, ← ordinalUpdate_add]
  constructor
  · intro h
    exact ordinalUpdate_eq_of_ge_of_step M φ h (Ordinal.le_add_right _ _)
  · intro h
    apply bpalStable_of_eq_later M φ _ h
    exact add_le_add_left (le_of_lt Ordinal.one_lt_omega0) Ordinal.omega0

/-- Theorem 26(1) iff (3), pointwise BPAL form. -/
theorem bpal_omega_stable_iff_commutes (M : Model World Atom Agent)
    (φ : Formula Atom Agent) :
    bpalRank M φ ≤ Ordinal.omega0 ↔
      (ordinalUpdate M φ Ordinal.omega0).update φ =
        ordinalUpdate (M.update φ) φ Ordinal.omega0 := by
  rw [bpalRank_le_iff, omega_after_update]
  rw [BPALStable, ordinalUpdate_succ]

/-- Theorem 26(1) iff (2), pointwise PAL form. -/
theorem pal_omega_stable_iff_idempotent (M : Model World Atom Agent)
    (φ : Formula Atom Agent) :
    palRank M φ ≤ Ordinal.omega0 ↔
      palRestart M φ (palDomain M φ Ordinal.omega0) Ordinal.omega0 =
        palDomain M φ Ordinal.omega0 := by
  rw [palRank_le_iff, palRestart_at_stage]
  constructor
  · intro h
    exact palDomain_eq_of_ge_of_stable M φ h (Ordinal.le_add_right _ _)
  · intro h
    apply palStable_of_eq_later M φ _ h
    exact add_le_add_left (le_of_lt Ordinal.one_lt_omega0) Ordinal.omega0

/-- Theorem 26(1) iff (3), pointwise PAL form. -/
theorem pal_omega_stable_iff_commutes (M : Model World Atom Agent)
    (φ : Formula Atom Agent) :
    palRank M φ ≤ Ordinal.omega0 ↔
      palRestart M φ (palDomain M φ Ordinal.omega0) 1 =
        palRestart M φ (palDomain M φ 1) Ordinal.omega0 := by
  rw [palRank_le_iff, palRestart_at_stage, palRestart_at_stage, Ordinal.one_add_omega0]
  exact Iff.rfl

/-- For a positive finite power, idempotence is equivalent to stabilization
at that power. This is Theorem 25(2) iff (4) for BPAL. -/
theorem bpal_finite_stable_iff_idempotent (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (N : Nat) (hN : 1 ≤ N) :
    bpalRank M φ ≤ (N : Ordinal.{max u w}) ↔
      (M.iterateUpdate φ N).iterateUpdate φ N = M.iterateUpdate φ N := by
  rw [bpalRank_le_iff]
  have hN' : (1 : Ordinal.{max u w}) ≤ (N : Ordinal.{max u w}) := by exact_mod_cast hN
  simp only [← ordinalUpdate_natCast]
  rw [← ordinalUpdate_add]
  constructor
  · intro h
    exact ordinalUpdate_eq_of_ge_of_step M φ h (Ordinal.le_add_right _ _)
  · intro h
    exact bpalStable_of_eq_later M φ (add_le_add_left hN' _) h

/-- The PAL version of the positive finite-power idempotence equivalence. -/
theorem pal_finite_stable_iff_idempotent (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (N : Nat) (hN : 1 ≤ N) :
    palRank M φ ≤ (N : Ordinal.{max u w}) ↔
      palRestart M φ (palDomain M φ (N : Ordinal.{max u w})) (N : Ordinal.{max u w}) =
        palDomain M φ (N : Ordinal.{max u w}) := by
  rw [palRank_le_iff, palRestart_at_stage]
  have hN' : (1 : Ordinal.{max u w}) ≤ (N : Ordinal.{max u w}) := by exact_mod_cast hN
  constructor
  · intro h
    exact palDomain_eq_of_ge_of_stable M φ h (Ordinal.le_add_right _ _)
  · intro h
    exact palStable_of_eq_later M φ (add_le_add_left hN' _) h

end PropertiesOfPublicAnnouncementsAsOperators
