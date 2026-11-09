import PropertiesOfPALAndBPALOperators.FiniteStabilization
import Mathlib.Order.WithBot

/-! # The finite stabilization rank, with infinity when no finite stage is stable -/

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity

universe u v w

noncomputable def firstFiniteStage (P : Nat → Prop) : WithTop Nat := by
  classical
  exact if h : ∃ n, P n then (Nat.find h : WithTop Nat) else ⊤

theorem firstFiniteStage_ne_top_iff (P : Nat → Prop) :
    firstFiniteStage P ≠ ⊤ ↔ ∃ n, P n := by
  classical
  by_cases h : ∃ n, P n <;> simp [firstFiniteStage, h]

theorem firstFiniteStage_eq_iff (P : Nat → Prop) (n : Nat) :
    firstFiniteStage P = (n : WithTop Nat) ↔ P n ∧ ∀ m < n, ¬ P m := by
  classical
  by_cases h : ∃ n, P n
  · rw [firstFiniteStage, dif_pos h]
    constructor
    · intro he
      have he' : Nat.find h = n := WithTop.coe_injective he
      subst n
      exact ⟨Nat.find_spec h, fun m hm => Nat.find_min h hm⟩
    · rintro ⟨hn, hmin⟩
      apply congrArg (fun n : Nat => (n : WithTop Nat))
      exact le_antisymm (Nat.find_min' h hn)
        (Nat.le_of_not_gt (fun hlt => hmin _ hlt (Nat.find_spec h)))
  · rw [firstFiniteStage, dif_neg h]
    constructor
    · intro he
      exact False.elim (WithTop.top_ne_coe he)
    · rintro ⟨hn, _⟩
      exact False.elim (h ⟨n, hn⟩)

variable {World : Type u} {Atom : Type v} {Agent : Type w}

noncomputable def palFiniteRank (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    WithTop Nat := firstFiniteStage (fun n => PALStable M φ (n : Ordinal.{max u w}))

noncomputable def bpalFiniteRank (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    WithTop Nat := firstFiniteStage (fun n => BPALStable M φ (n : Ordinal.{max u w}))

theorem palFiniteRank_ne_top_iff (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    palFiniteRank M φ ≠ ⊤ ↔ palRank M φ < Ordinal.omega0 :=
  (firstFiniteStage_ne_top_iff _).trans (palRank_lt_omega_iff M φ).symm

theorem bpalFiniteRank_ne_top_iff (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    bpalFiniteRank M φ ≠ ⊤ ↔ bpalRank M φ < Ordinal.omega0 :=
  (firstFiniteStage_ne_top_iff _).trans (bpalRank_lt_omega_iff M φ).symm

end PropertiesOfPALAndBPALOperators
