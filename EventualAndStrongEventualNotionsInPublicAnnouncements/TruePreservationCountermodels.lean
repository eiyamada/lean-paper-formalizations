import EventualAndStrongEventualNotionsInPublicAnnouncements.TruePreservation
import EventualAndStrongEventualNotionsInPublicAnnouncements.Oscillation
import EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalConditions

/-!
# Limit loss for the true-preservation witnesses

Both announcements have the same explicit finite stages on the two-peeling
model. Every arrow is removed by omega. The first formula is true at all finite
stages and false permanently at omega; the second is true only initially.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements
namespace TruePreservation

open ClassificationSigmaValidity
open Oscillation Oscillation.PeelingWorld

universe w
variable {Agent : Type w} (a b : Agent) (hab : a ≠ b)

@[simp] theorem twoPeeling_t_node (n m : Nat) (d : Fin (m + 1)) (side : Bool) :
    (twoPeeling a b n).val 3 (.node m d side) ↔ d.val = m ∧ side = false := by
  simp [twoPeeling, valuation, IsHead, head, Fin.ext_iff]

@[simp] theorem twoPeeling_P_head (n m : Nat) :
    (twoPeeling a b n).Satisfies (head m) (P 0 3) := by
  simp [P, twoPeeling, valuation, IsHead, head]

/-- Guarding the chain by C leaves precisely the same finite distance test. -/
theorem twoPeeling_D_odd (hab : a ≠ b) (n m : Nat) (d : Fin (m + 1)) :
    (twoPeeling a b n).Satisfies (.node m d true) (D 0 1 3 a b) ↔ n < d.val := by
  simp only [D, Model.satisfies_or, Model.satisfies_and, Model.satisfies_atom,
    Model.satisfies_neg, Model.satisfies_dia, Oscillation.twoPeeling_s,
    not_true_eq_false, false_and, or_false, true_and]
  constructor
  · rintro ⟨y, hy, _, _⟩
    obtain ⟨⟨e, he, rfl⟩, hn⟩ := (twoPeeling_rel_a a b hab n _ _).mp hy
    change n ≤ e.val at hn
    omega
  · intro hn
    let e : Fin (m + 1) := ⟨d.val - 1, by omega⟩
    have he : e.val + 1 = d.val := by dsimp [e]; omega
    refine ⟨.node m e false, ?_, ?_, ?_⟩
    · apply (twoPeeling_rel_a a b hab n _ _).mpr
      exact ⟨⟨e, he, rfl⟩, by change n ≤ e.val; dsimp [e]; omega⟩
    · refine ⟨twoPeeling_nonr a b n m e false, ?_⟩
      rw [twoPeeling_t_node]
      intro h
      have hd := d.isLt
      omega
    · simp

/-- Exactly one pair in each live branch falsifies A. -/
theorem twoPeeling_A (hab : a ≠ b) (n m : Nat) (d : Fin (m + 1)) (side : Bool) :
    (twoPeeling a b n).Satisfies (.node m d side) (A 0 1 3 a b) ↔ n ≠ d.val := by
  simp only [A, Model.satisfies_and, Model.satisfies_neg, Model.satisfies_atom,
    twoPeeling_nonr, not_false_eq_true, true_and, Model.satisfies_box, Model.satisfies_or]
  simp only [twoPeeling_rel_b a b hab, RB, distance]
  constructor
  · intro h hnd
    have ht := h (.node m d true) ⟨rfl, by simp [hnd]⟩
    rcases ht with hr | ht | hD
    · exact twoPeeling_nonr a b n m d true hr
    · simp only [twoPeeling_t_node, Bool.true_eq_false, and_false] at ht
    · have hlt := (twoPeeling_D_odd a b hab n m d).mp hD
      omega
  · intro hnd y hy
    rcases hy with ⟨rfl, hn⟩
    exact Or.inr (Or.inr ((twoPeeling_D_odd a b hab n m d).mpr
      (by change n ≤ d.val at hn; omega)))

/-- The next branch head witnesses falsity of Q at every head. -/
theorem twoPeeling_not_Q_head (hab : a ≠ b) (n m : Nat) :
    ¬(twoPeeling a b n).Satisfies (head m) (Q 0 1 3 a b) := by
  intro hQ
  have harrow : (twoPeeling a b n).rel a (head m) (head (n + 1)) := by
    rw [twoPeeling_rel_a a b hab, ra_head]
    exact ⟨⟨n + 1, rfl⟩, by simp [distance, head]⟩
  have hnotA := ((twoPeeling a b n).satisfies_imp _ _ _).mp
    (hQ (head (n + 1)) harrow) (twoPeeling_P_head a b n (n + 1))
  apply hnotA
  exact (twoPeeling_A a b hab n (n + 1) _ false).mpr (by simp)

@[simp] theorem twoPeeling_B_head (hab : a ≠ b) (n m : Nat) :
    (twoPeeling a b n).Satisfies (head m) (B 0 1 3 a b) ↔ n ≠ m := by
  rw [B, Model.satisfies_or]
  simp only [twoPeeling_not_Q_head a b hab, or_false]
  exact twoPeeling_A a b hab n m _ false

/-- Both announcements have the same value at every non-root state. -/
theorem twoPeeling_strong_node (hab : a ≠ b) (n m : Nat) (d : Fin (m + 1)) (side : Bool) :
    (twoPeeling a b n).Satisfies (.node m d side) (strongFormula 0 1 3 a b) ↔ n ≠ d.val := by
  classical
  by_cases hh : IsHead (.node m d side)
  · obtain ⟨k, hk⟩ := hh
    rw [hk, strong_at_P 0 1 3 a b _ _ (twoPeeling_P_head a b n k),
      twoPeeling_B_head a b hab]
    have hd : d.val = k := by simpa only [distance, head] using congrArg distance hk
    simp only [hd]
  · have hC : (twoPeeling a b n).Satisfies (.node m d side) (C 0 3) :=
      ⟨twoPeeling_nonr a b n m d side, hh⟩
    rw [strong_at_C 0 1 3 a b _ _ hC, twoPeeling_A a b hab]

theorem twoPeeling_stage_node (hab : a ≠ b) (n m : Nat) (d : Fin (m + 1)) (side : Bool) :
    (twoPeeling a b n).Satisfies (.node m d side) (stageFormula 0 1 3 4 a b) ↔ n ≠ d.val := by
  classical
  by_cases hh : IsHead (.node m d side)
  · obtain ⟨k, hk⟩ := hh
    rw [hk, stage_at_P 0 1 3 4 a b _ _ (twoPeeling_P_head a b n k),
      twoPeeling_B_head a b hab]
    have hd : d.val = k := by simpa only [distance, head] using congrArg distance hk
    simp only [hd]
  · have hC : (twoPeeling a b n).Satisfies (.node m d side) (C 0 3) :=
      ⟨twoPeeling_nonr a b n m d side, hh⟩
    rw [stage_at_C 0 1 3 4 a b _ _ hC, twoPeeling_A a b hab]

/-- A formula with the pair-distance truth rule produces the next explicit stage. -/
theorem twoPeeling_update_of_node (n : Nat) (θ : Formula (Fin 5) Agent)
    (hθ : ∀ m d side, (twoPeeling a b n).Satisfies (.node m d side) θ ↔ n ≠ d.val) :
    (twoPeeling a b n).update θ = twoPeeling a b (n + 1) := by
  apply Model.ext'
  · intro i x y
    cases y with
    | root =>
      cases x with
      | root => simp [Model.update_rel, twoPeeling, RA, RB, IsHead, head]
      | node m d side =>
        cases side <;> simp [Model.update_rel, twoPeeling, RA, RB, IsHead, head]
    | node m d side =>
      rw [Model.update_rel, hθ]
      change (_ ∧ n ≤ d.val) ∧ n ≠ d.val ↔ _ ∧ n + 1 ≤ d.val
      constructor
      · rintro ⟨⟨hr, hn⟩, hne⟩
        exact ⟨hr, by omega⟩
      · rintro ⟨hr, hn⟩
        exact ⟨⟨hr, by omega⟩, by omega⟩
  · intro p x
    rfl

theorem twoPeeling_strong_iterate (hab : a ≠ b) (n : Nat) :
    (twoPeeling a b 0).iterateUpdate (strongFormula 0 1 3 a b) n = twoPeeling a b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Model.iterateUpdate_succ, ih]
    exact twoPeeling_update_of_node a b n _ (twoPeeling_strong_node a b hab n)

theorem twoPeeling_stage_iterate (hab : a ≠ b) (n : Nat) :
    (twoPeeling a b 0).iterateUpdate (stageFormula 0 1 3 4 a b) n = twoPeeling a b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Model.iterateUpdate_succ, ih]
    exact twoPeeling_update_of_node a b n _ (twoPeeling_stage_node a b hab n)

theorem twoPeeling_Y_root (hab : a ≠ b) (n : Nat) :
    (twoPeeling a b n).Satisfies .root (Y 0 3 a) := by
  apply ((twoPeeling a b n).satisfies_dia _ _ _).mpr
  refine ⟨head n, ?_, twoPeeling_P_head a b n n⟩
  rw [twoPeeling_rel_a a b hab]
  exact ⟨⟨n, rfl⟩, by simp [distance, head]⟩

theorem twoPeeling_strong_root (hab : a ≠ b) (n : Nat) :
    (twoPeeling a b n).Satisfies .root (strongFormula 0 1 3 a b) := by
  exact ((twoPeeling a b n).satisfies_or _ _ _).mpr
    (Or.inr ⟨rfl, twoPeeling_Y_root a b hab n⟩)

theorem twoPeeling_not_H_root (hab : a ≠ b) (n : Nat) :
    ¬(twoPeeling a b n).Satisfies .root (H 0 1 3 a b) := by
  intro hH
  have harrow : (twoPeeling a b n).rel a .root (head n) := by
    rw [twoPeeling_rel_a a b hab]
    exact ⟨⟨n, rfl⟩, by simp [distance, head]⟩
  have hB := ((twoPeeling a b n).satisfies_imp _ _ _).mp
    (hH (head n) harrow) (twoPeeling_P_head a b n n)
  exact (twoPeeling_B_head a b hab n n).mp hB rfl

theorem twoPeeling_Z_root (hab : a ≠ b) (n : Nat) :
    (twoPeeling a b n).Satisfies .root (Z 0 3 4 a) ↔ n = 0 := by
  rw [Z, Model.satisfies_dia]
  constructor
  · rintro ⟨y, hy, _, hyu⟩
    change y = head 0 at hyu
    subst y
    have hn := ((twoPeeling_rel_a a b hab n _ _).mp hy).2
    simpa only [distance, head, Nat.le_zero] using hn
  · rintro rfl
    refine ⟨head 0, ?_, twoPeeling_P_head a b 0 0, rfl⟩
    rw [twoPeeling_rel_a a b hab]
    exact ⟨⟨0, rfl⟩, Nat.zero_le _⟩

theorem twoPeeling_stage_root (hab : a ≠ b) (n : Nat) :
    (twoPeeling a b n).Satisfies .root (stageFormula 0 1 3 4 a b) ↔ n = 0 := by
  have hr : (twoPeeling a b n).val 0 .root := rfl
  simp only [stageFormula, Model.satisfies_or, Model.satisfies_and, Model.satisfies_atom,
    base, C, P, Model.satisfies_neg, hr, not_true_eq_false, false_and, false_or, true_and]
  simp only [twoPeeling_not_H_root a b hab, and_false, or_false]
  exact twoPeeling_Z_root a b hab n

/-- The common terminal model has its original valuation and no arrows. -/
def emptyPeeling : Model PeelingWorld (Fin 5) Agent where
  rel _ _ _ := False
  val := valuation

/-- Every arrow of the explicit peeling run disappears before omega. -/
theorem twoPeeling_ordinal_omega (θ : Formula (Fin 5) Agent)
    (hfinite : ∀ n, (twoPeeling a b 0).iterateUpdate θ n = twoPeeling a b n) :
    ordinalUpdate (twoPeeling a b 0) θ Ordinal.omega0 = emptyPeeling := by
  apply Model.ext'
  · intro i x y
    constructor
    · intro hxy
      have hn := ordinalUpdate_rel_antitone (twoPeeling a b 0) θ
        (Ordinal.nat_lt_omega0 (distance y + 1)).le hxy
      rw [ordinalUpdate_natCast, hfinite] at hn
      have hh : distance y + 1 ≤ distance y := hn.2
      omega
    · exact False.elim
  · intro p x
    exact ordinalUpdate_val _ _ _ p x

@[simp] theorem emptyPeeling_update (θ : Formula (Fin 5) Agent) :
    (emptyPeeling (Agent := Agent)).update θ = emptyPeeling := by
  apply Model.ext'
  · intro i x y
    simp [emptyPeeling]
  · intro p x
    rfl

theorem twoPeeling_ordinal_after_omega (θ : Formula (Fin 5) Agent)
    (hfinite : ∀ n, (twoPeeling a b 0).iterateUpdate θ n = twoPeeling a b n)
    {α : Ordinal.{w}} (hα : Ordinal.omega0 ≤ α) :
    ordinalUpdate (twoPeeling a b 0) θ α = emptyPeeling := by
  have hω := twoPeeling_ordinal_omega a b θ hfinite
  have hstep : ordinalUpdate (twoPeeling a b 0) θ (Order.succ Ordinal.omega0) =
      ordinalUpdate (twoPeeling a b 0) θ Ordinal.omega0 := by
    rw [ordinalUpdate_succ, hω, emptyPeeling_update]
  rw [ordinalUpdate_eq_of_ge_of_step _ _ hstep hα, hω]

@[simp] theorem emptyPeeling_not_strong :
    ¬(emptyPeeling (Agent := Agent)).Satisfies .root (strongFormula 0 1 3 a b) := by
  simp [strongFormula, base, C, P, Y, emptyPeeling, valuation]

@[simp] theorem emptyPeeling_not_stage :
    ¬(emptyPeeling (Agent := Agent)).Satisfies .root (stageFormula 0 1 3 4 a b) := by
  simp [stageFormula, base, C, P, Y, Z, emptyPeeling, valuation]

/-- The finite strongly successful witness fails ordinal strong success. -/
theorem strongFormula_not_ordinalStrongEventual (hab : a ≠ b) :
    ¬OrdinalStrongEventual.{0} true true (strongFormula (0 : Fin 5) 1 3 a b) := by
  intro h
  obtain ⟨α, _, htail⟩ := h (twoPeeling a b 0) (twoPeeling_isK45 a b hab 0) .root
    (twoPeeling_strong_root a b hab 0)
  have hv := htail (max α Ordinal.omega0) (le_max_left _ _)
  change (ordinalUpdate (twoPeeling a b 0) (strongFormula 0 1 3 a b) _).Satisfies .root _ at hv
  rw [twoPeeling_ordinal_after_omega a b _ (twoPeeling_strong_iterate a b hab)
    (le_max_right _ _)] at hv
  exact emptyPeeling_not_strong a b hv

/-- The finite S witness has no positive ordinal return to truth. -/
theorem stageFormula_not_ordinalEventual (hab : a ≠ b) :
    ¬OrdinalEventual.{0} true true (stageFormula (0 : Fin 5) 1 3 4 a b) := by
  intro h
  obtain ⟨α, hα, hv⟩ := h (twoPeeling a b 0) (twoPeeling_isK45 a b hab 0) .root
    ((twoPeeling_stage_root a b hab 0).mpr rfl)
  change (ordinalUpdate (twoPeeling a b 0) (stageFormula 0 1 3 4 a b) α).Satisfies .root _ at hv
  by_cases hαω : α < Ordinal.omega0
  · obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hαω
    rw [ordinalUpdate_natCast, twoPeeling_stage_iterate a b hab] at hv
    have hn := (twoPeeling_stage_root a b hab n).mp hv
    subst n
    exact (lt_irrefl _ hα).elim
  · rw [twoPeeling_ordinal_after_omega a b _ (twoPeeling_stage_iterate a b hab)
      (le_of_not_gt hαω)] at hv
    exact emptyPeeling_not_stage a b hv

/-- Both strict separations in Lemma 11, with concrete formulas. -/
theorem limit_loss_separations (hab : a ≠ b) :
    (StrongEventual.{0} true true (strongFormula (0 : Fin 5) 1 3 a b) ∧
      ¬OrdinalStrongEventual.{0} true true (strongFormula (0 : Fin 5) 1 3 a b)) ∧
    (FiniteStageCondition.{0} true true (stageFormula (0 : Fin 5) 1 3 4 a b) ∧
      ¬OrdinalEventual.{0} true true (stageFormula (0 : Fin 5) 1 3 4 a b)) :=
  ⟨⟨strongFormula_strongEventual _ _ _ a b, strongFormula_not_ordinalStrongEventual a b hab⟩,
    ⟨stageFormula_finiteStageCondition _ _ _ _ a b, stageFormula_not_ordinalEventual a b hab⟩⟩

end TruePreservation
end EventualAndStrongEventualNotionsInPublicAnnouncements
