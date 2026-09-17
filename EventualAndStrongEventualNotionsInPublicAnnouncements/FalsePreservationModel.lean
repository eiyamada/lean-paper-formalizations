import EventualAndStrongEventualNotionsInPublicAnnouncements.FalsePreservation
import EventualAndStrongEventualNotionsInPublicAnnouncements.PeelingModels

/-! The concrete one-peeling countermodel with a persistent target, Lemma 12. -/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements
namespace FalsePreservationCountermodels

open ClassificationSigmaValidity FalsePreservation

abbrev model (n : Nat) := OnePeeling.modelAt true n
abbrev limitModel := OnePeeling.modelLimit true
abbrev witness (finite : Bool) := theta finite false true

@[simp] theorem node_W (n m : Nat) (j : Fin (m + 2)) :
    (model n).Satisfies (.node m j) W := by
  simp [W, Model.Satisfies, model, OnePeeling.modelAt, OnePeeling.valuation]

@[simp] theorem persistent_T (n : Nat) : (model n).Satisfies .persistent T := by
  simp [T, Model.Satisfies, model, OnePeeling.modelAt, OnePeeling.valuation]

theorem node_D (n m : Nat) (j : Fin (m + 2)) :
    (model n).Satisfies (.node m j) (D false true) ↔ n < m + 1 - j.val := by
  by_cases hj : j.val % 2 = 0
  · have hs : ¬ (model n).Satisfies (.node m j) (.atom 2) := by
      simp [Model.Satisfies, model, OnePeeling.modelAt, OnePeeling.valuation, hj]
    simp only [D, Model.satisfies_or, Model.satisfies_and, Model.satisfies_neg,
      hs, false_and, not_false_eq_true, true_and, false_or]
    have ha : OnePeeling.activeAgent j.val = true := by
      simp [OnePeeling.activeAgent, hj]
    rw [← ha, OnePeeling.node_forward_dia_iff]
    constructor
    · rintro ⟨l, hl, hn, _⟩
      have hbound := j.isLt
      omega
    · intro hn
      let l : Fin (m + 2) := ⟨j.val + 1, by omega⟩
      refine ⟨l, rfl, by dsimp [l]; omega, node_W n m l, ?_⟩
      change l.val % 2 = 1
      dsimp [l]
      omega
  · have hj' : j.val % 2 = 1 := by omega
    have hs : (model n).Satisfies (.node m j) (.atom 2) := by
      simp [Model.Satisfies, model, OnePeeling.modelAt, OnePeeling.valuation, hj']
    simp only [D, Model.satisfies_or, Model.satisfies_and, Model.satisfies_neg,
      hs, true_and, not_true_eq_false, false_and, or_false]
    have ha : OnePeeling.activeAgent j.val = false := by
      simp [OnePeeling.activeAgent, hj]
    rw [← ha, OnePeeling.node_forward_dia_iff]
    constructor
    · rintro ⟨l, hl, hn, _⟩
      have hbound := j.isLt
      omega
    · intro hn
      let l : Fin (m + 2) := ⟨j.val + 1, by omega⟩
      refine ⟨l, rfl, by dsimp [l]; omega, node_W n m l, ?_⟩
      change ¬ l.val % 2 = 1
      dsimp [l]
      omega

theorem root_F (n : Nat) : (model n).Satisfies .root (F false true) := by
  apply (Model.satisfies_dia _ _ _ _).mpr
  let j : Fin (n + 2) := ⟨0, by omega⟩
  refine ⟨.node n j, (OnePeeling.root_head_iff true n n j).mpr ⟨rfl, by omega⟩,
    node_W n n j, (node_D n n j).mpr ?_⟩
  simp [j]

theorem root_not_N (n : Nat) : ¬ (model n).Satisfies .root (N false) := by
  intro hN
  let j : Fin (n + 2) := ⟨0, by omega⟩
  exact hN (.node n j)
    ((OnePeeling.root_head_iff true n n j).mpr ⟨rfl, by omega⟩) (node_W n n j)

theorem persistent_witness (n : Nat) (finite : Bool) :
    (model n).Satisfies .persistent (witness finite) := by
  apply (theta_at_T (model n) finite false true .persistent (persistent_T n)).mpr
  apply (K_agreement (model n) (OnePeeling.modelAt_isK45 true n)
    false true ((OnePeeling.root_persistent_iff true n).mpr rfl)).mp
  exact (Model.satisfies_or _ _ _ _).mpr (Or.inl (root_F n))

theorem node_witness (n m : Nat) (j : Fin (m + 2)) (finite : Bool) :
    (model n).Satisfies (.node m j) (witness finite) ↔ n < m + 1 - j.val :=
  (theta_at_W (model n) finite false true (.node m j) (node_W n m j)).trans
    (node_D n m j)

theorem finite_iterate (finite : Bool) (n : Nat) :
    (model 0).iterateUpdate (witness finite) n = model n := by
  apply OnePeeling.iterate_eq true (witness finite)
  · exact fun n m j => node_witness n m j finite
  · exact fun n _ => persistent_witness n finite

theorem root_B (n : Nat) : (model n).Satisfies .root (B false true) ↔ 0 < n := by
  rw [B, Model.satisfies_dia]
  constructor
  · rintro ⟨y, hy, hW, hnD⟩
    cases y with
    | root => exact (OnePeeling.no_root_target true n false .root hy).elim
    | persistent =>
        have ht : (model n).val 1 .persistent := by trivial
        exact (hW.2 ht).elim
    | node m j =>
        obtain ⟨hj, hn⟩ := (OnePeeling.root_head_iff true n m j).mp hy
        have hnot : ¬ n < m + 1 - j.val := fun h => hnD ((node_D n m j).mpr h)
        simp only [hj, Nat.sub_zero] at hnot
        omega
  · intro hn
    let m := n - 1
    let j : Fin (m + 2) := ⟨0, by omega⟩
    have hm : m + 1 = n := by dsimp [m]; omega
    refine ⟨.node m j, (OnePeeling.root_head_iff true n m j).mpr ⟨rfl, by omega⟩,
      node_W n m j, ?_⟩
    intro hD
    have hlt := (node_D n m j).mp hD
    dsimp [j] at hlt
    omega

theorem root_strong_false (n : Nat) :
    ¬ (model n).Satisfies .root (witness false) := by
  intro h
  simp only [witness, theta, Bool.false_eq_true, ↓reduceIte,
    Model.satisfies_or, Model.satisfies_and] at h
  rcases h with (⟨hW, _⟩ | ⟨hT, _⟩) | ⟨_, hN, _⟩
  · exact hW.1 (by trivial)
  · exact hT.1 (by trivial)
  · exact root_not_N n hN

theorem root_finite_iff (n : Nat) :
    (model n).Satisfies .root (witness true) ↔ 0 < n := by
  change (model n).Satisfies .root (theta00fin false true) ↔ _
  rw [theta00fin_decomposition]
  have hSE : ¬ (model n).Satisfies .root (theta00SE false true) := root_strong_false n
  simp only [hSE, false_or]
  exact ⟨fun h => (root_B n).mp h.2, fun h => ⟨by trivial, (root_B n).mpr h⟩⟩

theorem limit_N (x : OnePeeling.World) : limitModel.Satisfies x (N false) := by
  intro y hy hW
  have heq := hy.2.2
  subst y
  exact hW.2 (by trivial)

theorem limit_root_U : limitModel.Satisfies .root (U false) := by
  apply (Model.satisfies_dia _ _ _ _).mpr
  exact ⟨.persistent, by simp [limitModel, OnePeeling.modelLimit,
    OnePeeling.block, OnePeeling.target], by
      simp [T, Model.Satisfies, limitModel, OnePeeling.modelLimit, OnePeeling.valuation]⟩

theorem limit_persistent_U : limitModel.Satisfies .persistent (U false) := by
  apply (Model.satisfies_dia _ _ _ _).mpr
  exact ⟨.persistent, by simp [limitModel, OnePeeling.modelLimit,
    OnePeeling.block, OnePeeling.target], by
      simp [T, Model.Satisfies, limitModel, OnePeeling.modelLimit, OnePeeling.valuation]⟩

theorem limit_root_witness (finite : Bool) :
    limitModel.Satisfies .root (witness finite) := by
  apply (Model.satisfies_or _ _ _ _).mpr
  apply Or.inr
  refine ⟨by trivial, ?_⟩
  cases finite with
  | false => exact ⟨limit_N .root, limit_root_U⟩
  | true =>
    exact (Model.satisfies_or _ _ _ _).mpr
      (Or.inr ⟨limit_N .root, limit_root_U⟩)

theorem limit_persistent_witness (finite : Bool) :
    limitModel.Satisfies .persistent (witness finite) := by
  apply (theta_at_T limitModel finite false true .persistent (by
    simp [T, Model.Satisfies, limitModel, OnePeeling.modelLimit, OnePeeling.valuation])).mpr
  exact (Model.satisfies_or _ _ _ _).mpr
    (Or.inr ⟨limit_N .persistent, limit_persistent_U⟩)

theorem limit_fixed (finite : Bool) :
    limitModel.update (witness finite) = limitModel :=
  OnePeeling.modelLimit_update_eq true (witness finite)
    (fun _ => limit_persistent_witness finite)

end FalsePreservationCountermodels
end EventualAndStrongEventualNotionsInPublicAnnouncements
