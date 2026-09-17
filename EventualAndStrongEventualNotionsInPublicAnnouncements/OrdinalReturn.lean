import EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalConditions
import EventualAndStrongEventualNotionsInPublicAnnouncements.PeelingModels
import EventualAndStrongEventualNotionsInPublicAnnouncements.ReversalSeparations

/-!
# Ordinal return separations

Lemma 10: in both preservation cases, strong ordinal eventuality need not imply
finite eventuality. The countermodels have arbitrarily long finite branches.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements
namespace OrdinalReturn

open ClassificationSigmaValidity

universe u w
variable {Agent : Type w} {World : Type u}

def chi (a b : Agent) : Formula Nat Agent :=
  .or (.conj (.atom 2) (.dia a (.neg (.atom 2))))
    (.conj (.neg (.atom 2)) (.dia b (.atom 2)))

def theta11 (a b : Agent) : Formula Nat Agent :=
  ReversalSeparations.completion a b (chi a b)

def D (a b : Agent) : Formula Nat Agent :=
  .or (.conj (.atom 2) (Formula.dia a
      (.conj (.neg (.atom 0)) (.conj (.neg (.atom 2)) Formula.verum))))
    (.conj (.neg (.atom 2)) (Formula.dia b
      (.conj (.neg (.atom 0)) (.conj (.atom 2) Formula.verum))))

def A (a b : Agent) : Formula Nat Agent := .conj (.neg (.atom 0)) (D a b)
def Y (a b : Agent) : Formula Nat Agent := .box a (.or (.atom 0) (A a b))
def theta00 (a b : Agent) : Formula Nat Agent :=
  .or (A a b) (.conj (.atom 0) (.neg (Y a b)))

/-- The completion is true at every common-belief stage, with no initial-value
hypothesis needed. -/
theorem theta11_ordinalStrongEventual (a b : Agent) :
    OrdinalStrongEventual.{u} true true (theta11 a b) := by
  apply ordinalStageCondition_iff_ordinalStrongEventual.mp
  intro W M hM x _ α hC
  exact ReversalSeparations.common_completion (ordinalUpdate M (theta11 a b) α)
    (ordinalUpdate_isK45 M (theta11 a b) hM α) a b (chi a b) x hC

/-- The alternating propositional diamond cannot become true when arrows are
removed, including at limit stages. -/
theorem D_backward_ordinal (M : Model World Nat Agent) (φ : Formula Nat Agent)
    (a b : Agent) (x : World) (α : Ordinal.{max u w}) :
    (ordinalUpdate M φ α).Satisfies x (D a b) → M.Satisfies x (D a b) := by
  classical
  simp only [D, Model.satisfies_or, Model.satisfies_and, Model.satisfies_dia,
    Model.satisfies_neg, Model.satisfies_atom, Model.satisfies_verum, and_true,
    ordinalUpdate_val]
  rintro (⟨hs, y, hxy, hr, ht⟩ | ⟨hs, y, hxy, hr, ht⟩)
  · exact Or.inl ⟨hs, y, (ordinalUpdate_rel_iff M φ α a x y).mp hxy |>.1, hr, ht⟩
  · exact Or.inr ⟨hs, y, (ordinalUpdate_rel_iff M φ α b x y).mp hxy |>.1, hr, ht⟩

/-- At an r-state, common belief of theta00 forces its negation. -/
theorem common_theta00_false_at_r (M : Model World Nat Agent) (a b : Agent)
    (x : World) (hr : M.val 0 x) (hC : Common M x (theta00 a b)) :
    ¬ M.Satisfies x (theta00 a b) := by
  have hY : M.Satisfies x (Y a b) := by
    intro y hxy
    have hy := hC y (Relation.TransGen.single ⟨a, hxy⟩)
    rcases (Model.satisfies_or _ _ _ _).mp hy with hA | hrY
    · exact (Model.satisfies_or _ _ _ _).mpr (Or.inr hA)
    · exact (Model.satisfies_or _ _ _ _).mpr (Or.inl hrY.1)
  intro hx
  rcases (Model.satisfies_or _ _ _ _).mp hx with hA | hrY
  · exact hA.1 hr
  · exact hrY.2 hY

/-- The initially false formula stays false at non-r states and is false at
every common-belief stage at r-states. -/
theorem theta00_ordinalStrongEventual (a b : Agent) :
    OrdinalStrongEventual.{u} false false (theta00 a b) := by
  apply ordinalStageCondition_iff_ordinalStrongEventual.mp
  intro W M hM x hx α hC
  by_cases hr : M.val 0 x
  · have hr' : (ordinalUpdate M (theta00 a b) α).val 0 x :=
      (ordinalUpdate_val M (theta00 a b) α 0 x).mpr hr
    exact common_theta00_false_at_r (ordinalUpdate M (theta00 a b) α) a b x hr' hC
  · have hD : ¬ M.Satisfies x (D a b) := by
      intro h
      exact hx ((Model.satisfies_or _ _ _ _).mpr (Or.inl ⟨hr, h⟩))
    intro hstage
    rcases (Model.satisfies_or _ _ _ _).mp hstage with hA | hrY
    · exact hD (D_backward_ordinal M (theta00 a b) a b x α hA.2)
    · exact hr ((ordinalUpdate_val M (theta00 a b) α 0 x).mp hrY.1)

namespace Countermodel

open OnePeeling

/-- All actual arrow targets have r false. -/
theorem target_not_r (keep : Bool) (n : Nat) (a : Bool) (x y : OnePeeling.World)
    (hxy : (modelAt keep n).rel a x y) : ¬ (modelAt keep n).val 0 y := by
  cases y with
  | root => exact (no_root_target keep n a x hxy).elim
  | persistent => simp [modelAt, valuation]
  | node m j => simp [modelAt, valuation]

theorem chi_iff_D (keep : Bool) (n : Nat) (x : OnePeeling.World) :
    (modelAt keep n).Satisfies x (chi false true) ↔
      (modelAt keep n).Satisfies x OnePeeling.D := by
  classical
  simp only [chi, OnePeeling.D, OnePeeling.L, Model.satisfies_or,
    Model.satisfies_and, Model.satisfies_dia, Model.satisfies_neg,
    Model.satisfies_atom, Model.satisfies_verum, and_true]
  constructor
  · rintro (⟨hs, y, hy, ht⟩ | ⟨hs, y, hy, ht⟩)
    · exact Or.inl ⟨hs, y, hy, target_not_r keep n false x y hy, ht⟩
    · exact Or.inr ⟨hs, y, hy, target_not_r keep n true x y hy, ht⟩
  · rintro (⟨hs, y, hy, _, ht⟩ | ⟨hs, y, hy, _, ht⟩)
    · exact Or.inl ⟨hs, y, hy, ht⟩
    · exact Or.inr ⟨hs, y, hy, ht⟩

theorem node_chi_iff (keep : Bool) (n m : Nat) (j : Fin (m + 2)) :
    (modelAt keep n).Satisfies (.node m j) (chi false true) ↔
      n < m + 1 - j.val :=
  (chi_iff_D keep n (.node m j)).trans (node_D_iff keep n m j)

theorem node_has_loop (keep : Bool) (n m : Nat) (j : Fin (m + 2))
    (hn : n ≤ m + 1 - j.val) :
    ∃ a : Bool, (modelAt keep n).rel a (.node m j) (.node m j) := by
  by_cases hj : j.val % 2 = 0
  · exact ⟨false, rfl, hj, hn⟩
  · have hj' : j.val % 2 = 1 := by omega
    exact ⟨true, rfl, hj', hn⟩

theorem node_theta11_iff (keep : Bool) (n m : Nat) (j : Fin (m + 2))
    (hn : n ≤ m + 1 - j.val) :
    (modelAt keep n).Satisfies (.node m j) (theta11 false true) ↔
      n < m + 1 - j.val := by
  obtain ⟨a, ha⟩ := node_has_loop keep n m j hn
  have hi : a = false ∨ a = true := by cases a <;> simp
  exact (ReversalSeparations.completion_at_target (modelAt keep n)
    (modelAt_isK45 keep n) false true (chi false true) hi ha).trans
    (node_chi_iff keep n m j)

theorem iterate_theta11 (n : Nat) :
    (modelAt false 0).iterateUpdate (theta11 false true) n = modelAt false n :=
  iterate_eq_of_alive false (theta11 false true)
    (fun n m j hn => node_theta11_iff false n m j hn) (by simp) n

theorem root_chi_false (keep : Bool) (n : Nat) :
    ¬ (modelAt keep n).Satisfies .root (chi false true) := by
  intro h
  exact root_L_false keep n Formula.verum ((chi_iff_D keep n .root).mp h)

theorem root_theta11_initial : (modelAt false 0).Satisfies .root (theta11 false true) := by
  apply (Model.satisfies_or _ _ _ _).mpr
  right
  constructor
  · intro y hy
    cases y with
    | root => exact (no_root_target false 0 false .root hy).elim
    | persistent => cases ((root_persistent_iff false 0).mp hy)
    | node m j =>
        obtain ⟨hj, _⟩ := (root_head_iff false 0 m j).mp hy
        exact (node_chi_iff false 0 m j).mpr (by omega)
  · intro y hy
    exact (root_b_empty false 0 y hy).elim

theorem root_theta11_false_of_pos (n : Nat) (hn : 1 ≤ n) :
    ¬ (modelAt false n).Satisfies .root (theta11 false true) := by
  intro h
  rcases (Model.satisfies_or _ _ _ _).mp h with hc | hboxes
  · exact root_chi_false false n hc
  · let j : Fin (n - 1 + 2) := ⟨0, by omega⟩
    have hrel : (modelAt false n).rel false .root (.node (n - 1) j) :=
      (root_head_iff false n (n - 1) j).mpr ⟨rfl, by omega⟩
    have hc := hboxes.1 (.node (n - 1) j) hrel
    have := (node_chi_iff false n (n - 1) j).mp hc
    dsimp [j] at this
    omega

theorem node_theta00_iff (keep : Bool) (n m : Nat) (j : Fin (m + 2)) :
    (modelAt keep n).Satisfies (.node m j) (theta00 false true) ↔
      n < m + 1 - j.val := by
  have hr : ¬ (modelAt keep n).val 0 (.node m j) := by simp [modelAt, valuation]
  simp only [theta00, A, Model.satisfies_or, Model.satisfies_and, Model.satisfies_neg,
    Model.satisfies_atom, hr, not_false_eq_true, true_and, false_and, or_false]
  exact node_D_iff keep n m j

theorem iterate_theta00 (n : Nat) :
    (modelAt false 0).iterateUpdate (theta00 false true) n = modelAt false n :=
  iterate_eq false (theta00 false true)
    (fun n m j => node_theta00_iff false n m j) (by simp) n

theorem root_theta00_iff (keep : Bool) (n : Nat) :
    (modelAt keep n).Satisfies .root (theta00 false true) ↔
      ¬ (modelAt keep n).Satisfies .root (Y false true) := by
  have hr : (modelAt keep n).val 0 .root := by trivial
  simp [theta00, A, Model.satisfies_or, Model.Satisfies, hr]

theorem root_Y_initial : (modelAt false 0).Satisfies .root (Y false true) := by
  intro y hy
  cases y with
  | root => exact (no_root_target false 0 false .root hy).elim
  | persistent => cases ((root_persistent_iff false 0).mp hy)
  | node m j =>
      obtain ⟨hj, _⟩ := (root_head_iff false 0 m j).mp hy
      exact (Model.satisfies_or _ _ _ _).mpr (Or.inr ⟨by simp [modelAt, valuation],
        (node_D_iff false 0 m j).mpr (by omega)⟩)

theorem root_theta00_initial_false :
    ¬ (modelAt false 0).Satisfies .root (theta00 false true) := by
  intro h
  exact (root_theta00_iff false 0).mp h root_Y_initial

theorem root_theta00_true_of_pos (n : Nat) (hn : 1 ≤ n) :
    (modelAt false n).Satisfies .root (theta00 false true) := by
  apply (root_theta00_iff false n).mpr
  intro hY
  let j : Fin (n - 1 + 2) := ⟨0, by omega⟩
  have hrel : (modelAt false n).rel false .root (.node (n - 1) j) :=
    (root_head_iff false n (n - 1) j).mpr ⟨rfl, by omega⟩
  rcases (Model.satisfies_or _ _ _ _).mp (hY (.node (n - 1) j) hrel) with hr | hA
  · exact hr.elim
  · have := (node_D_iff false n (n - 1) j).mp hA.2
    dsimp [j] at this
    omega

end Countermodel

/-- The 11 witness is initially true and false at every positive finite stage. -/
theorem theta11_not_eventual : ¬ Eventual.{0} true true (theta11 false true) := by
  intro h
  obtain ⟨n, hn, hv⟩ := h (OnePeeling.modelAt false 0)
    (OnePeeling.modelAt_isK45 false 0) .root Countermodel.root_theta11_initial
  rw [Model.trace, Countermodel.iterate_theta11] at hv
  exact Countermodel.root_theta11_false_of_pos n hn hv

/-- The 00 witness is initially false and true at every positive finite stage. -/
theorem theta00_not_eventual : ¬ Eventual.{0} false false (theta00 false true) := by
  intro h
  obtain ⟨n, hn, hv⟩ := h (OnePeeling.modelAt false 0)
    (OnePeeling.modelAt_isK45 false 0) .root Countermodel.root_theta00_initial_false
  rw [Model.trace, Countermodel.iterate_theta00] at hv
  exact hv (Countermodel.root_theta00_true_of_pos n hn)

/-- Lemma 10, with its two explicit two-agent witnesses. -/
theorem ordinal_return_separations :
    (∃ φ : Formula Nat Bool, OrdinalStrongEventual.{0} true true φ ∧
      ¬ Eventual.{0} true true φ) ∧
    (∃ φ : Formula Nat Bool, OrdinalStrongEventual.{0} false false φ ∧
      ¬ Eventual.{0} false false φ) :=
  ⟨⟨theta11 false true, theta11_ordinalStrongEventual false true, theta11_not_eventual⟩,
    ⟨theta00 false true, theta00_ordinalStrongEventual false true, theta00_not_eventual⟩⟩

end OrdinalReturn
end EventualAndStrongEventualNotionsInPublicAnnouncements
