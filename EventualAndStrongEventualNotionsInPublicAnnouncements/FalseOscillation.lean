import EventualAndStrongEventualNotionsInPublicAnnouncements.FiniteConditions
import EventualAndStrongEventualNotionsInPublicAnnouncements.PeelingModels

/-!
# An eventual impossible lie with an oscillating trace

The formula and reductions of Lemma `lem:two-agent-e00-oscillation`.
The reduction argument is valid on arbitrary frames.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements
namespace FalseOscillation

open ClassificationSigmaValidity

universe u w
variable {Agent : Type w} {World : Type u}

/-- Atoms 0,2,3 denote r,s,p, matching the common peeling models. -/
def L (a b : Agent) (χ : Formula Nat Agent) : Formula Nat Agent :=
  .or (.conj (.atom 2) (.dia a (.conj (.neg (.atom 0)) (.conj (.neg (.atom 2)) χ))))
    (.conj (.neg (.atom 2)) (.dia b (.conj (.neg (.atom 0)) (.conj (.atom 2) χ))))

def D (a b : Agent) : Nat → Formula Nat Agent
  | 0 => .verum
  | k + 1 => L a b (D a b k)

def H (a b : Agent) (k : Nat) : Formula Nat Agent :=
  .conj (D a b k) (.neg (D a b (k + 1)))

def X (a b : Agent) (k : Nat) : Formula Nat Agent :=
  .dia a (.conj (.neg (.atom 0))
    (.conj (.neg (.atom 2)) (.conj (.atom 3) (H a b k))))

def theta (a b : Agent) : Formula Nat Agent :=
  .or (.conj (.neg (.atom 0)) (D a b 1))
    (.conj (.atom 0) (.conj (X a b 1) (.neg (X a b 2))))

def Step (a b : Agent) (M : Model World Nat Agent) (x y : World) : Prop :=
  ¬ M.val 0 y ∧
    ((M.val 2 x ∧ M.rel a x y ∧ ¬ M.val 2 y) ∨
      (¬ M.val 2 x ∧ M.rel b x y ∧ M.val 2 y))

theorem L_iff (a b : Agent) (M : Model World Nat Agent) (x : World)
    (χ : Formula Nat Agent) :
    M.Satisfies x (L a b χ) ↔ ∃ y, Step a b M x y ∧ M.Satisfies y χ := by
  simp only [L, Model.satisfies_or, Model.satisfies_and, Model.satisfies_dia,
    Model.satisfies_neg, Model.satisfies_atom]
  constructor
  · rintro (⟨hs, y, hr, hnr, hns, hχ⟩ | ⟨hns, y, hr, hnr, hs, hχ⟩)
    · exact ⟨y, ⟨hnr, Or.inl ⟨hs, hr, hns⟩⟩, hχ⟩
    · exact ⟨y, ⟨hnr, Or.inr ⟨hns, hr, hs⟩⟩, hχ⟩
  · rintro ⟨y, ⟨hnr, hstep⟩, hχ⟩
    rcases hstep with ⟨hs, hr, hns⟩ | ⟨hns, hr, hs⟩
    · exact Or.inl ⟨hs, y, hr, hnr, hns, hχ⟩
    · exact Or.inr ⟨hns, y, hr, hnr, hs, hχ⟩

theorem D_succ_iff (a b : Agent) (M : Model World Nat Agent) (x : World)
    (k : Nat) : M.Satisfies x (D a b (k + 1)) ↔
      ∃ y, Step a b M x y ∧ M.Satisfies y (D a b k) :=
  L_iff a b M x (D a b k)

theorem D_positive_implies_D_one (a b : Agent) (M : Model World Nat Agent)
    (x : World) (k : Nat) (h : M.Satisfies x (D a b (k + 1))) :
    M.Satisfies x (D a b 1) := by
  obtain ⟨y, hy, _⟩ := (D_succ_iff a b M x k).mp h
  exact (D_succ_iff a b M x 0).mpr ⟨y, hy, Model.satisfies_verum M y⟩

theorem theta_nonroot (a b : Agent) (M : Model World Nat Agent) (x : World)
    (hx : ¬ M.val 0 x) : M.Satisfies x (theta a b) ↔ M.Satisfies x (D a b 1) := by
  simp [theta, hx]

theorem theta_root (a b : Agent) (M : Model World Nat Agent) (x : World)
    (hx : M.val 0 x) : M.Satisfies x (theta a b) ↔
      M.Satisfies x (X a b 1) ∧ ¬ M.Satisfies x (X a b 2) := by
  simp [theta, hx]

theorem step_update_iff (a b : Agent) (M : Model World Nat Agent) (x y : World)
    (φ : Formula Nat Agent) :
    Step a b (M.update φ) x y ↔ Step a b M x y ∧ M.Satisfies y φ := by
  constructor
  · rintro ⟨hnr, hstep⟩
    rcases hstep with ⟨hs, ⟨hr, hφ⟩, hns⟩ | ⟨hns, ⟨hr, hφ⟩, hs⟩
    · exact ⟨⟨hnr, Or.inl ⟨hs, hr, hns⟩⟩, hφ⟩
    · exact ⟨⟨hnr, Or.inr ⟨hns, hr, hs⟩⟩, hφ⟩
  · rintro ⟨⟨hnr, hstep⟩, hφ⟩
    rcases hstep with ⟨hs, hr, hns⟩ | ⟨hns, hr, hs⟩
    · exact ⟨hnr, Or.inl ⟨hs, ⟨hr, hφ⟩, hns⟩⟩
    · exact ⟨hnr, Or.inr ⟨hns, ⟨hr, hφ⟩, hs⟩⟩

/-- Announcing the witness shifts every positive path-depth test by one. -/
theorem update_D (a b : Agent) (M : Model World Nat Agent) (x : World) (k : Nat) :
    (M.update (theta a b)).Satisfies x (D a b (k + 1)) ↔
      M.Satisfies x (D a b (k + 2)) := by
  induction k generalizing x with
  | zero =>
    rw [D_succ_iff a b (M.update (theta a b)) x 0, D_succ_iff a b M x 1]
    constructor
    · rintro ⟨y, hy, _⟩
      obtain ⟨hy, hθ⟩ := (step_update_iff a b M x y (theta a b)).mp hy
      exact ⟨y, hy, (theta_nonroot a b M y hy.1).mp hθ⟩
    · rintro ⟨y, hy, hD⟩
      exact ⟨y, (step_update_iff a b M x y (theta a b)).mpr
        ⟨hy, (theta_nonroot a b M y hy.1).mpr hD⟩,
        Model.satisfies_verum _ _⟩
  | succ k ih =>
    rw [D_succ_iff a b (M.update (theta a b)) x (k + 1),
      D_succ_iff a b M x (k + 2)]
    constructor
    · rintro ⟨y, hy, hD⟩
      exact ⟨y, ((step_update_iff a b M x y (theta a b)).mp hy).1, (ih y).mp hD⟩
    · rintro ⟨y, hy, hD⟩
      refine ⟨y, (step_update_iff a b M x y (theta a b)).mpr ⟨hy, ?_⟩,
        (ih y).mpr hD⟩
      exact (theta_nonroot a b M y hy.1).mpr
        (D_positive_implies_D_one a b M y (k + 1) hD)

theorem update_H (a b : Agent) (M : Model World Nat Agent) (x : World) (k : Nat) :
    (M.update (theta a b)).Satisfies x (H a b (k + 1)) ↔
      M.Satisfies x (H a b (k + 2)) := by
  simp only [H, Model.satisfies_and, Model.satisfies_neg,
    update_D a b M x k, update_D a b M x (k + 1)]

theorem update_X (a b : Agent) (M : Model World Nat Agent) (x : World) (k : Nat) :
    (M.update (theta a b)).Satisfies x (X a b (k + 1)) ↔
      M.Satisfies x (X a b (k + 2)) := by
  simp only [X, Model.satisfies_dia, Model.satisfies_and, Model.satisfies_neg,
    Model.satisfies_atom, Model.update_rel]
  constructor
  · rintro ⟨y, ⟨hxy, _⟩, hnr, hns, hp, hH⟩
    exact ⟨y, hxy, hnr, hns, hp, (update_H a b M y k).mp hH⟩
  · rintro ⟨y, hxy, hnr, hns, hp, hH⟩
    have hD : M.Satisfies y (D a b 1) :=
      D_positive_implies_D_one a b M y (k + 1) hH.1
    exact ⟨y, ⟨hxy, (theta_nonroot a b M y hnr).mpr hD⟩,
      hnr, hns, hp, (update_H a b M y k).mpr hH⟩

/-- Every initially false instance is false again after one or two updates. -/
theorem eventual_impossible_lie (a b : Agent) : Eventual.{u} false false (theta a b) := by
  classical
  intro W M _ x hx
  by_cases hr : M.val 0 x
  · by_cases hnext : (M.update (theta a b)).Satisfies x (theta a b)
    · refine ⟨2, by omega, ?_⟩
      have hNX : ¬ (M.update (theta a b)).Satisfies x (X a b 2) :=
        ((theta_root a b (M.update (theta a b)) x hr).mp hnext).2
      have hnX : ¬ ((M.update (theta a b)).update (theta a b)).Satisfies x
          (X a b 1) := fun h => hNX ((update_X a b (M.update (theta a b)) x 0).mp h)
      intro ht
      exact hnX ((theta_root a b ((M.update (theta a b)).update (theta a b)) x hr).mp ht).1
    · exact ⟨1, le_rfl, hnext⟩
  · refine ⟨1, le_rfl, ?_⟩
    intro hnext
    have hD := (theta_nonroot a b (M.update (theta a b)) x hr).mp hnext
    have hDtwo := (update_D a b M x 0).mp hD
    exact hx ((theta_nonroot a b M x hr).mpr
      (D_positive_implies_D_one a b M x 1 hDtwo))

/-- Repeated reductions shift X by the number of announcements. -/
theorem iterate_X (a b : Agent) (M : Model World Nat Agent) (x : World)
    (n k : Nat) :
    (M.iterateUpdate (theta a b) n).Satisfies x (X a b (k + 1)) ↔
      M.Satisfies x (X a b (n + k + 1)) := by
  induction n generalizing k with
  | zero => simp only [Model.iterateUpdate_zero, Nat.zero_add]
  | succ n ih =>
    rw [Model.iterateUpdate_succ, update_X]
    have h := ih (k + 1)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

open OnePeeling in
theorem node_D_initial (m : Nat) (j : Fin (m + 2)) (k : Nat) :
    (modelAt false 0).Satisfies (.node m j) (D false true k) ↔
      k ≤ m + 1 - j.val := by
  induction k generalizing j with
  | zero => simp [D]
  | succ k ih =>
    change (modelAt false 0).Satisfies (.node m j)
      (OnePeeling.L (D false true k)) ↔ _
    rw [node_L_iff]
    constructor
    · rintro ⟨l, hl, _, hD⟩
      have hDl := (ih l).mp hD
      have hj := j.isLt
      have hll := l.isLt
      omega
    · intro hk
      let l : Fin (m + 2) := ⟨j.val + 1, by omega⟩
      refine ⟨l, rfl, Nat.zero_le _, (ih l).mpr ?_⟩
      dsimp [l]
      omega

open OnePeeling in
theorem node_H_initial (m : Nat) (j : Fin (m + 2)) (k : Nat) :
    (modelAt false 0).Satisfies (.node m j) (H false true k) ↔
      k = m + 1 - j.val := by
  simp only [H, Model.satisfies_and, Model.satisfies_neg, node_D_initial]
  omega

open OnePeeling in
theorem root_X_initial (k : Nat) (hk : 1 ≤ k) :
    (modelAt false 0).Satisfies .root (X false true k) ↔ k % 2 = 0 := by
  rw [X, Model.satisfies_dia]
  constructor
  · rintro ⟨y, hy, hχ⟩
    cases y with
    | root => exact (no_root_target false 0 false .root hy).elim
    | persistent =>
      have hf : (false : Bool) = true := (root_persistent_iff false 0).mp hy
      cases hf
    | node m j =>
      have hj := ((root_head_iff false 0 m j).mp hy).1
      have hp : j.val = 0 ∧ (m + 1) % 2 = 0 := hχ.2.2.1
      have hH := (node_H_initial m j k).mp hχ.2.2.2
      simpa only [hj, Nat.sub_zero, hH] using hp.2
  · intro hp
    let j : Fin ((k - 1) + 2) := ⟨0, by omega⟩
    have hkm : k - 1 + 1 = k := by omega
    refine ⟨.node (k - 1) j,
      (root_head_iff false 0 (k - 1) j).mpr ⟨rfl, Nat.zero_le _⟩, ?_⟩
    refine ⟨?_, ?_, ?_, (node_H_initial (k - 1) j k).mpr ?_⟩
    · simp [Model.Satisfies, modelAt, valuation]
    · simp [Model.Satisfies, modelAt, valuation, j]
    · change j.val = 0 ∧ (k - 1 + 1) % 2 = 0
      exact ⟨rfl, by simpa only [hkm] using hp⟩
    · change k = k - 1 + 1
      omega

/-- The actual root trace is false, true, false, true, and so on. -/
theorem root_trace_iff (n : Nat) :
    (OnePeeling.modelAt false 0).trace .root (theta false true) n ↔ n % 2 = 1 := by
  unfold Model.trace
  have hr : ((OnePeeling.modelAt false 0).iterateUpdate (theta false true) n).val
      0 .root := by
    rw [Model.iterateUpdate_val]
    trivial
  rw [theta_root false true
    ((OnePeeling.modelAt false 0).iterateUpdate (theta false true) n) .root hr,
    iterate_X, iterate_X]
  rw [root_X_initial (n + 0 + 1) (by omega), root_X_initial (n + 1 + 1) (by omega)]
  omega

theorem not_strongEventual_impossible_lie :
    ¬ StrongEventual.{0} false false (theta false true) := by
  intro h
  have hzero : ¬ (OnePeeling.modelAt false 0).Satisfies .root (theta false true) := by
    change ¬ (OnePeeling.modelAt false 0).trace .root (theta false true) 0
    rw [root_trace_iff]
    decide
  obtain ⟨N, _, htail⟩ := h (OnePeeling.modelAt false 0)
    (OnePeeling.modelAt_isK45 false 0) .root hzero
  have hn : N ≤ 2 * N + 1 := by omega
  have htrue := (root_trace_iff (2 * N + 1)).mpr (by omega)
  exact htail (2 * N + 1) hn htrue

/-- Lemma 9 for the two named agents. -/
theorem impossible_lie_separation :
    ∃ φ : Formula Nat Bool, Eventual.{0} false false φ ∧
      ¬ StrongEventual.{0} false false φ :=
  ⟨theta false true, eventual_impossible_lie false true, not_strongEventual_impossible_lie⟩

end FalseOscillation
end EventualAndStrongEventualNotionsInPublicAnnouncements
