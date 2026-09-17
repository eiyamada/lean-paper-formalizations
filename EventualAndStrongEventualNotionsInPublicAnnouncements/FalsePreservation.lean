import EventualAndStrongEventualNotionsInPublicAnnouncements.Definitions

/-!
# Global membership facts for the false-preserving separation witnesses

The formulas and positive membership assertions of Lemma
`lem:two-agent-00-limit-loss-separations`. The atoms `r`, `t`, and `s` are
represented by `0`, `1`, and `2`. No assumption that the two agents differ is
needed for these membership assertions.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements
namespace FalsePreservation

open ClassificationSigmaValidity

universe u w
variable {Agent : Type w} {World : Type u}

def W : Formula Nat Agent := .conj (.neg (.atom 0)) (.neg (.atom 1))
def T : Formula Nat Agent := .conj (.neg (.atom 0)) (.atom 1)
def D (a b : Agent) : Formula Nat Agent :=
  .or (.conj (.atom 2) (.dia a (.conj W (.neg (.atom 2)))))
    (.conj (.neg (.atom 2)) (.dia b (.conj W (.atom 2))))
def F (a b : Agent) : Formula Nat Agent := .dia a (.conj W (D a b))
def B (a b : Agent) : Formula Nat Agent := .dia a (.conj W (.neg (D a b)))
def N (a : Agent) : Formula Nat Agent := .box a (.neg W)
def U (a : Agent) : Formula Nat Agent := .dia a T
def K (a b : Agent) : Formula Nat Agent := .or (F a b) (.conj (N a) (U a))

/-- The Boolean selects the finite-stage variant when it is true. -/
def theta (finite : Bool) (a b : Agent) : Formula Nat Agent :=
  .or (.or (.conj W (D a b)) (.conj T (K a b)))
    (.conj (.atom 0)
      (if finite then .or (B a b) (.conj (N a) (U a)) else .conj (N a) (U a)))

def theta00SE (a b : Agent) : Formula Nat Agent := theta false a b
def theta00fin (a b : Agent) : Formula Nat Agent := theta true a b

theorem theta_at_W (M : Model World Nat Agent) (finite : Bool) (a b : Agent)
    (x : World) (hW : M.Satisfies x W) :
    M.Satisfies x (theta finite a b) ↔ M.Satisfies x (D a b) := by
  have hr : ¬ M.val 0 x := hW.1
  have ht : ¬ M.val 1 x := hW.2
  cases finite <;>
    simp [theta, W, T, Model.Satisfies, Model.satisfies_or, hr, ht]

theorem theta_at_T (M : Model World Nat Agent) (finite : Bool) (a b : Agent)
    (x : World) (hT : M.Satisfies x T) :
    M.Satisfies x (theta finite a b) ↔ M.Satisfies x (K a b) := by
  have hr : ¬ M.val 0 x := hT.1
  have ht : M.val 1 x := hT.2
  cases finite <;>
    simp [theta, W, T, Model.Satisfies, Model.satisfies_or, hr, ht]

theorem D_backward_update (M : Model World Nat Agent) (φ : Formula Nat Agent)
    (a b : Agent) (x : World) :
    (M.update φ).Satisfies x (D a b) → M.Satisfies x (D a b) := by
  simp only [D, Model.satisfies_or, Model.satisfies_and, Model.satisfies_dia,
    Model.satisfies_neg, Model.satisfies_atom, Model.update_rel, Model.update_val]
  rintro (⟨hs, y, ⟨hxy, _⟩, hW, hns⟩ | ⟨hns, y, ⟨hxy, _⟩, hW, hs⟩)
  · exact Or.inl ⟨hs, y, hxy, hW, hns⟩
  · exact Or.inr ⟨hns, y, hxy, hW, hs⟩

theorem F_backward_update (M : Model World Nat Agent) (φ : Formula Nat Agent)
    (a b : Agent) (x : World) :
    (M.update φ).Satisfies x (F a b) → M.Satisfies x (F a b) := by
  simp only [F, Model.satisfies_dia, Model.satisfies_and]
  rintro ⟨y, hxy, hW, hD⟩
  exact ⟨y, hxy.1, hW, D_backward_update M φ a b y hD⟩

theorem K_agreement (M : Model World Nat Agent) (hM : IsK45 M)
    (a b : Agent) {x y : World} (hxy : M.rel a x y) :
    M.Satisfies x (K a b) ↔ M.Satisfies y (K a b) := by
  simp only [K, Model.satisfies_or, Model.satisfies_and]
  exact or_congr (Model.modalAgreement_dia hM hxy (.conj W (D a b)))
    (and_congr (Model.modalAgreement_box hM hxy (.neg W))
      (Model.modalAgreement_dia hM hxy T))

/-- The conjunction `N ∧ U` cannot first become true at a successor update. -/
theorem NU_backward_update (M : Model World Nat Agent) (hM : IsK45 M)
    (finite : Bool) (a b : Agent) (x : World)
    (hN : (M.update (theta finite a b)).Satisfies x (N a))
    (hU : (M.update (theta finite a b)).Satisfies x (U a)) :
    M.Satisfies x (N a) ∧ M.Satisfies x (U a) := by
  obtain ⟨y, hxy, hTy⟩ := (Model.satisfies_dia _ _ _ _).mp hU
  have hKy : M.Satisfies y (K a b) :=
    (theta_at_T M finite a b y hTy).mp hxy.2
  have hKx := (K_agreement M hM a b hxy.1).mpr hKy
  rcases (Model.satisfies_or _ _ _ _).mp hKx with hF | hNU
  · obtain ⟨z, hxz, hWz, hDz⟩ := (Model.satisfies_dia _ _ _ _).mp hF
    have hφz := (theta_at_W M finite a b z hWz).mpr hDz
    exact False.elim (hN z ⟨hxz, hφz⟩ hWz)
  · exact hNU

/-- In fact `K` itself cannot first become true under either announcement. -/
theorem K_backward_update (M : Model World Nat Agent) (hM : IsK45 M)
    (finite : Bool) (a b : Agent) (x : World) :
    (M.update (theta finite a b)).Satisfies x (K a b) → M.Satisfies x (K a b) := by
  intro hK
  rcases (Model.satisfies_or _ _ _ _).mp hK with hF | hNU
  · exact (Model.satisfies_or _ _ _ _).mpr
      (Or.inl (F_backward_update M (theta finite a b) a b x hF))
  · exact (Model.satisfies_or _ _ _ _).mpr
      (Or.inr (NU_backward_update M hM finite a b x hNU.1 hNU.2))

/-- The SE witness is backward persistent under either witness's update. -/
theorem theta00SE_backward_update (M : Model World Nat Agent) (hM : IsK45 M)
    (finite : Bool) (a b : Agent) (x : World) :
    (M.update (theta finite a b)).Satisfies x (theta00SE a b) →
      M.Satisfies x (theta00SE a b) := by
  simp only [theta00SE, theta, Bool.false_eq_true, ↓reduceIte,
    Model.satisfies_or, Model.satisfies_and, Model.satisfies_atom]
  rintro ((⟨hW, hD⟩ | ⟨hT, hK⟩) | ⟨hr, hN, hU⟩)
  · exact Or.inl (Or.inl ⟨hW, D_backward_update M (theta finite a b) a b x hD⟩)
  · exact Or.inl (Or.inr ⟨hT, K_backward_update M hM finite a b x hK⟩)
  · exact Or.inr ⟨hr, NU_backward_update M hM finite a b x hN hU⟩

theorem theta00SE_backward_iterate (M : Model World Nat Agent) (hM : IsK45 M)
    (finite : Bool) (a b : Agent) (x : World) (n : Nat) :
    (M.iterateUpdate (theta finite a b) n).Satisfies x (theta00SE a b) →
      M.Satisfies x (theta00SE a b) := by
  induction n with
  | zero => exact id
  | succ n ih =>
      intro hn
      exact ih (theta00SE_backward_update (M.iterateUpdate (theta finite a b) n)
        (Model.iterateUpdate_isK45 hM _ n) finite a b x hn)

/-- The first witness is already an impossible lie, hence strongly eventual 00. -/
theorem theta00SE_strongEventual (a b : Agent) :
    StrongEventual.{u} false false (theta00SE a b) := by
  intro World M hM x hx
  refine ⟨1, le_rfl, fun n _ hn => ?_⟩
  exact hx (theta00SE_backward_iterate M hM false a b x n hn)

theorem theta00fin_decomposition (M : Model World Nat Agent) (a b : Agent)
    (x : World) :
    M.Satisfies x (theta00fin a b) ↔
      M.Satisfies x (theta00SE a b) ∨ (M.val 0 x ∧ M.Satisfies x (B a b)) := by
  simp only [theta00fin, theta00SE, theta, Bool.false_eq_true,
    ↓reduceIte, Model.satisfies_or, Model.satisfies_and, Model.satisfies_atom]
  constructor
  · rintro (h | ⟨hr, hB | hNU⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨hr, hB⟩
    · exact Or.inl (Or.inr ⟨hr, hNU⟩)
  · rintro (h | ⟨hr, hB⟩)
    · rcases h with h | ⟨hr, hNU⟩
      · exact Or.inl h
      · exact Or.inr ⟨hr, Or.inr hNU⟩
    · exact Or.inr ⟨hr, Or.inl hB⟩

/-- A newly true finite-stage witness has a false direct successor. -/
theorem theta00fin_finiteStageCondition (a b : Agent) :
    FiniteStageCondition.{u} false false (theta00fin a b) := by
  intro n World M hM x hx hC hn
  rcases (theta00fin_decomposition (M.iterateUpdate (theta00fin a b) n) a b x).mp hn
    with hSE | ⟨_, hB⟩
  · have hSE0 := theta00SE_backward_iterate M hM true a b x n hSE
    exact hx ((theta00fin_decomposition M a b x).mpr (Or.inl hSE0))
  · obtain ⟨y, hxy, hW, hnD⟩ := (Model.satisfies_dia _ _ _ _).mp hB
    have hy := hC y (Relation.TransGen.single ⟨a, hxy⟩)
    exact hnD ((theta_at_W (M.iterateUpdate (theta00fin a b) n) true a b y hW).mp hy)

end FalsePreservation
end EventualAndStrongEventualNotionsInPublicAnnouncements
