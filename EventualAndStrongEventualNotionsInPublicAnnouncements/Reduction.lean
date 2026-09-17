import ClassificationSigmaValidity.Expressivity
import EventualAndStrongEventualNotionsInPublicAnnouncements.Definitions

/-! The six BPAL reduction laws, including arbitrary nested BPAL formulas. -/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

namespace Reduction

variable (M : Model World Atom Agent) (R : Agent → World → World → Prop)
  (x : World) (φ ψ χ : BPALFormula Atom Agent)

theorem atom (p : Atom) :
    BPAL.Satisfies M R x (.announce φ (.atom p)) ↔ M.val p x := Iff.rfl

theorem neg :
    BPAL.Satisfies M R x (.announce φ (.neg ψ)) ↔
      ¬ BPAL.Satisfies M R x (.announce φ ψ) := Iff.rfl

theorem conj :
    BPAL.Satisfies M R x (.announce φ (.conj ψ χ)) ↔
      BPAL.Satisfies M R x (.announce φ ψ) ∧
      BPAL.Satisfies M R x (.announce φ χ) := Iff.rfl

theorem box (i : Agent) :
    BPAL.Satisfies M R x (.announce φ (.box i ψ)) ↔
      ∀ y, R i x y → BPAL.Satisfies M R y φ →
        BPAL.Satisfies M R y (.announce φ ψ) := by
  simp only [BPAL.Satisfies]
  exact ⟨fun h y hy hφ => h y ⟨hy, hφ⟩,
    fun h y hy => h y hy.1 hy.2⟩

theorem diamond (i : Agent) :
    BPAL.Satisfies M R x (.announce φ (.neg (.box i (.neg ψ)))) ↔
      ∃ y, R i x y ∧ BPAL.Satisfies M R y φ ∧
        BPAL.Satisfies M R y (.announce φ ψ) := by
  classical
  simp only [BPAL.Satisfies, not_forall, not_not]
  exact ⟨fun ⟨y, ⟨hy, hφ⟩, hψ⟩ => ⟨y, hy, hφ, hψ⟩,
    fun ⟨y, hy, hφ, hψ⟩ => ⟨y, ⟨hy, hφ⟩, hψ⟩⟩

theorem composition :
    BPAL.Satisfies M R x (.announce φ (.announce ψ χ)) ↔
      BPAL.Satisfies M R x (.announce (.conj φ (.announce φ ψ)) χ) := by
  change BPAL.Satisfies M
    (fun i y z => (R i y z ∧ BPAL.Satisfies M R z φ) ∧
      BPAL.Satisfies M (fun i y z => R i y z ∧ BPAL.Satisfies M R z φ) z ψ) x χ ↔
    BPAL.Satisfies M
    (fun i y z => R i y z ∧ (BPAL.Satisfies M R z φ ∧
      BPAL.Satisfies M (fun i y z => R i y z ∧ BPAL.Satisfies M R z φ) z ψ)) x χ
  have hR : (fun i y z => (R i y z ∧ BPAL.Satisfies M R z φ) ∧
      BPAL.Satisfies M (fun i y z => R i y z ∧ BPAL.Satisfies M R z φ) z ψ) =
    (fun i y z => R i y z ∧ (BPAL.Satisfies M R z φ ∧
      BPAL.Satisfies M (fun i y z => R i y z ∧ BPAL.Satisfies M R z φ) z ψ)) := by
    funext i y z
    exact propext and_assoc
  rw [hR]

end Reduction

/-- The self-fulfilling sentence in Example 1 is a one-step true lie. -/
theorem selfFulfilling_trueLie (M : Model World Atom Agent) (hM : IsK45 M)
    (x : World) (p : Atom) (i : Agent)
    (h : ¬ M.Satisfies x (Formula.or (.atom p) (.box i (.atom p)))) :
    (M.update (Formula.or (.atom p) (.box i (.atom p)))).Satisfies x
      (Formula.or (.atom p) (.box i (.atom p))) := by
  rw [Model.satisfies_or] at h ⊢
  apply Or.inr
  intro y hy
  rcases (M.satisfies_or y _ _).mp hy.2 with hp | hb
  · exact hp
  · exact False.elim (h (Or.inr ((Model.modalAgreement_box hM hy.1 (.atom p)).mpr hb)))

end EventualAndStrongEventualNotionsInPublicAnnouncements
