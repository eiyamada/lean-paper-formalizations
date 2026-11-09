import PropertiesOfPALAndBPALOperators.Algebra
import PropertiesOfPALAndBPALOperators.Extinction

/-! The over-K forms of Proposition 21. The converse for BPAL genuinely
quantifies over every world type: adding a fresh predecessor removes the
incoming-arrow guard in the modelwise characterization. -/

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity

universe u v w
variable {Atom : Type v} {Agent : Type w}

theorem bpal_all_targets_iff_valid [Nonempty Agent] (δ : BPALFormula Atom Agent) :
    (∀ (W : Type u) (M : Model W Atom Agent) i x y,
      M.rel i x y → BPAL.InitiallySatisfies M y δ) ↔
    (∀ (W : Type u) (M : Model W Atom Agent) y, BPAL.InitiallySatisfies M y δ) := by
  constructor
  · intro h W M y
    obtain ⟨i⟩ := ‹Nonempty Agent›
    let N := Extinction.predecessor M y i
    have hd := h (Option W) N i none (some y) ⟨rfl, rfl⟩
    apply (BPAL.initiallySatisfies_toFormula M y δ).mpr
    apply (Extinction.predecessor_truth M y i y δ.toFormula).mp
    exact (BPAL.initiallySatisfies_toFormula N (some y) δ).mp hd
  · exact fun h W M _ _ y _ => h W M y

/-- Proposition 21(2), full BPAL equivalence over K, for dynamic formulas. -/
theorem bpal_global_idempotent_iff_success [Nonempty Agent]
    (φ : BPALFormula Atom Agent) :
    (∀ (W : Type u) (M : Model W Atom Agent),
      bpalUpdate M φ (bpalUpdate M φ M.rel) = bpalUpdate M φ M.rel) ↔
    (∀ (W : Type u) (M : Model W Atom Agent) x,
      BPAL.Satisfies M M.rel x φ → BPAL.Satisfies M (bpalUpdate M φ M.rel) x φ) := by
  simp only [bpal_idempotent_iff_target_success]
  have h := bpal_all_targets_iff_valid.{u, v, w}
    (.neg (.conj φ (.neg (.announce φ φ))))
  simpa only [BPAL.InitiallySatisfies, BPAL.Satisfies, not_and, not_not,
    bpalUpdate] using h

/-- Proposition 21(3), full BPAL equivalence over K. -/
theorem bpal_global_square_zero_iff_selfRefuting [Nonempty Agent]
    (φ : BPALFormula Atom Agent) :
    (∀ (W : Type u) (M : Model W Atom Agent),
      bpalUpdate M φ (bpalUpdate M φ M.rel) = (fun _ _ _ => False)) ↔
    (∀ (W : Type u) (M : Model W Atom Agent) x,
      BPAL.Satisfies M M.rel x φ → ¬ BPAL.Satisfies M (bpalUpdate M φ M.rel) x φ) := by
  simp only [bpal_square_zero_iff]
  have h := bpal_all_targets_iff_valid.{u, v, w} (.neg (.conj φ (.announce φ φ)))
  simpa only [BPAL.InitiallySatisfies, BPAL.Satisfies, not_and, bpalUpdate] using h

/-- The same idempotence equivalence expressed using equality of actual
updated models, rather than their fixed-valuation relation representation. -/
theorem bpal_global_model_idempotent_iff_success [Nonempty Agent]
    (φ : BPALFormula Atom Agent) :
    (∀ (W : Type u) (M : Model W Atom Agent),
      bpalUpdateModel (bpalUpdateModel M φ) φ = bpalUpdateModel M φ) ↔
    (∀ (W : Type u) (M : Model W Atom Agent) x,
      BPAL.Satisfies M M.rel x φ → BPAL.Satisfies M (bpalUpdate M φ M.rel) x φ) := by
  simp only [bpalUpdateModel_composition_eq_iff]
  exact bpal_global_idempotent_iff_success φ

end PropertiesOfPALAndBPALOperators
