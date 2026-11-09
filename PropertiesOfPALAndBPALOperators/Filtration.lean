import ClassificationSigmaValidity.FiniteModelProperty

/-!
# Minimal filtration over arbitrary frames

The filtration in the earlier paper preserves K45. Here the existential
quotient relation is needed for arbitrary K frames, and preserves every
original edge. This supplies the finite countermodel step in Theorem 28.
-/

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity

universe u v w

namespace MinimalFiltration

variable {World : Type u} {Atom : Type v} {Agent : Type w}

abbrev WorldType (M : Model World Atom Agent) (φ : Formula Atom Agent) :=
  Filtration.FilteredWorld M φ

def point (M : Model World Atom Agent) (φ : Formula Atom Agent) (x : World) :
    WorldType M φ := Quotient.mk (Filtration.setoid M φ) x

noncomputable def model (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    Model (WorldType M φ) Atom Agent where
  rel i a b := ∃ x y, point M φ x = a ∧ point M φ y = b ∧ M.rel i x y
  val p a := M.val p a.out

theorem representative_agrees (M : Model World Atom Agent) (φ : Formula Atom Agent)
    {x : World} {a : WorldType M φ} (h : point M φ x = a)
    {ψ : Formula Atom Agent} (hψ : ψ ∈ φ.subformulas) :
    M.Satisfies x ψ ↔ M.Satisfies a.out ψ := by
  subst a
  exact (Filtration.out_mk_satisfies_iff M φ x ψ hψ).symm

theorem original_edge (M : Model World Atom Agent) (φ : Formula Atom Agent)
    {i : Agent} {x y : World} (h : M.rel i x y) :
    (model M φ).rel i (point M φ x) (point M φ y) :=
  ⟨x, y, rfl, rfl, h⟩

theorem truth (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (a : WorldType M φ) (ψ : Formula Atom Agent) (hψ : ψ ∈ φ.subformulas) :
    (model M φ).Satisfies a ψ ↔ M.Satisfies a.out ψ := by
  induction ψ generalizing a with
  | atom p => rfl
  | neg ψ ih =>
      exact not_congr (ih a (Formula.mem_subformulas_of_mem hψ (by
        simp [Formula.subformulas])))
  | conj ψ χ ihψ ihχ =>
      exact and_congr
        (ihψ a (Formula.mem_subformulas_of_mem hψ (by simp [Formula.subformulas])))
        (ihχ a (Formula.mem_subformulas_of_mem hψ (by simp [Formula.subformulas])))
  | box i ψ ih =>
      have hsub : ψ ∈ φ.subformulas :=
        Formula.mem_subformulas_of_mem hψ (by simp [Formula.subformulas])
      constructor
      · intro h y hay
        have hy := h (point M φ y) ⟨a.out, y, Quotient.out_eq a, rfl, hay⟩
        exact (representative_agrees M φ rfl hsub).mpr
          ((ih (point M φ y) hsub).mp hy)
      · intro h b hab
        obtain ⟨x, y, hx, hy, hxy⟩ := hab
        have hxbox := (representative_agrees M φ hx hψ).mpr h
        exact (ih b hsub).mpr
          ((representative_agrees M φ hy hsub).mp (hxbox y hxy))

theorem truth_point (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (x : World) :
    (model M φ).Satisfies (point M φ x) φ ↔ M.Satisfies x φ :=
  (truth M φ _ φ (Formula.mem_subformulas_self φ)).trans
    (representative_agrees M φ rfl (Formula.mem_subformulas_self φ)).symm

theorem globally_true (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (h : ∀ x, M.Satisfies x φ) : ∀ a, (model M φ).Satisfies a φ := by
  intro a
  exact (truth M φ a φ (Formula.mem_subformulas_self φ)).mpr (h a.out)

theorem targets_true (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (h : ∀ i x y, M.rel i x y → M.Satisfies y φ) :
    ∀ i a b, (model M φ).rel i a b → (model M φ).Satisfies b φ := by
  rintro i a b ⟨x, y, hx, hy, hxy⟩
  rw [← hy]
  exact (truth_point M φ y).mpr (h i x y hxy)

end MinimalFiltration

end PropertiesOfPALAndBPALOperators
