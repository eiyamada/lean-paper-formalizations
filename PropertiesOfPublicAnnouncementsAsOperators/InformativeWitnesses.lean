import PropertiesOfPublicAnnouncementsAsOperators.S5OrdinalWitness
import PropertiesOfPublicAnnouncementsAsOperators.Extinction

/-! The remark following Theorem 28: always being informative when true
places no uniform bound on ordinal stabilization ranks. -/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u

theorem ordinalWitness_unknowable :
    Extinction.CommonlyUnknowable.{u} OrdinalWitness.formula := by
  intro W M x ⟨hφ, hc⟩
  obtain ⟨hp, y, hxy, hpy, hybox⟩ :=
    (show M.Satisfies x (.atom ()) ∧
      ∃ y, M.rel () x y ∧ M.Satisfies y (.atom ()) ∧
        M.Satisfies y (.box () (.neg (.atom ()))) from
      by simpa only [OrdinalWitness.formula, Model.satisfies_and,
        Model.satisfies_dia] using hφ)
  have hyφ := hc y (Relation.TransGen.single ⟨(), hxy⟩)
  obtain ⟨_, z, hyz, hpz, _⟩ :=
    (show M.Satisfies y (.atom ()) ∧
      ∃ z, M.rel () y z ∧ M.Satisfies z (.atom ()) ∧
        M.Satisfies z (.box () (.neg (.atom ()))) from
      by simpa only [OrdinalWitness.formula, Model.satisfies_and,
        Model.satisfies_dia] using hyφ)
  exact hybox z hyz hpz

theorem s5Witness_L_mono {W : Type u} (M : Model W Unit Bool)
    (x : W) (φ ψ : Formula Unit Bool)
    (h : ∀ y, M.Satisfies y φ → M.Satisfies y ψ) :
    M.Satisfies x (S5OrdinalWitness.L φ) → M.Satisfies x (S5OrdinalWitness.L ψ) := by
  intro hx
  simp only [S5OrdinalWitness.L, Model.satisfies_or, Model.satisfies_and,
    Model.satisfies_dia] at hx ⊢
  rcases hx with ⟨hp, y, hxy, hnp, hy⟩ | ⟨hnp, y, hxy, hp, hy⟩
  · exact Or.inl ⟨hp, y, hxy, hnp, h y hy⟩
  · exact Or.inr ⟨hnp, y, hxy, hp, h y hy⟩

theorem s5Witness_formula_implies_delta {W : Type u} (M : Model W Unit Bool) (x : W) :
    M.Satisfies x S5OrdinalWitness.formula → M.Satisfies x S5OrdinalWitness.delta :=
  s5Witness_L_mono M x _ _ (fun y _ => Model.satisfies_verum M y)

theorem s5Witness_false_target {W : Type u} (M : Model W Unit Bool) (x : W)
    (h : M.Satisfies x S5OrdinalWitness.formula) :
    ∃ i y, M.rel i x y ∧ ¬ M.Satisfies y S5OrdinalWitness.formula := by
  simp only [S5OrdinalWitness.formula, S5OrdinalWitness.L,
    Model.satisfies_or, Model.satisfies_and, Model.satisfies_dia] at h
  rcases h with ⟨_, y, hxy, _, hy⟩ | ⟨_, y, hxy, _, hy⟩
  · exact ⟨true, y, hxy, fun hφ => hy (s5Witness_formula_implies_delta M y hφ)⟩
  · exact ⟨false, y, hxy, fun hφ => hy (s5Witness_formula_implies_delta M y hφ)⟩

theorem s5Witness_unknowable :
    Extinction.CommonlyUnknowable.{u} S5OrdinalWitness.formula := by
  intro W M x ⟨hφ, hc⟩
  obtain ⟨i, y, hxy, hy⟩ := s5Witness_false_target M x hφ
  exact hy (hc y (Relation.TransGen.single ⟨i, hxy⟩))

theorem ordinalWitness_informative :
    Extinction.InformativeWhenTrue.{u} OrdinalWitness.formula :=
  (Extinction.unknowable_iff_informative OrdinalWitness.formula).mp ordinalWitness_unknowable

theorem s5Witness_informative :
    Extinction.InformativeWhenTrue.{u} S5OrdinalWitness.formula :=
  (Extinction.unknowable_iff_informative S5OrdinalWitness.formula).mp s5Witness_unknowable

/-- A single always-informative-when-true formula realizes every ordinal as
both its PAL and BPAL rank, even with S5 initial models and two agents. -/
theorem informative_s5_unbounded_ranks :
    Extinction.InformativeWhenTrue.{u} S5OrdinalWitness.formula ∧
      ∀ α : Ordinal.{u}, ∃ (W : Type u) (M : Model W Unit Bool), IsS5 M ∧
        palRank M S5OrdinalWitness.formula = α ∧ bpalRank M S5OrdinalWitness.formula = α := by
  refine ⟨s5Witness_informative, fun α => ?_⟩
  exact ⟨S5OrdinalWitness.World α, S5OrdinalWitness.model α,
    S5OrdinalWitness.model_isS5 α, S5OrdinalWitness.ranks_eq α⟩

/-- Renaming the one used atom and the two modalities preserves the
unknowability argument even in a larger atom/agent alphabet. -/
theorem s5Witness_many_unknowable {Atom Agent : Type} (p : Atom) (a b : Agent) :
    Extinction.CommonlyUnknowable.{u} (S5OrdinalWitness.formulaMany p a b) := by
  intro W M x ⟨hφ, hc⟩
  let N : Model W Unit Bool :=
    { rel := fun i y z => M.rel (if i then a else b) y z
      val := fun _ y => M.val p y }
  have ht (χ : Formula Unit Bool) (y : W) :
      N.Satisfies y χ ↔
        M.Satisfies y (χ.map (fun _ => p) (fun i => if i then a else b)) := by
    induction χ generalizing y with
    | atom q => rfl
    | neg χ ih => exact not_congr (ih y)
    | conj χ ψ ihχ ihψ => exact and_congr (ihχ y) (ihψ y)
    | box i χ ih =>
        apply forall_congr'; intro z
        exact imp_congr_right (fun _ => ih z)
  apply s5Witness_unknowable W N x
  refine ⟨(ht S5OrdinalWitness.formula x).mpr hφ, ?_⟩
  intro y hxy
  apply (ht S5OrdinalWitness.formula y).mpr
  apply hc y
  exact Relation.TransGen.mono (fun _ _ ⟨i, hi⟩ => ⟨if i then a else b, hi⟩) hxy

theorem s5Witness_many_informative {Atom Agent : Type} (p : Atom) (a b : Agent) :
    Extinction.InformativeWhenTrue.{u} (S5OrdinalWitness.formulaMany p a b) :=
  (Extinction.unknowable_iff_informative _).mp (s5Witness_many_unknowable p a b)

/-- The full arbitrary-alphabet version, including the paper's countably
infinite atom alphabet and any finite agent set containing two distinct agents. -/
theorem informative_s5_unbounded_ranks_many {Atom Agent : Type}
    (p : Atom) (a b : Agent) (hab : a ≠ b) :
    Extinction.InformativeWhenTrue.{u} (S5OrdinalWitness.formulaMany p a b) ∧
      ∀ α : Ordinal.{u}, ∃ (W : Type u) (M : Model W Atom Agent), IsS5 M ∧
        palRank M (S5OrdinalWitness.formulaMany p a b) = α ∧
          bpalRank M (S5OrdinalWitness.formulaMany p a b) = α := by
  refine ⟨s5Witness_many_informative p a b, fun α => ?_⟩
  exact ⟨S5OrdinalWitness.World α, S5OrdinalWitness.modelMany a α,
    S5OrdinalWitness.modelMany_isS5 a α, S5OrdinalWitness.ranks_eq_many p a b hab α⟩

theorem ordinalWitness_many_unknowable {Atom Agent : Type} (p : Atom) (a : Agent) :
    Extinction.CommonlyUnknowable.{u} (OrdinalWitness.formulaMany p a) := by
  intro W M x ⟨hφ, hc⟩
  let N : Model W Unit Unit :=
    { rel := fun _ y z => M.rel a y z
      val := fun _ y => M.val p y }
  have ht (χ : Formula Unit Unit) (y : W) :
      N.Satisfies y χ ↔ M.Satisfies y (χ.map (fun _ => p) (fun _ => a)) := by
    induction χ generalizing y with
    | atom q => rfl
    | neg χ ih => exact not_congr (ih y)
    | conj χ ψ ihχ ihψ => exact and_congr (ihχ y) (ihψ y)
    | box i χ ih =>
        apply forall_congr'; intro z
        exact imp_congr_right (fun _ => ih z)
  apply ordinalWitness_unknowable W N x
  refine ⟨(ht OrdinalWitness.formula x).mpr hφ, ?_⟩
  intro y hxy
  apply (ht OrdinalWitness.formula y).mpr
  apply hc y
  exact Relation.TransGen.mono (fun _ _ ⟨_, hi⟩ => ⟨a, hi⟩) hxy

theorem ordinalWitness_many_informative {Atom Agent : Type} (p : Atom) (a : Agent) :
    Extinction.InformativeWhenTrue.{u} (OrdinalWitness.formulaMany p a) :=
  (Extinction.unknowable_iff_informative _).mp (ordinalWitness_many_unknowable p a)

/-- The single-modality witness gives the same unbounded-rank phenomenon over
K, for any chosen atom and agent in the language. -/
theorem informative_K_unbounded_ranks_many {Atom Agent : Type} (p : Atom) (a : Agent) :
    Extinction.InformativeWhenTrue.{u} (OrdinalWitness.formulaMany p a) ∧
      ∀ α : Ordinal.{u}, 0 < α → ∃ (W : Type u) (M : Model W Atom Agent),
        palRank M (OrdinalWitness.formulaMany p a) = α ∧
          bpalRank M (OrdinalWitness.formulaMany p a) = α := by
  refine ⟨ordinalWitness_many_informative p a, fun α hα => ?_⟩
  exact ⟨Option α.toType, OrdinalWitness.stageMany α 0,
    OrdinalWitness.ranks_eq_many p a α hα⟩

end PropertiesOfPublicAnnouncementsAsOperators
