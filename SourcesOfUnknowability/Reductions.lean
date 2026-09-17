import SourcesOfUnknowability.Static

/-!
# The eight K45 reduction laws

Lemma 3 of *The Sources of Unknowability and Self-refutation in Epistemic and
Dynamic Epistemic Logic*. Each equivalence is proved at an arbitrary point of
an arbitrary multi-agent K45 model, for any fixed agent. Consequently each is
valid in single-agent K45 and also in KD45 and S5.
-/

namespace SourcesOfUnknowability
namespace Reductions

open ClassificationSigmaValidity

universe u v t

variable {World : Type u} {Atom : Type v} {Agent : Type t}

/-- A formula constant along an accessibility edge can be factored out of
an existential modal statement. -/
private theorem dia_conj_of_agreement (M : Model World Atom Agent)
    (i : Agent) (C B : Formula Atom Agent)
    (hagree : ∀ {x y : World}, M.rel i x y →
      (M.Satisfies x C ↔ M.Satisfies y C)) (x : World) :
    M.Satisfies x (Formula.dia i (.conj C B)) ↔
      M.Satisfies x (.conj C (Formula.dia i B)) := by
  simp only [Model.satisfies_dia, Model.satisfies_and]
  constructor
  · rintro ⟨y, hxy, hC, hB⟩
    exact ⟨(hagree hxy).mpr hC, ⟨y, hxy, hB⟩⟩
  · rintro ⟨hC, y, hxy, hB⟩
    exact ⟨y, hxy, (hagree hxy).mp hC, hB⟩

/-- The dual factoring rule for a universal modal statement. -/
private theorem box_or_of_agreement (M : Model World Atom Agent)
    (i : Agent) (C B : Formula Atom Agent)
    (hagree : ∀ {x y : World}, M.rel i x y →
      (M.Satisfies x C ↔ M.Satisfies y C)) (x : World) :
    M.Satisfies x (.box i (Formula.or C B)) ↔
      M.Satisfies x (Formula.or C (.box i B)) := by
  simp only [Model.satisfies_box, Model.satisfies_or]
  constructor
  · intro h
    by_cases hC : M.Satisfies x C
    · exact Or.inl hC
    · right
      intro y hxy
      rcases h y hxy with hCy | hBy
      · exact (hC ((hagree hxy).mpr hCy)).elim
      · exact hBy
  · intro h y hxy
    rcases h with hC | hB
    · exact Or.inl ((hagree hxy).mp hC)
    · exact Or.inr (hB y hxy)

/-- Lemma 3(1): `□◇A ↔ (◇A ∨ □⊥)`. -/
theorem box_dia [Inhabited Atom] (M : Model World Atom Agent)
    (hM : IsK45 M) (i : Agent) (A : Formula Atom Agent) (x : World) :
    M.Satisfies x (.box i (Formula.dia i A)) ↔
      M.Satisfies x (Formula.or (Formula.dia i A)
        (.box i Formula.falsum)) := by
  constructor
  · intro h
    apply (M.satisfies_or x _ _).mpr
    by_cases hd : M.Satisfies x (Formula.dia i A)
    · exact Or.inl hd
    · right
      intro y hxy
      exact (hd ((M.modalAgreement_dia hM hxy A).mpr (h y hxy))).elim
  · intro h
    rcases (M.satisfies_or x _ _).mp h with hd | hbot
    · intro y hxy
      exact (M.modalAgreement_dia hM hxy A).mp hd
    · intro y hxy
      exact ((M.satisfies_falsum y) (hbot y hxy)).elim

/-- Lemma 3(2): `◇□A ↔ (□A ∧ ◇⊤)`. -/
theorem dia_box [Inhabited Atom] (M : Model World Atom Agent)
    (hM : IsK45 M) (i : Agent) (A : Formula Atom Agent) (x : World) :
    M.Satisfies x (Formula.dia i (.box i A)) ↔
      M.Satisfies x (.conj (.box i A) (Formula.dia i Formula.verum)) := by
  constructor
  · intro h
    obtain ⟨y, hxy, hbox⟩ := (M.satisfies_dia x i (.box i A)).mp h
    exact ⟨(M.modalAgreement_box hM hxy A).mpr hbox,
      (M.satisfies_dia x i Formula.verum).mpr
        ⟨y, hxy, M.satisfies_verum y⟩⟩
  · rintro ⟨hbox, hnonempty⟩
    obtain ⟨y, hxy, _⟩ :=
      (M.satisfies_dia x i Formula.verum).mp hnonempty
    exact (M.satisfies_dia x i (.box i A)).mpr
      ⟨y, hxy, (M.modalAgreement_box hM hxy A).mp hbox⟩

/-- Lemma 3(3): `□□A ↔ □A`. -/
theorem box_box (M : Model World Atom Agent)
    (hM : IsK45 M) (i : Agent) (A : Formula Atom Agent) (x : World) :
    M.Satisfies x (.box i (.box i A)) ↔ M.Satisfies x (.box i A) := by
  constructor
  · intro h y hxy
    exact (h y hxy) y ((hM i).2 hxy hxy)
  · intro h y hxy z hyz
    exact h z ((hM i).1 hxy hyz)

/-- Lemma 3(4): `◇◇A ↔ ◇A`. -/
theorem dia_dia (M : Model World Atom Agent)
    (hM : IsK45 M) (i : Agent) (A : Formula Atom Agent) (x : World) :
    M.Satisfies x (Formula.dia i (Formula.dia i A)) ↔
      M.Satisfies x (Formula.dia i A) := by
  simp only [Model.satisfies_dia]
  constructor
  · rintro ⟨y, hxy, z, hyz, hA⟩
    exact ⟨z, (hM i).1 hxy hyz, hA⟩
  · rintro ⟨y, hxy, hA⟩
    exact ⟨y, hxy, y, (hM i).2 hxy hxy, hA⟩

/-- Lemma 3(5): `◇(◇A ∧ B) ↔ (◇A ∧ ◇B)`. -/
theorem dia_dia_conj (M : Model World Atom Agent)
    (hM : IsK45 M) (i : Agent) (A B : Formula Atom Agent) (x : World) :
    M.Satisfies x (Formula.dia i (.conj (Formula.dia i A) B)) ↔
      M.Satisfies x (.conj (Formula.dia i A) (Formula.dia i B)) := by
  exact dia_conj_of_agreement M i (Formula.dia i A) B
    (fun hxy => M.modalAgreement_dia hM hxy A) x

/-- Lemma 3(6): `◇(□A ∧ B) ↔ (□A ∧ ◇B)`. -/
theorem dia_box_conj (M : Model World Atom Agent)
    (hM : IsK45 M) (i : Agent) (A B : Formula Atom Agent) (x : World) :
    M.Satisfies x (Formula.dia i (.conj (.box i A) B)) ↔
      M.Satisfies x (.conj (.box i A) (Formula.dia i B)) := by
  exact dia_conj_of_agreement M i (.box i A) B
    (fun hxy => M.modalAgreement_box hM hxy A) x

/-- Lemma 3(7): `□(◇A ∨ B) ↔ (◇A ∨ □B)`. -/
theorem box_dia_or (M : Model World Atom Agent)
    (hM : IsK45 M) (i : Agent) (A B : Formula Atom Agent) (x : World) :
    M.Satisfies x (.box i (Formula.or (Formula.dia i A) B)) ↔
      M.Satisfies x (Formula.or (Formula.dia i A) (.box i B)) := by
  exact box_or_of_agreement M i (Formula.dia i A) B
    (fun hxy => M.modalAgreement_dia hM hxy A) x

/-- Lemma 3(8): `□(□A ∨ B) ↔ (□A ∨ □B)`. -/
theorem box_box_or (M : Model World Atom Agent)
    (hM : IsK45 M) (i : Agent) (A B : Formula Atom Agent) (x : World) :
    M.Satisfies x (.box i (Formula.or (.box i A) B)) ↔
      M.Satisfies x (Formula.or (.box i A) (.box i B)) := by
  exact box_or_of_agreement M i (.box i A) B
    (fun hxy => M.modalAgreement_box hM hxy A) x

/-- Example 1: a Moore sentence is unbelievable in KD45. -/
theorem example1_moore_unbelievable_kd45 (i : Agent) (p : Atom) :
    Static.Unbelievable
      (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i
      (Static.moore i (.atom p)) :=
  (Static.unbelievable_iff_unknowable_kd45 i _).mpr
    (Static.moore_unknowable _ i _)

/-- The same Moore sentence is unbelievable in S5. -/
theorem example1_moore_unbelievable_s5 (i : Agent) (p : Atom) :
    Static.Unbelievable
      (Static.Classes.S5 : FrameClass.{u} Atom Agent) i
      (Static.moore i (.atom p)) :=
  (Static.unbelievable_iff_unknowable_s5 i _).mpr
    (Static.moore_unknowable _ i _)

/-- Two S5 worlds disagree on `p` and `q`; every world satisfies one
of the two Moore sentences. -/
private def alternatingModel (p q : Atom) :
    Model (ULift.{u} Bool) Atom Agent where
  rel := fun _ _ _ => True
  val := fun r w => if w.down = true then r = q else r = p

private theorem alternatingModel_isS5 (p q : Atom) :
    IsS5 (alternatingModel (Agent := Agent) p q) := by
  intro i
  refine ⟨?_, ?_, ?_⟩
  · intro x
    trivial
  · intro x y z _ _
    trivial
  · intro x y z _ _
    trivial

/-- Example 1: although each disjunct is unbelievable, their disjunction
is believable in S5. The two atoms are required to be distinct. -/
theorem example1_disjunction_believable_s5 (i : Agent) (p q : Atom)
    (hpq : p ≠ q) :
    Static.Believable (Static.Classes.S5 : FrameClass.{u} Atom Agent) i
      (Formula.or (Static.moore i (.atom p))
        (Static.moore i (.atom q))) := by
  let M : Model (ULift.{u} Bool) Atom Agent := alternatingModel p q
  have hp0 : M.Satisfies (ULift.up false) (.atom p) := by
    simp [M, alternatingModel, Model.Satisfies]
  have hnq0 : ¬ M.Satisfies (ULift.up false) (.atom q) := by
    simpa [M, alternatingModel, Model.Satisfies] using hpq.symm
  have hq1 : M.Satisfies (ULift.up true) (.atom q) := by
    simp [M, alternatingModel, Model.Satisfies]
  have hnp1 : ¬ M.Satisfies (ULift.up true) (.atom p) := by
    simpa [M, alternatingModel, Model.Satisfies] using hpq
  have hfirst : M.Satisfies (ULift.up false) (Static.moore i (.atom p)) := by
    refine ⟨hp0, ?_⟩
    intro hbox
    exact hnp1 (hbox (ULift.up true) trivial)
  have hsecond : M.Satisfies (ULift.up true) (Static.moore i (.atom q)) := by
    refine ⟨hq1, ?_⟩
    intro hbox
    exact hnq0 (hbox (ULift.up false) trivial)
  refine ⟨ULift.{u} Bool, M, alternatingModel_isS5 p q,
    ULift.up false, ?_⟩
  intro y _
  cases y with
  | up b =>
      cases b with
      | false =>
          exact (M.satisfies_or (ULift.up false) _ _).mpr (Or.inl hfirst)
      | true =>
          exact (M.satisfies_or (ULift.up true) _ _).mpr (Or.inr hsecond)

/-- The S5 witness also establishes the KD45 half of Example 1. -/
theorem example1_disjunction_believable_kd45 (i : Agent) (p q : Atom)
    (hpq : p ≠ q) :
    Static.Believable (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i
      (Formula.or (Static.moore i (.atom p))
        (Static.moore i (.atom q))) := by
  have hS5 :
      Static.Believable (Static.Classes.S5 : FrameClass.{u} Atom Agent) i
        (Formula.or (Static.moore i (.atom p))
          (Static.moore i (.atom q))) :=
    example1_disjunction_believable_s5 i p q hpq
  obtain ⟨W, M, hM, x, hx⟩ := hS5
  exact ⟨W, M, hM.isKD45, x, hx⟩

end Reductions
end SourcesOfUnknowability
