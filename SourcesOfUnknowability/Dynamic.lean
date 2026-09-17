import ClassificationSigmaValidity.Locality
import ClassificationSigmaValidity.Patterns
import SourcesOfUnknowability.Static

/-!
# Standard public announcements and their iteration

The update in `ClassificationSigmaValidity.Semantics` deletes arrows and belongs
to a different paper.  Here a public announcement restricts the *worlds* of a
model, as in Definitions 6--10 of the present paper.  `survivors n` keeps the
world type fixed while recording the carrier of the `n`th restricted model.
-/

namespace SourcesOfUnknowability
namespace Dynamic

open ClassificationSigmaValidity

universe u v w

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- Definition 6: standard public announcement of `phi`. -/
def announce (M : Model World Atom Agent) (phi : Formula Atom Agent) :
    Model (Subtype (M.truthSet phi)) Atom Agent :=
  M.restrict (M.truthSet phi)

/-- Satisfaction in the induced model on `U`, expressed on the original world
type.  The designated world is normally assumed to belong to `U`. -/
def SatisfiesOn (M : Model World Atom Agent) (U : Set World) (x : World) :
    Formula Atom Agent → Prop
  | .atom p => M.val p x
  | .neg phi => ¬ SatisfiesOn M U x phi
  | .conj phi psi => SatisfiesOn M U x phi ∧ SatisfiesOn M U x psi
  | .box i phi => ∀ y, y ∈ U → M.rel i x y → SatisfiesOn M U y phi

theorem satisfiesOn_iff_restrict (M : Model World Atom Agent) (U : Set World)
    (x : Subtype U) (phi : Formula Atom Agent) :
    SatisfiesOn M U x.1 phi ↔ (M.restrict U).Satisfies x phi := by
  induction phi generalizing x with
  | atom p => rfl
  | neg phi ih => exact not_congr (ih x)
  | conj phi psi ihPhi ihPsi => exact and_congr (ihPhi x) (ihPsi x)
  | box i phi ih =>
      constructor
      · intro h y hxy
        exact (ih y).mp (h y.1 y.2 hxy)
      · intro h y hy hxy
        exact (ih ⟨y, hy⟩).mpr (h ⟨y, hy⟩ hxy)

/-- The original model is the zero-step restriction. -/
theorem satisfiesOn_univ (M : Model World Atom Agent) (x : World)
    (phi : Formula Atom Agent) :
    SatisfiesOn M Set.univ x phi ↔ M.Satisfies x phi := by
  induction phi generalizing x with
  | atom p => rfl
  | neg phi ih => exact not_congr (ih x)
  | conj phi psi ihPhi ihPsi => exact and_congr (ihPhi x) (ihPsi x)
  | box i phi ih =>
      simp only [SatisfiesOn, Model.satisfies_box, Set.mem_univ, true_implies]
      exact forall_congr' (fun y => imp_congr_right (fun _ => ih y))

/-- Definition 9: worlds surviving `n` standard public announcements. -/
def survivors (M : Model World Atom Agent) (phi : Formula Atom Agent) :
    Nat → Set World
  | 0 => Set.univ
  | n + 1 => {x | x ∈ survivors M phi n ∧
      SatisfiesOn M (survivors M phi n) x phi}

@[simp] theorem survivors_zero (M : Model World Atom Agent)
    (phi : Formula Atom Agent) : survivors M phi 0 = Set.univ := rfl

theorem survivors_succ (M : Model World Atom Agent)
    (phi : Formula Atom Agent) (n : Nat) (x : World) :
    x ∈ survivors M phi (n + 1) ↔
      x ∈ survivors M phi n ∧
        SatisfiesOn M (survivors M phi n) x phi := Iff.rfl

theorem survivors_antitone (M : Model World Atom Agent)
    (phi : Formula Atom Agent) : Antitone (survivors M phi) := by
  intro m n hmn
  induction hmn with
  | refl =>
      intro x hx
      exact hx
  | @step n hmn ih =>
      intro x hx
      exact ih (hx.1)

/-- Truth after `n` announcements, treating a removed designated world as
false.  This makes the statement of eventual refutation total. -/
def TrueAfter (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (n : Nat) (x : World) : Prop :=
  x ∈ survivors M phi n ∧ SatisfiesOn M (survivors M phi n) x phi

theorem trueAfter_iff_survives_succ (M : Model World Atom Agent)
    (phi : Formula Atom Agent) (n : Nat) (x : World) :
    TrueAfter M phi n x ↔ x ∈ survivors M phi (n + 1) := Iff.rfl

theorem trueAfter_zero (M : Model World Atom Agent)
    (phi : Formula Atom Agent) (x : World) :
    TrueAfter M phi 0 x ↔ M.Satisfies x phi := by
  simp [TrueAfter, survivors, satisfiesOn_univ]

variable {Atom : Type v} {Agent : Type w}

/-- Definition 7, with the paper's `phi ∧ ◇phi` precondition. -/
def Successful (C : FrameClass.{u} Atom Agent) (i : Agent)
    (phi : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), C M → ∀ x,
    M.Satisfies x phi → M.Satisfies x (Formula.dia i phi) →
      SatisfiesOn M (M.truthSet phi) x phi

def SelfRefuting (C : FrameClass.{u} Atom Agent) (i : Agent)
    (phi : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), C M → ∀ x,
    M.Satisfies x phi → M.Satisfies x (Formula.dia i phi) →
      ¬ SatisfiesOn M (M.truthSet phi) x phi

def Unsuccessful (C : FrameClass.{u} Atom Agent) (i : Agent)
    (phi : Formula Atom Agent) : Prop := ¬ Successful C i phi

/-- Definition 8: the carrier changes after a truthful announcement. -/
def Informative (C : FrameClass.{u} Atom Agent)
    (phi : Formula Atom Agent) : Prop :=
  ∃ (World : Type u) (M : Model World Atom Agent) (x : World),
    C M ∧ M.Satisfies x phi ∧ M.truthSet phi ≠ Set.univ

def AlwaysInformative (C : FrameClass.{u} Atom Agent)
    (phi : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), C M → ∀ x,
    M.Satisfies x phi → M.truthSet phi ≠ Set.univ

def Uninformative (C : FrameClass.{u} Atom Agent)
    (phi : Formula Atom Agent) : Prop := ¬ Informative C phi

/-- Definition 9, bounded and unbounded self-refutation. -/
def SelfRefutingWithin (C : FrameClass.{u} Atom Agent)
    (phi : Formula Atom Agent) (n : Nat) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), C M → ∀ x,
    M.Satisfies x phi → ∃ m ≤ n, ¬ TrueAfter M phi m x

def EventuallySelfRefuting (C : FrameClass.{u} Atom Agent)
    (phi : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), C M → ∀ x,
    M.Satisfies x phi → ∃ n, ¬ TrueAfter M phi n x

/-- Definition 10: knowledge after a suitable truthful announcement. -/
def Learnable (C : FrameClass.{u} Atom Agent) (i : Agent)
    (phi : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), C M → ∀ x,
    M.Satisfies x phi → ∃ psi : Formula Atom Agent,
      x ∈ M.truthSet psi ∧
        SatisfiesOn M (M.truthSet psi) x (.box i phi)

/-- Remark 2: unbelievability forces every truthful announcement to remove
at least one world. -/
theorem unbelievable_implies_alwaysInformative
    (C : FrameClass.{u} Atom Agent) (i : Agent)
    (phi : Formula Atom Agent)
    (h : ∀ {World : Type u} (M : Model World Atom Agent), C M →
      ∀ x, ¬ M.Satisfies x (.box i phi)) :
    AlwaysInformative C phi := by
  intro World M hM x hx heq
  have hall : ∀ y, M.Satisfies y phi := by
    intro y
    have : y ∈ M.truthSet phi := by rw [heq]; trivial
    exact this
  exact h M hM x (fun y _ => hall y)

/-- The same implication stated using the static definition of
unbelievability. -/
theorem staticUnbelievable_implies_alwaysInformative
    (C : FrameClass.{u} Atom Agent) (i : Agent)
    (phi : Formula Atom Agent)
    (h : Static.Unbelievable C i phi) : AlwaysInformative C phi := by
  apply unbelievable_implies_alwaysInformative C i phi
  intro World M hM x hbox
  exact h ⟨World, M, hM, x, hbox⟩

/-- A full-carrier announcement leaves every later carrier full. -/
theorem survivors_all_of_truth_everywhere
    (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (h : ∀ x, M.Satisfies x phi) (n : Nat) :
    survivors M phi n = Set.univ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      ext x
      simp only [survivors_succ, ih, Set.mem_univ, true_and]
      exact ⟨fun _ => trivial,
        fun _ => (satisfiesOn_univ M x phi).2 (h x)⟩

/-- Remark 2: eventual self-refutation implies always informativeness in any
frame class. -/
theorem eventuallySelfRefuting_implies_alwaysInformative
    (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent)
    (h : EventuallySelfRefuting C phi) : AlwaysInformative C phi := by
  intro World M hM x hx heq
  have hall : ∀ y, M.Satisfies y phi := by
    intro y
    have : y ∈ M.truthSet phi := by rw [heq]; trivial
    exact this
  obtain ⟨n, hn⟩ := h M hM x hx
  apply hn
  change x ∈ survivors M phi n ∧
    SatisfiesOn M (survivors M phi n) x phi
  rw [survivors_all_of_truth_everywhere M phi hall n]
  exact ⟨Set.mem_univ x, (satisfiesOn_univ M x phi).2 hx⟩

end Dynamic
end SourcesOfUnknowability
