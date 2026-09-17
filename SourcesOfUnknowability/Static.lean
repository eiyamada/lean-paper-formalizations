import ClassificationSigmaValidity.FrameClass

/-!
# Static unknowability and unbelievability

Definitions 1--2 and the static parts of Lemmas 1--2 and Theorem 1 of
Yamada, *The Sources of Unknowability and Self-refutation in Epistemic and
Dynamic Epistemic Logic*. The definitions work for any number of agents;
the single-agent language is obtained by taking `Agent = Unit`.
-/

namespace SourcesOfUnknowability
namespace Static

open ClassificationSigmaValidity

universe u v w

variable {Atom : Type v} {Agent : Type w}

/-- A formula has a pointed model in a class. -/
def Satisfiable (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent) : Prop :=
  ∃ (World : Type u) (M : Model World Atom Agent), C M ∧
    ∃ x : World, M.Satisfies x phi

/-- A formula holds at every point of every model in a class. -/
def Valid (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent) : Prop :=
  ∀ (World : Type u) (M : Model World Atom Agent), C M →
    ∀ x : World, M.Satisfies x phi

/-- Logical equivalence relative to a class of frames. -/
def Equivalent (C : FrameClass.{u} Atom Agent)
    (phi psi : Formula Atom Agent) : Prop :=
  ∀ (World : Type u) (M : Model World Atom Agent), C M →
    ∀ x : World, M.Satisfies x phi ↔ M.Satisfies x psi

/-- A formula is believable when its box is satisfiable. -/
def Believable (C : FrameClass.{u} Atom Agent) (i : Agent)
    (phi : Formula Atom Agent) : Prop :=
  Satisfiable C (.box i phi)

/-- A formula is knowable when it and its box can hold together. -/
def Knowable (C : FrameClass.{u} Atom Agent) (i : Agent)
    (phi : Formula Atom Agent) : Prop :=
  Satisfiable C (.conj phi (.box i phi))

def Unbelievable (C : FrameClass.{u} Atom Agent) (i : Agent)
    (phi : Formula Atom Agent) : Prop :=
  ¬ Believable C i phi

def Unknowable (C : FrameClass.{u} Atom Agent) (i : Agent)
    (phi : Formula Atom Agent) : Prop :=
  ¬ Knowable C i phi

/-- The Moore operation `phi ↦ phi ∧ ¬□ᵢ phi`. -/
def moore (i : Agent) (phi : Formula Atom Agent) : Formula Atom Agent :=
  .conj phi (.neg (.box i phi))

namespace Classes

/-- K imposes no frame conditions. -/
def K : FrameClass.{u} Atom Agent := fun _ => True

/-- KD has serial accessibility for every agent. -/
def KD : FrameClass.{u} Atom Agent :=
  fun M => ∀ i, Frame.Serial (M.rel i)

/-- The standard KD45 class from the existing modal infrastructure. -/
def KD45 : FrameClass.{u} Atom Agent := fun M => IsKD45 M

/-- The standard S5 class from the existing modal infrastructure. -/
def S5 : FrameClass.{u} Atom Agent := fun M => IsS5 M

end Classes

/-- The paper's modal agreement lemma, for a boxed formula. The proof only
needs transitivity and Euclideanness. -/
theorem modalAgreement_box {World : Type u} {M : Model World Atom Agent}
    (hM : IsK45 M) {i : Agent} {x y : World} (hxy : M.rel i x y)
    (phi : Formula Atom Agent) :
    M.Satisfies x (.box i phi) ↔ M.Satisfies y (.box i phi) :=
  M.modalAgreement_box hM hxy phi

/-- The diamond form of the modal agreement lemma. -/
theorem modalAgreement_dia {World : Type u} {M : Model World Atom Agent}
    (hM : IsK45 M) {i : Agent} {x y : World} (hxy : M.rel i x y)
    (phi : Formula Atom Agent) :
    M.Satisfies x (Formula.dia i phi) ↔
      M.Satisfies y (Formula.dia i phi) :=
  M.modalAgreement_dia hM hxy phi

/-- For any frame class, unknowability is precisely being a fixed point of
the Moore operation up to logical equivalence. -/
theorem unknowable_iff_mooreFixed (C : FrameClass.{u} Atom Agent)
    (i : Agent) (phi : Formula Atom Agent) :
    Unknowable C i phi ↔ Equivalent C phi (moore i phi) := by
  constructor
  · intro h World M hM x
    constructor
    · intro hphi
      refine ⟨hphi, ?_⟩
      intro hbox
      exact h ⟨World, M, hM, x, ⟨hphi, hbox⟩⟩
    · intro hmoore
      exact hmoore.1
  · intro h ⟨World, M, hM, x, hknow⟩
    exact ((h World M hM x).mp hknow.1).2 hknow.2

/-- Unbelievability always entails unknowability. -/
theorem unbelievable_implies_unknowable (C : FrameClass.{u} Atom Agent)
    (i : Agent) (phi : Formula Atom Agent) :
    Unbelievable C i phi → Unknowable C i phi := by
  intro h ⟨World, M, hM, x, hknow⟩
  exact h ⟨World, M, hM, x, hknow.2⟩

/-- Belief can be made knowledge at an accessible state when accessibility
is serial and transitive. This is the stronger KD4 form of Lemma 2. -/
theorem believable_iff_knowable_of_serial_transitive
    (C : FrameClass.{u} Atom Agent)
    (hC : ∀ {World : Type u} (M : Model World Atom Agent),
      C M → ∀ i, Frame.Serial (M.rel i) ∧ Frame.Transitive (M.rel i))
    (i : Agent) (phi : Formula Atom Agent) :
    Believable C i phi ↔ Knowable C i phi := by
  constructor
  · rintro ⟨World, M, hM, x, hbox⟩
    obtain ⟨y, hxy⟩ := (hC M hM i).1 x
    refine ⟨World, M, hM, y, ⟨hbox y hxy, ?_⟩⟩
    intro z hyz
    exact hbox z ((hC M hM i).2 hxy hyz)
  · rintro ⟨World, M, hM, x, hknow⟩
    exact ⟨World, M, hM, x, hknow.2⟩

/-- Lemma 2 for any serial and transitive class, including KD45 and S5. -/
theorem unbelievable_iff_unknowable_of_serial_transitive
    (C : FrameClass.{u} Atom Agent)
    (hC : ∀ {World : Type u} (M : Model World Atom Agent),
      C M → ∀ i, Frame.Serial (M.rel i) ∧ Frame.Transitive (M.rel i))
    (i : Agent) (phi : Formula Atom Agent) :
    Unbelievable C i phi ↔ Unknowable C i phi := by
  exact not_congr (believable_iff_knowable_of_serial_transitive C hC i phi)

theorem unbelievable_iff_unknowable_kd45 (i : Agent)
    (phi : Formula Atom Agent) :
    Unbelievable (Classes.KD45 : FrameClass.{u} Atom Agent) i phi ↔
      Unknowable (Classes.KD45 : FrameClass.{u} Atom Agent) i phi := by
  apply unbelievable_iff_unknowable_of_serial_transitive
  intro World M hM j
  exact ⟨(hM j).1, (hM j).2.1⟩

theorem unbelievable_iff_unknowable_s5 (i : Agent)
    (phi : Formula Atom Agent) :
    Unbelievable (Classes.S5 : FrameClass.{u} Atom Agent) i phi ↔
      Unknowable (Classes.S5 : FrameClass.{u} Atom Agent) i phi := by
  apply unbelievable_iff_unknowable_of_serial_transitive
  intro World M hM j
  exact ⟨Frame.reflexive_serial (hM j).1, (hM j).2.1⟩

/-- Every formula is believable in K, including unsatisfiable formulas:
a dead-end state believes everything. -/
theorem believable_k (i : Agent) (phi : Formula Atom Agent) :
    Believable (Classes.K : FrameClass.{u} Atom Agent) i phi := by
  let M : Model (ULift.{u} PUnit) Atom Agent :=
    { rel := fun _ _ _ => False, val := fun _ _ => False }
  refine ⟨ULift.{u} PUnit, M, trivial, ULift.up PUnit.unit, ?_⟩
  intro y hy
  exact False.elim hy

/-- Add a predecessor pointing to `x` without changing the original model. -/
def addRoot {World : Type u} (M : Model World Atom Agent) (x : World) :
    Model (Option World) Atom Agent where
  rel i a b :=
    match a, b with
    | none, some y => y = x
    | some y, some z => M.rel i y z
    | _, _ => False
  val p a :=
    match a with
    | none => False
    | some y => M.val p y

/-- All old states retain the truth of every modal formula after adding a
predecessor. -/
theorem addRoot_satisfies_some {World : Type u}
    (M : Model World Atom Agent) (x : World) (phi : Formula Atom Agent) :
    ∀ y : World, (addRoot M x).Satisfies (some y) phi ↔ M.Satisfies y phi := by
  induction phi with
  | atom p =>
      intro y
      rfl
  | neg psi ih =>
      intro y
      exact not_congr (ih y)
  | conj psi theta ihψ ihθ =>
      intro y
      exact and_congr (ihψ y) (ihθ y)
  | box j psi ih =>
      intro y
      constructor
      · intro h z hyz
        exact (ih z).mp (h (some z) hyz)
      · intro h z hyz
        cases z with
        | none => exact False.elim hyz
        | some z => exact (ih z).mpr (h z hyz)

theorem addRoot_isKD {World : Type u} {M : Model World Atom Agent}
    (hM : Classes.KD M) (x : World) : Classes.KD (addRoot M x) := by
  intro i y
  cases y with
  | none => exact ⟨some x, rfl⟩
  | some y =>
      obtain ⟨z, hyz⟩ := hM i y
      exact ⟨some z, hyz⟩

/-- Theorem 1(2): in KD a formula is believable exactly when it is
satisfiable. -/
theorem believable_iff_satisfiable_kd (i : Agent)
    (phi : Formula Atom Agent) :
    Believable (Classes.KD : FrameClass.{u} Atom Agent) i phi ↔
      Satisfiable (Classes.KD : FrameClass.{u} Atom Agent) phi := by
  constructor
  · rintro ⟨World, M, hM, x, hbox⟩
    obtain ⟨y, hxy⟩ := hM i x
    exact ⟨World, M, hM, y, hbox y hxy⟩
  · rintro ⟨World, M, hM, x, hphi⟩
    let N := addRoot M x
    refine ⟨Option World, N, addRoot_isKD hM x, none, ?_⟩
    intro y hy
    cases y with
    | none => exact False.elim hy
    | some y =>
        change y = x at hy
        subst y
        exact (addRoot_satisfies_some M x phi x).mpr hphi

theorem unbelievable_iff_unsatisfiable_kd (i : Agent)
    (phi : Formula Atom Agent) :
    Unbelievable (Classes.KD : FrameClass.{u} Atom Agent) i phi ↔
      ¬ Satisfiable (Classes.KD : FrameClass.{u} Atom Agent) phi :=
  not_congr (believable_iff_satisfiable_kd i phi)

/-- Every Moore sentence `phi ∧ ¬□ᵢ phi` is unknowable, without frame
conditions. -/
theorem moore_unknowable (C : FrameClass.{u} Atom Agent)
    (i : Agent) (phi : Formula Atom Agent) :
    Unknowable C i (moore i phi) := by
  rintro ⟨World, M, hM, x, hknow⟩
  have hnotBox : ¬ M.Satisfies x (.box i phi) := hknow.1.2
  apply hnotBox
  intro y hxy
  exact (hknow.2 y hxy).1

/-- The two-state serial cycle used in the proof of Lemma 2. Its valuation
makes every atom true at `true` and false at `false`. -/
def cycleModel : Model (ULift.{u} Bool) Atom Agent where
  rel := fun _ x y => x.down ≠ y.down
  val := fun _ x => x.down = true

theorem cycleModel_isKD :
    Classes.KD (cycleModel : Model (ULift.{u} Bool) Atom Agent) := by
  intro i x
  cases x with
  | up b =>
      cases b with
      | false =>
          refine ⟨ULift.up true, ?_⟩
          change (false : Bool) ≠ true
          decide
      | true =>
          refine ⟨ULift.up false, ?_⟩
          change (true : Bool) ≠ false
          decide

/-- The Moore sentence is nevertheless believable at the `false` state of
the serial cycle. -/
theorem moore_believable_kd (i : Agent) (p : Atom) :
    Believable (Classes.KD : FrameClass.{u} Atom Agent)
      i (moore i (.atom p)) := by
  let M : Model (ULift.{u} Bool) Atom Agent := cycleModel
  refine ⟨ULift.{u} Bool, M, cycleModel_isKD, ULift.up false, ?_⟩
  intro y hy
  cases y with
  | up b =>
      cases b with
      | false => exact (hy rfl).elim
      | true =>
          constructor
          · rfl
          · intro hbox
            have htf : M.rel i (ULift.up true) (ULift.up false) := by
              change (true : Bool) ≠ false
              decide
            have hpfalse := hbox (ULift.up false) htf
            exact Bool.false_ne_true hpfalse

/-- The converse of `unbelievable_implies_unknowable` fails in KD. -/
theorem moore_unknowable_and_believable_kd (i : Agent) (p : Atom) :
    Unknowable (Classes.KD : FrameClass.{u} Atom Agent)
      i (moore i (.atom p)) ∧
    Believable (Classes.KD : FrameClass.{u} Atom Agent)
      i (moore i (.atom p)) :=
  ⟨moore_unknowable _ i _, moore_believable_kd i p⟩

theorem moore_unknowable_and_believable_k (i : Agent) (p : Atom) :
    Unknowable (Classes.K : FrameClass.{u} Atom Agent)
      i (moore i (.atom p)) ∧
    Believable (Classes.K : FrameClass.{u} Atom Agent)
      i (moore i (.atom p)) :=
  ⟨moore_unknowable _ i _, believable_k i _⟩

end Static
end SourcesOfUnknowability
