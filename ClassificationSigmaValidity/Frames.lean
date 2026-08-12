import ClassificationSigmaValidity.Semantics

/-!
# K45, KD45, and S5 frames
-/

namespace ClassificationSigmaValidity

universe u v w

namespace Frame

variable {World : Type u}

def Serial (R : World -> World -> Prop) : Prop :=
  forall x, exists y, R x y

def Transitive (R : World -> World -> Prop) : Prop :=
  forall {x y z}, R x y -> R y z -> R x z

def Euclidean (R : World -> World -> Prop) : Prop :=
  forall {x y z}, R x y -> R x z -> R y z

def Reflexive (R : World -> World -> Prop) : Prop :=
  forall x, R x x

theorem successor_eq_of_transitive_euclidean {R : World -> World -> Prop}
    (ht : Transitive R) (he : Euclidean R) {x y : World} (hxy : R x y) :
    forall z, R x z <-> R y z := by
  intro z
  constructor
  · exact fun hxz => he hxy hxz
  · exact fun hyz => ht hxy hyz

theorem reflexive_serial {R : World -> World -> Prop} (h : Reflexive R) : Serial R :=
  fun x => ⟨x, h x⟩

theorem reflexive_transitive_euclidean_symmetric {R : World -> World -> Prop}
    (hr : Reflexive R) (he : Euclidean R) :
    forall {x y}, R x y -> R y x := by
  intro x y hxy
  exact he hxy (hr x)

end Frame

/-- All agents have transitive, Euclidean accessibility (K45). -/
def IsK45 {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) : Prop :=
  forall i, Frame.Transitive (M.rel i) /\ Frame.Euclidean (M.rel i)

/-- All agents have serial, transitive, Euclidean accessibility (KD45). -/
def IsKD45 {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) : Prop :=
  forall i, Frame.Serial (M.rel i) /\
    Frame.Transitive (M.rel i) /\ Frame.Euclidean (M.rel i)

/-- All agents have reflexive, transitive, Euclidean accessibility (S5). -/
def IsS5 {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) : Prop :=
  forall i, Frame.Reflexive (M.rel i) /\
    Frame.Transitive (M.rel i) /\ Frame.Euclidean (M.rel i)

theorem IsKD45.isK45 {World : Type u} {Atom : Type v} {Agent : Type w}
    {M : Model World Atom Agent} (hM : IsKD45 M) : IsK45 M := by
  intro i
  exact ⟨(hM i).2.1, (hM i).2.2⟩

theorem IsS5.isKD45 {World : Type u} {Atom : Type v} {Agent : Type w}
    {M : Model World Atom Agent} (hM : IsS5 M) : IsKD45 M := by
  intro i
  exact ⟨Frame.reflexive_serial (hM i).1, (hM i).2.1, (hM i).2.2⟩

theorem IsS5.isK45 {World : Type u} {Atom : Type v} {Agent : Type w}
    {M : Model World Atom Agent} (hM : IsS5 M) : IsK45 M :=
  hM.isKD45.isK45

namespace Model

variable {World : Type u} {Atom : Type v} {Agent : Type w}

theorem update_transitive (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (i : Agent) (h : Frame.Transitive (M.rel i)) :
    Frame.Transitive ((M.update phi).rel i) := by
  rintro x y z ⟨hxy, _⟩ ⟨hyz, hz⟩
  exact ⟨h hxy hyz, hz⟩

theorem update_euclidean (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (i : Agent) (h : Frame.Euclidean (M.rel i)) :
    Frame.Euclidean ((M.update phi).rel i) := by
  rintro x y z ⟨hxy, _⟩ ⟨hxz, hz⟩
  exact ⟨h hxy hxz, hz⟩

theorem update_isK45 {M : Model World Atom Agent} (hM : IsK45 M)
    (phi : Formula Atom Agent) : IsK45 (M.update phi) := by
  intro i
  exact ⟨M.update_transitive phi i (hM i).1,
    M.update_euclidean phi i (hM i).2⟩

theorem iterateUpdate_isK45 {M : Model World Atom Agent} (hM : IsK45 M)
    (phi : Formula Atom Agent) : forall n, IsK45 (M.iterateUpdate phi n)
  | 0 => hM
  | n + 1 => update_isK45 (iterateUpdate_isK45 hM phi n) phi

/-- Modal agreement lemma (paper Lemma `lem:modal agreement lemma`), box form. -/
theorem modalAgreement_box {M : Model World Atom Agent} (hM : IsK45 M)
    {i : Agent} {x y : World} (hxy : M.rel i x y) (phi : Formula Atom Agent) :
    M.Satisfies x (.box i phi) <-> M.Satisfies y (.box i phi) := by
  simp only [satisfies_box]
  constructor
  · intro hx z hyz
    exact hx z ((Frame.successor_eq_of_transitive_euclidean
      (R := M.rel i) (x := x) (y := y) (hM i).1 (hM i).2 hxy z).mpr hyz)
  · intro hy z hxz
    exact hy z ((Frame.successor_eq_of_transitive_euclidean
      (R := M.rel i) (x := x) (y := y) (hM i).1 (hM i).2 hxy z).mp hxz)

/-- Modal agreement lemma, diamond form. -/
theorem modalAgreement_dia {M : Model World Atom Agent} (hM : IsK45 M)
    {i : Agent} {x y : World} (hxy : M.rel i x y) (phi : Formula Atom Agent) :
    M.Satisfies x (Formula.dia i phi) <->
      M.Satisfies y (Formula.dia i phi) := by
  simp only [satisfies_dia]
  constructor <;> rintro ⟨z, hz, hphi⟩
  · exact ⟨z, (Frame.successor_eq_of_transitive_euclidean
      (R := M.rel i) (x := x) (y := y) (hM i).1 (hM i).2 hxy z).mp hz, hphi⟩
  · exact ⟨z, (Frame.successor_eq_of_transitive_euclidean
      (R := M.rel i) (x := x) (y := y) (hM i).1 (hM i).2 hxy z).mpr hz, hphi⟩

end Model

end ClassificationSigmaValidity
