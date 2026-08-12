import Mathlib.Logic.Relation
import ClassificationSigmaValidity.Syntax

/-!
# Kripke semantics and believed public announcements

Believed public announcement keeps the state space and valuation fixed and
removes precisely the arrows whose targets do not satisfy the announced
formula.  This is the update operation iterated throughout the paper.
-/

namespace ClassificationSigmaValidity

universe u v w

/-- A multi-agent Kripke model.  A pointed model is obtained by additionally
choosing an element of `World`, so no separate nonemptiness field is needed. -/
@[ext]
structure Model (World : Type u) (Atom : Type v) (Agent : Type w) where
  rel : Agent -> World -> World -> Prop
  val : Atom -> World -> Prop

namespace Model

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- Truth of a basic modal formula at a state. -/
def Satisfies (M : Model World Atom Agent) (x : World) : Formula Atom Agent -> Prop
  | .atom p => M.val p x
  | .neg phi => Not (Satisfies M x phi)
  | .conj phi psi => Satisfies M x phi /\ Satisfies M x psi
  | .box i phi => forall y, M.rel i x y -> Satisfies M y phi

@[simp] theorem satisfies_atom (M : Model World Atom Agent) (x : World) (p : Atom) :
    M.Satisfies x (.atom p) <-> M.val p x := Iff.rfl

@[simp] theorem satisfies_neg (M : Model World Atom Agent) (x : World)
    (phi : Formula Atom Agent) :
    M.Satisfies x (.neg phi) <-> Not (M.Satisfies x phi) := Iff.rfl

@[simp] theorem satisfies_and (M : Model World Atom Agent) (x : World)
    (phi psi : Formula Atom Agent) :
    M.Satisfies x (.conj phi psi) <-> M.Satisfies x phi /\ M.Satisfies x psi := Iff.rfl

@[simp] theorem satisfies_box (M : Model World Atom Agent) (x : World) (i : Agent)
    (phi : Formula Atom Agent) :
    M.Satisfies x (.box i phi) <->
      forall y, M.rel i x y -> M.Satisfies y phi := Iff.rfl

@[simp] theorem satisfies_or (M : Model World Atom Agent) (x : World)
    (phi psi : Formula Atom Agent) :
    M.Satisfies x (Formula.or phi psi) <-> M.Satisfies x phi \/ M.Satisfies x psi := by
  classical
  simp only [Formula.or, Satisfies]
  constructor
  · intro h
    by_cases hp : M.Satisfies x phi
    · exact Or.inl hp
    · by_cases hq : M.Satisfies x psi
      · exact Or.inr hq
      · exact (h ⟨hp, hq⟩).elim
  · rintro (hp | hpsi) ⟨hnp, hnq⟩
    · exact hnp hp
    · exact hnq hpsi

@[simp] theorem satisfies_imp (M : Model World Atom Agent) (x : World)
    (phi psi : Formula Atom Agent) :
    M.Satisfies x (Formula.imp phi psi) <->
      (M.Satisfies x phi -> M.Satisfies x psi) := by
  classical
  change M.Satisfies x (Formula.or (.neg phi) psi) <-> _
  rw [satisfies_or, satisfies_neg]
  constructor
  · rintro (hn | hpsi) hphi
    · exact (hn hphi).elim
    · exact hpsi
  · intro h
    by_cases hphi : M.Satisfies x phi
    · exact Or.inr (h hphi)
    · exact Or.inl hphi

@[simp] theorem satisfies_dia (M : Model World Atom Agent) (x : World) (i : Agent)
    (phi : Formula Atom Agent) :
    M.Satisfies x (Formula.dia i phi) <->
      exists y, M.rel i x y /\ M.Satisfies y phi := by
  simp [Formula.dia, Satisfies]

@[simp] theorem not_satisfies_dia (M : Model World Atom Agent) (x : World) (i : Agent)
    (phi : Formula Atom Agent) :
    Not (M.Satisfies x (Formula.dia i phi)) <->
      forall y, M.rel i x y -> Not (M.Satisfies y phi) := by
  simp [Formula.dia, Satisfies]

@[simp] theorem satisfies_falsum [Inhabited Atom] (M : Model World Atom Agent) (x : World) :
    Not (M.Satisfies x Formula.falsum) := by
  simp [Formula.falsum, Satisfies]

@[simp] theorem satisfies_verum [Inhabited Atom] (M : Model World Atom Agent) (x : World) :
    M.Satisfies x Formula.verum := by
  simp [Formula.verum]

/-- The extension of a formula in a model. -/
def truthSet (M : Model World Atom Agent) (phi : Formula Atom Agent) : Set World :=
  {x | M.Satisfies x phi}

/-- Relativization under a believed public announcement. -/
def update (M : Model World Atom Agent) (phi : Formula Atom Agent) :
    Model World Atom Agent where
  rel i x y := M.rel i x y /\ M.Satisfies y phi
  val := M.val

@[simp] theorem update_rel (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (i : Agent) (x y : World) :
    (M.update phi).rel i x y <-> M.rel i x y /\ M.Satisfies y phi := Iff.rfl

@[simp] theorem update_val (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (p : Atom) (x : World) :
    (M.update phi).val p x <-> M.val p x := Iff.rfl

/-- The model after `n` believed public announcements of the same formula. -/
def iterateUpdate (M : Model World Atom Agent) (phi : Formula Atom Agent) :
    Nat -> Model World Atom Agent
  | 0 => M
  | n + 1 => (iterateUpdate M phi n).update phi

@[simp] theorem iterateUpdate_zero (M : Model World Atom Agent) (phi : Formula Atom Agent) :
    M.iterateUpdate phi 0 = M := rfl

@[simp] theorem iterateUpdate_succ (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (n : Nat) :
    M.iterateUpdate phi (n + 1) = (M.iterateUpdate phi n).update phi := rfl

@[simp] theorem iterateUpdate_val (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (n : Nat) (p : Atom) (x : World) :
    (M.iterateUpdate phi n).val p x <-> M.val p x := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [iterateUpdate] using ih

/-- The truth trace generated by repeatedly announcing `phi`. -/
def trace (M : Model World Atom Agent) (x : World) (phi : Formula Atom Agent)
    (n : Nat) : Prop :=
  (M.iterateUpdate phi n).Satisfies x phi

@[simp] theorem trace_zero (M : Model World Atom Agent) (x : World)
    (phi : Formula Atom Agent) : M.trace x phi 0 <-> M.Satisfies x phi := Iff.rfl

@[simp] theorem trace_one (M : Model World Atom Agent) (x : World)
    (phi : Formula Atom Agent) :
    M.trace x phi 1 <-> (M.update phi).Satisfies x phi := Iff.rfl

/-- Targets surviving the first `n` announcements. -/
def Survives (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (n : Nat) (y : World) : Prop :=
  forall m, m < n -> (M.iterateUpdate phi m).Satisfies y phi

@[simp] theorem survives_zero (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (y : World) : M.Survives phi 0 y := by
  simp [Survives]

theorem survives_succ_iff (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (n : Nat) (y : World) :
    M.Survives phi (n + 1) y <->
      M.Survives phi n y /\ (M.iterateUpdate phi n).Satisfies y phi := by
  simp only [Survives]
  constructor
  · intro h
    exact ⟨fun m hm => h m (Nat.lt.step hm), h n (Nat.lt_succ_self n)⟩
  · rintro ⟨h, hn⟩ m hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
    · exact h m hm
    · exact hn

/-- After `n` updates, an original arrow remains exactly when its target has
survived every earlier announcement. -/
theorem iterateUpdate_rel_iff (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (n : Nat) (i : Agent) (x y : World) :
    (M.iterateUpdate phi n).rel i x y <-> M.rel i x y /\ M.Survives phi n y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iterateUpdate_succ, update_rel, ih, survives_succ_iff]
      constructor
      · rintro ⟨⟨hxy, hs⟩, hn⟩
        exact ⟨hxy, hs, hn⟩
      · rintro ⟨hxy, hs, hn⟩
        exact ⟨⟨hxy, hs⟩, hn⟩

theorem survives_antitone (M : Model World Atom Agent) (phi : Formula Atom Agent)
    {m n : Nat} (hmn : m <= n) :
    {y | M.Survives phi n y} <= {y | M.Survives phi m y} := by
  intro y hy j hj
  exact hy j (Nat.lt_of_lt_of_le hj hmn)

/-- Extensional equality specialized to models. -/
theorem ext' {M N : Model World Atom Agent}
    (hrel : forall i x y, M.rel i x y <-> N.rel i x y)
    (hval : forall p x, M.val p x <-> N.val p x) : M = N := by
  ext i x y
  · exact hrel i x y
  · exact hval i x

theorem satisfies_congr {M N : Model World Atom Agent} (h : M = N)
    (x : World) (phi : Formula Atom Agent) :
    M.Satisfies x phi <-> N.Satisfies x phi := by
  subst h
  rfl

/-- If two consecutive iterates coincide, all subsequent iterates coincide. -/
theorem iterateUpdate_eq_of_step (M : Model World Atom Agent) (phi : Formula Atom Agent)
    {n : Nat} (h : M.iterateUpdate phi (n + 1) = M.iterateUpdate phi n) :
    forall k, M.iterateUpdate phi (n + k) = M.iterateUpdate phi n := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.add_succ, iterateUpdate_succ, ih]
      exact h

end Model

end ClassificationSigmaValidity
