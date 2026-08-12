import ClassificationSigmaValidity.Frames

/-!
# Submodels, generated models, and locality

This file develops the locality facts used throughout the paper.  Restricting a
model to a forward-closed set does not change the truth of modal formulas at
states in that set.  Generated submodels are obtained as a special case.  The
same observation also shows that restriction commutes with believed public
announcement and with its finite iterations.

For the finite-descent arguments, we additionally prove the precise shift
identity for the set of targets which survive the first `n` announcements.
-/

namespace ClassificationSigmaValidity

universe u v w

namespace Model

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- The induced submodel on a set of worlds. -/
def restrict (M : Model World Atom Agent) (U : Set World) :
    Model (Subtype U) Atom Agent where
  rel i x y := M.rel i x.1 y.1
  val p x := M.val p x.1

/-- A model on a subtype is an induced submodel of `M` when its relations and
valuation are exactly the restrictions specified in the paper's definition. -/
def IsSubmodel {U : Set World} (N : Model (Subtype U) Atom Agent)
    (M : Model World Atom Agent) : Prop :=
  (∀ i x y, N.rel i x y ↔ M.rel i x.1 y.1) ∧
    ∀ p x, N.val p x ↔ M.val p x.1

/-- The canonical restriction realizes the paper's submodel definition. -/
theorem restrict_isSubmodel (M : Model World Atom Agent) (U : Set World) :
    (M.restrict U).IsSubmodel M := by
  exact ⟨fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

@[simp] theorem restrict_rel (M : Model World Atom Agent) (U : Set World)
    (i : Agent) (x y : Subtype U) :
    (M.restrict U).rel i x y <-> M.rel i x.1 y.1 := Iff.rfl

@[simp] theorem restrict_val (M : Model World Atom Agent) (U : Set World)
    (p : Atom) (x : Subtype U) :
    (M.restrict U).val p x <-> M.val p x.1 := Iff.rfl

/-- No accessibility arrow starting in `U` leaves `U`. -/
def ForwardClosed (M : Model World Atom Agent) (U : Set World) : Prop :=
  forall {x : World}, x ∈ U -> forall (i : Agent) {y : World}, M.rel i x y -> y ∈ U

theorem forwardClosed_univ (M : Model World Atom Agent) :
    M.ForwardClosed Set.univ := by
  intro x hx i y hxy
  trivial

theorem ForwardClosed.mono_rel {M N : Model World Atom Agent} {U : Set World}
    (hU : M.ForwardClosed U)
    (hrel : forall i x y, N.rel i x y -> M.rel i x y) :
    N.ForwardClosed U := by
  intro x hx i y hxy
  exact hU hx i (hrel i x y hxy)

/-- Truth is invariant under restriction to a forward-closed set. -/
theorem restrict_satisfies_iff (M : Model World Atom Agent) (U : Set World)
    (hU : M.ForwardClosed U) (x : Subtype U) (phi : Formula Atom Agent) :
    (M.restrict U).Satisfies x phi <-> M.Satisfies x.1 phi := by
  induction phi generalizing x with
  | atom p => rfl
  | neg phi ih => exact not_congr (ih x)
  | conj phi psi ihPhi ihPsi => exact and_congr (ihPhi x) (ihPsi x)
  | box i phi ih =>
      simp only [satisfies_box]
      constructor
      · intro h y hxy
        let yU : Subtype U := ⟨y, hU x.property i hxy⟩
        exact (ih yU).mp (h yU hxy)
      · intro h y hxy
        exact (ih y).mpr (h y.1 hxy)

/-- Restriction preserves transitivity. -/
theorem restrict_transitive (M : Model World Atom Agent) (U : Set World)
    (i : Agent) (h : Frame.Transitive (M.rel i)) :
    Frame.Transitive ((M.restrict U).rel i) := by
  intro x y z hxy hyz
  exact h hxy hyz

/-- Restriction preserves Euclideanness. -/
theorem restrict_euclidean (M : Model World Atom Agent) (U : Set World)
    (i : Agent) (h : Frame.Euclidean (M.rel i)) :
    Frame.Euclidean ((M.restrict U).rel i) := by
  intro x y z hxy hxz
  exact h hxy hxz

/-- Restriction preserves reflexivity. -/
theorem restrict_reflexive (M : Model World Atom Agent) (U : Set World)
    (i : Agent) (h : Frame.Reflexive (M.rel i)) :
    Frame.Reflexive ((M.restrict U).rel i) := by
  intro x
  exact h x.1

/-- A forward-closed restriction of a serial relation is serial. -/
theorem restrict_serial (M : Model World Atom Agent) (U : Set World)
    (hU : M.ForwardClosed U) (i : Agent) (h : Frame.Serial (M.rel i)) :
    Frame.Serial ((M.restrict U).rel i) := by
  intro x
  obtain ⟨y, hxy⟩ := h x.1
  exact ⟨⟨y, hU x.property i hxy⟩, hxy⟩

theorem restrict_isK45 {M : Model World Atom Agent} (hM : IsK45 M)
    (U : Set World) : IsK45 (M.restrict U) := by
  intro i
  exact ⟨M.restrict_transitive U i (hM i).1,
    M.restrict_euclidean U i (hM i).2⟩

theorem restrict_isKD45 {M : Model World Atom Agent} (hM : IsKD45 M)
    (U : Set World) (hU : M.ForwardClosed U) : IsKD45 (M.restrict U) := by
  intro i
  exact ⟨M.restrict_serial U hU i (hM i).1,
    M.restrict_transitive U i (hM i).2.1,
    M.restrict_euclidean U i (hM i).2.2⟩

theorem restrict_isS5 {M : Model World Atom Agent} (hM : IsS5 M)
    (U : Set World) : IsS5 (M.restrict U) := by
  intro i
  exact ⟨M.restrict_reflexive U i (hM i).1,
    M.restrict_transitive U i (hM i).2.1,
    M.restrict_euclidean U i (hM i).2.2⟩

/-! ## Generated submodels -/

/-- One step along the union of all agents' accessibility relations. -/
def AnyStep (M : Model World Atom Agent) (x y : World) : Prop :=
  exists i : Agent, M.rel i x y

/-- Reachability by a finite path using arbitrary agents. -/
def Reachable (M : Model World Atom Agent) (root y : World) : Prop :=
  Relation.ReflTransGen M.AnyStep root y

theorem reachable_refl (M : Model World Atom Agent) (root : World) :
    M.Reachable root root := Relation.ReflTransGen.refl

theorem Reachable.tail {M : Model World Atom Agent} {root x y : World}
    (hx : M.Reachable root x) (i : Agent) (hxy : M.rel i x y) :
    M.Reachable root y :=
  Relation.ReflTransGen.tail hx ⟨i, hxy⟩

theorem Reachable.trans {M : Model World Atom Agent} {x y z : World}
    (hxy : M.Reachable x y) (hyz : M.Reachable y z) : M.Reachable x z :=
  Relation.ReflTransGen.trans hxy hyz

/-- The carrier set of the submodel generated at `root`. -/
def generatedSet (M : Model World Atom Agent) (root : World) : Set World :=
  {y | M.Reachable root y}

theorem generatedSet_forwardClosed (M : Model World Atom Agent) (root : World) :
    M.ForwardClosed (M.generatedSet root) := by
  intro x hx i y hxy
  exact Reachable.tail hx i hxy

/-- The submodel generated by all finite multi-agent paths from `root`. -/
def generatedSubmodel (M : Model World Atom Agent) (root : World) :
    Model (Subtype (M.generatedSet root)) Atom Agent :=
  M.restrict (M.generatedSet root)

/-- The distinguished root in its generated submodel. -/
def generatedPoint (M : Model World Atom Agent) (root : World) :
    Subtype (M.generatedSet root) :=
  ⟨root, M.reachable_refl root⟩

theorem generatedSubmodel_satisfies_iff (M : Model World Atom Agent)
    (root : World) (x : Subtype (M.generatedSet root)) (phi : Formula Atom Agent) :
    (M.generatedSubmodel root).Satisfies x phi <-> M.Satisfies x.1 phi := by
  exact M.restrict_satisfies_iff (M.generatedSet root)
    (M.generatedSet_forwardClosed root) x phi

theorem generatedSubmodel_root_satisfies_iff (M : Model World Atom Agent)
    (root : World) (phi : Formula Atom Agent) :
    (M.generatedSubmodel root).Satisfies (M.generatedPoint root) phi <->
      M.Satisfies root phi :=
  M.generatedSubmodel_satisfies_iff root (M.generatedPoint root) phi

theorem generatedSubmodel_isK45 {M : Model World Atom Agent} (hM : IsK45 M)
    (root : World) : IsK45 (M.generatedSubmodel root) :=
  M.restrict_isK45 hM (M.generatedSet root)

theorem generatedSubmodel_isKD45 {M : Model World Atom Agent} (hM : IsKD45 M)
    (root : World) : IsKD45 (M.generatedSubmodel root) :=
  M.restrict_isKD45 hM (M.generatedSet root) (M.generatedSet_forwardClosed root)

theorem generatedSubmodel_isS5 {M : Model World Atom Agent} (hM : IsS5 M)
    (root : World) : IsS5 (M.generatedSubmodel root) :=
  M.restrict_isS5 hM (M.generatedSet root)

/-! ## Local agreement -/

/-- Two models on the same carrier agree on valuations and internal arrows of
`U`. -/
def LocallyAgrees (M N : Model World Atom Agent) (U : Set World) : Prop :=
  (forall p x, x ∈ U -> (M.val p x <-> N.val p x)) /\
  (forall i x, x ∈ U -> forall y, y ∈ U -> (M.rel i x y <-> N.rel i x y))

theorem locallyAgrees_refl (M : Model World Atom Agent) (U : Set World) :
    M.LocallyAgrees M U := by
  constructor <;> intros <;> rfl

theorem LocallyAgrees.symm {M N : Model World Atom Agent} {U : Set World}
    (h : M.LocallyAgrees N U) : N.LocallyAgrees M U := by
  constructor
  · intro p x hx
    exact (h.1 p x hx).symm
  · intro i x hx y hy
    exact (h.2 i x hx y hy).symm

theorem restrict_eq_of_locallyAgrees {M N : Model World Atom Agent} {U : Set World}
    (h : M.LocallyAgrees N U) : M.restrict U = N.restrict U := by
  apply ext'
  · intro i x y
    exact h.2 i x.1 x.2 y.1 y.2
  · intro p x
    exact h.1 p x.1 x.2

/-- Reusable locality theorem: forward-closed, locally agreeing models satisfy
the same formulas at every point of the common local region. -/
theorem satisfies_iff_of_locallyAgrees {M N : Model World Atom Agent}
    {U : Set World} (hM : M.ForwardClosed U) (hN : N.ForwardClosed U)
    (hAgree : M.LocallyAgrees N U) (x : World) (hx : x ∈ U)
    (phi : Formula Atom Agent) :
    M.Satisfies x phi <-> N.Satisfies x phi := by
  let xU : Subtype U := ⟨x, hx⟩
  calc
    M.Satisfies x phi <-> (M.restrict U).Satisfies xU phi :=
      (M.restrict_satisfies_iff U hM xU phi).symm
    _ <-> (N.restrict U).Satisfies xU phi := by
      exact satisfies_congr (restrict_eq_of_locallyAgrees hAgree) xU phi
    _ <-> N.Satisfies x phi := N.restrict_satisfies_iff U hN xU phi

/-! ## Restriction and believed public announcement -/

theorem forwardClosed_update {M : Model World Atom Agent} {U : Set World}
    (hU : M.ForwardClosed U) (phi : Formula Atom Agent) :
    (M.update phi).ForwardClosed U := by
  intro x hx i y hxy
  exact hU hx i hxy.1

theorem forwardClosed_iterateUpdate {M : Model World Atom Agent} {U : Set World}
    (hU : M.ForwardClosed U) (phi : Formula Atom Agent) :
    forall n, (M.iterateUpdate phi n).ForwardClosed U
  | 0 => hU
  | n + 1 => forwardClosed_update (forwardClosed_iterateUpdate hU phi n) phi

/-- Restriction to a forward-closed set commutes with one believed public
announcement. -/
theorem restrict_update_eq (M : Model World Atom Agent) (U : Set World)
    (hU : M.ForwardClosed U) (phi : Formula Atom Agent) :
    (M.update phi).restrict U = (M.restrict U).update phi := by
  apply ext'
  · intro i x y
    change (M.rel i x.1 y.1 /\ M.Satisfies y.1 phi) <->
      (M.rel i x.1 y.1 /\ (M.restrict U).Satisfies y phi)
    exact and_congr Iff.rfl (M.restrict_satisfies_iff U hU y phi).symm
  · intro p x
    rfl

/-- Restriction to a forward-closed set commutes with every finite iteration. -/
theorem restrict_iterateUpdate_eq (M : Model World Atom Agent) (U : Set World)
    (hU : M.ForwardClosed U) (phi : Formula Atom Agent) :
    forall n,
      (M.iterateUpdate phi n).restrict U =
        (M.restrict U).iterateUpdate phi n
  | 0 => rfl
  | n + 1 => by
      rw [iterateUpdate_succ, iterateUpdate_succ,
        (M.iterateUpdate phi n).restrict_update_eq U
          (forwardClosed_iterateUpdate hU phi n) phi,
        restrict_iterateUpdate_eq M U hU phi n]

/-- Iterations split at an arbitrary finite time. -/
theorem iterateUpdate_add (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (n m : Nat) :
    M.iterateUpdate phi (n + m) =
      (M.iterateUpdate phi n).iterateUpdate phi m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.add_succ, iterateUpdate_succ, iterateUpdate_succ, ih]

/-- Shift restriction through an iterated update, starting at time `n`. -/
theorem restrict_iterateUpdate_shift_eq (M : Model World Atom Agent)
    (U : Set World) (phi : Formula Atom Agent) (n m : Nat)
    (hU : (M.iterateUpdate phi n).ForwardClosed U) :
    ((M.iterateUpdate phi n).restrict U).iterateUpdate phi m =
      (M.iterateUpdate phi (n + m)).restrict U := by
  calc
    ((M.iterateUpdate phi n).restrict U).iterateUpdate phi m =
        ((M.iterateUpdate phi n).iterateUpdate phi m).restrict U :=
      ((M.iterateUpdate phi n).restrict_iterateUpdate_eq U hU phi m).symm
    _ = (M.iterateUpdate phi (n + m)).restrict U := by
      rw [M.iterateUpdate_add phi n m]

/-- Semantic form of the general restriction/update shift theorem. -/
theorem restrict_iterateUpdate_shift_satisfies_iff
    (M : Model World Atom Agent) (U : Set World)
    (phi : Formula Atom Agent) (n m : Nat)
    (hU : (M.iterateUpdate phi n).ForwardClosed U)
    (x : Subtype U) (psi : Formula Atom Agent) :
    (((M.iterateUpdate phi n).restrict U).iterateUpdate phi m).Satisfies x psi <->
      (M.iterateUpdate phi (n + m)).Satisfies x.1 psi := by
  have hULater : (M.iterateUpdate phi (n + m)).ForwardClosed U := by
    rw [M.iterateUpdate_add phi n m]
    exact forwardClosed_iterateUpdate hU phi m
  rw [restrict_iterateUpdate_shift_eq M U phi n m hU]
  exact (M.iterateUpdate phi (n + m)).restrict_satisfies_iff U hULater x psi

/-! ## The survivor-set shift identity -/

/-- The states surviving the first `n` announcements, denoted `A_n` in the
paper's finite-descent proofs. -/
def survivalSet (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (n : Nat) : Set World :=
  {x | M.Survives phi n x}

@[simp] theorem mem_survivalSet (M : Model World Atom Agent)
    (phi : Formula Atom Agent) (n : Nat) (x : World) :
    x ∈ M.survivalSet phi n <-> M.Survives phi n x := Iff.rfl

/-- At time `n`, all remaining arrows target `A_n`. -/
theorem iterateUpdate_forwardClosed_survivalSet
    (M : Model World Atom Agent) (phi : Formula Atom Agent) (n : Nat) :
    (M.iterateUpdate phi n).ForwardClosed (M.survivalSet phi n) := by
  intro x hx i y hxy
  exact (M.iterateUpdate_rel_iff phi n i x y).mp hxy |>.2

/-- On `A_n`, the original model and the model at time `n` induce exactly the
same submodel. -/
theorem iterateUpdate_restrict_survivalSet_eq_restrict
    (M : Model World Atom Agent) (phi : Formula Atom Agent) (n : Nat) :
    (M.iterateUpdate phi n).restrict (M.survivalSet phi n) =
      M.restrict (M.survivalSet phi n) := by
  apply ext'
  · intro i x y
    change (M.iterateUpdate phi n).rel i x.1 y.1 <-> M.rel i x.1 y.1
    rw [M.iterateUpdate_rel_iff phi n i x.1 y.1]
    exact and_iff_left y.property
  · intro p x
    exact M.iterateUpdate_val phi n p x.1

/-- Exact model-level shift identity used in the S5 descent arguments:
restricting the original model to `A_n` and making `m` further announcements is
the restriction of the original run at time `n + m`. -/
theorem restrict_survivalSet_iterateUpdate_eq
    (M : Model World Atom Agent) (phi : Formula Atom Agent) (n m : Nat) :
    (M.restrict (M.survivalSet phi n)).iterateUpdate phi m =
      (M.iterateUpdate phi (n + m)).restrict (M.survivalSet phi n) := by
  rw [← M.iterateUpdate_restrict_survivalSet_eq_restrict phi n]
  exact M.restrict_iterateUpdate_shift_eq (M.survivalSet phi n) phi n m
    (M.iterateUpdate_forwardClosed_survivalSet phi n)

/-- Pointwise semantic form of the survivor-set shift identity. -/
theorem restrict_survivalSet_shift_satisfies_iff
    (M : Model World Atom Agent) (phi : Formula Atom Agent) (n m : Nat)
    (x : Subtype (M.survivalSet phi n)) (psi : Formula Atom Agent) :
    ((M.restrict (M.survivalSet phi n)).iterateUpdate phi m).Satisfies x psi <->
      (M.iterateUpdate phi (n + m)).Satisfies x.1 psi := by
  have hULater : (M.iterateUpdate phi (n + m)).ForwardClosed
      (M.survivalSet phi n) := by
    rw [M.iterateUpdate_add phi n m]
    exact forwardClosed_iterateUpdate
      (M.iterateUpdate_forwardClosed_survivalSet phi n) phi m
  rw [M.restrict_survivalSet_iterateUpdate_eq phi n m]
  exact (M.iterateUpdate phi (n + m)).restrict_satisfies_iff
    (M.survivalSet phi n) hULater x psi

end Model

end ClassificationSigmaValidity
