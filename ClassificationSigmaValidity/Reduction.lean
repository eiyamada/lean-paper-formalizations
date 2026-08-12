import ClassificationSigmaValidity.Semantics

/-!
# Reduction for believed public announcements

Believed public announcement does not remove states.  It restricts every
accessibility relation to targets satisfying the announced formula.  Therefore
a basic modal formula evaluated after one announcement can again be expressed
in the basic modal language: a box is relativized by the announcement formula.

This file proves the one-step reduction theorem and its iteration.  In
particular, every finite truth condition arising from repeated announcements is
equivalent to an ordinary modal formula.
-/

namespace ClassificationSigmaValidity

universe u v w

namespace Formula

variable {Atom : Type v} {Agent : Type w}

/-- Reduction of a basic modal formula after a believed public announcement of
`announcement`.

The only non-Boolean clause is
`[up announcement] box i phi = box i (announcement -> [up announcement] phi)`.
-/
def announcementReduce (announcement : Formula Atom Agent) :
    Formula Atom Agent -> Formula Atom Agent
  | .atom p => .atom p
  | .neg phi => .neg (announcementReduce announcement phi)
  | .conj phi psi =>
      .conj (announcementReduce announcement phi)
        (announcementReduce announcement psi)
  | .box i phi => .box i (imp announcement (announcementReduce announcement phi))

@[simp] theorem announcementReduce_atom (announcement : Formula Atom Agent) (p : Atom) :
    announcementReduce announcement (.atom p) = .atom p := rfl

@[simp] theorem announcementReduce_neg (announcement phi : Formula Atom Agent) :
    announcementReduce announcement (.neg phi) =
      .neg (announcementReduce announcement phi) := rfl

@[simp] theorem announcementReduce_conj (announcement phi psi : Formula Atom Agent) :
    announcementReduce announcement (.conj phi psi) =
      .conj (announcementReduce announcement phi)
        (announcementReduce announcement psi) := rfl

@[simp] theorem announcementReduce_box (announcement phi : Formula Atom Agent) (i : Agent) :
    announcementReduce announcement (.box i phi) =
      .box i (imp announcement (announcementReduce announcement phi)) := rfl

/-- Apply the same announcement reduction `n` times.  The recursion is written
so that it follows the semantic recursion for `Model.iterateUpdate` directly.
-/
def iteratedAnnouncementReduce (announcement : Formula Atom Agent) :
    Nat -> Formula Atom Agent -> Formula Atom Agent
  | 0, phi => phi
  | n + 1, phi =>
      announcementReduce announcement (iteratedAnnouncementReduce announcement n phi)

@[simp] theorem iteratedAnnouncementReduce_zero
    (announcement phi : Formula Atom Agent) :
    iteratedAnnouncementReduce announcement 0 phi = phi := rfl

@[simp] theorem iteratedAnnouncementReduce_succ
    (announcement phi : Formula Atom Agent) (n : Nat) :
    iteratedAnnouncementReduce announcement (n + 1) phi =
      announcementReduce announcement (iteratedAnnouncementReduce announcement n phi) := rfl

/-- Equivalently, one may apply the innermost reduction first. -/
theorem iteratedAnnouncementReduce_succ_apply
    (announcement phi : Formula Atom Agent) (n : Nat) :
    iteratedAnnouncementReduce announcement (n + 1) phi =
      iteratedAnnouncementReduce announcement n (announcementReduce announcement phi) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedAnnouncementReduce_succ]
      exact congrArg (announcementReduce announcement) ih

/-- Iterating for `m + n` steps is composition of the two iterations. -/
theorem iteratedAnnouncementReduce_add
    (announcement phi : Formula Atom Agent) (m n : Nat) :
    iteratedAnnouncementReduce announcement (m + n) phi =
      iteratedAnnouncementReduce announcement m
        (iteratedAnnouncementReduce announcement n phi) := by
  induction m generalizing phi with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, iteratedAnnouncementReduce_succ,
        iteratedAnnouncementReduce_succ, ih]

/-- Reduction can increase modal depth only by the modal depth of the
announcement. -/
theorem modalDepth_announcementReduce_le
    (announcement phi : Formula Atom Agent) :
    modalDepth (announcementReduce announcement phi) <=
      modalDepth phi + modalDepth announcement := by
  induction phi with
  | atom p => simp [announcementReduce, modalDepth]
  | neg phi ih => simpa [announcementReduce, modalDepth] using ih
  | conj phi psi ihPhi ihPsi =>
      simp only [announcementReduce, modalDepth]
      omega
  | box i phi ih =>
      simp only [announcementReduce, modalDepth, modalDepth_imp]
      omega

/-- Announcements have no syntactic effect on modal-depth-zero formulas. -/
theorem announcementReduce_eq_self_of_modalDepth_eq_zero
    (announcement phi : Formula Atom Agent) (hdepth : modalDepth phi = 0) :
    announcementReduce announcement phi = phi := by
  induction phi with
  | atom p => rfl
  | neg phi ih =>
      simp only [modalDepth] at hdepth
      simp [announcementReduce, ih hdepth]
  | conj phi psi ihPhi ihPsi =>
      simp only [modalDepth] at hdepth
      have hPhi : modalDepth phi = 0 := by omega
      have hPsi : modalDepth psi = 0 := by omega
      simp [announcementReduce, ihPhi hPhi, ihPsi hPsi]
  | box i phi =>
      simp [modalDepth] at hdepth

/-- Repeated reductions also leave modal-depth-zero formulas unchanged. -/
theorem iteratedAnnouncementReduce_eq_self_of_modalDepth_eq_zero
    (announcement phi : Formula Atom Agent) (hdepth : modalDepth phi = 0) :
    forall n, iteratedAnnouncementReduce announcement n phi = phi
  | 0 => rfl
  | n + 1 => by
      rw [iteratedAnnouncementReduce_succ,
        iteratedAnnouncementReduce_eq_self_of_modalDepth_eq_zero
          announcement phi hdepth n,
        announcementReduce_eq_self_of_modalDepth_eq_zero announcement phi hdepth]

end Formula

namespace Model

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- Semantic correctness of one-step believed-public-announcement reduction. -/
theorem satisfies_announcementReduce (M : Model World Atom Agent) (x : World)
    (announcement phi : Formula Atom Agent) :
    (M.update announcement).Satisfies x phi <->
      M.Satisfies x (Formula.announcementReduce announcement phi) := by
  induction phi generalizing x with
  | atom p => rfl
  | neg phi ih =>
      simp only [Formula.announcementReduce_neg, satisfies_neg]
      exact not_congr (ih x)
  | conj phi psi ihPhi ihPsi =>
      simp only [Formula.announcementReduce_conj, satisfies_and]
      exact and_congr (ihPhi x) (ihPsi x)
  | box i phi ih =>
      simp only [Formula.announcementReduce_box, satisfies_box, satisfies_imp, update_rel]
      constructor
      · intro h y hxy hyAnnouncement
        exact (ih y).mp (h y ⟨hxy, hyAnnouncement⟩)
      · intro h y hy
        exact (ih y).mpr (h y hy.1 hy.2)

/-- Semantic correctness of iterated reduction and iterated announcement. -/
theorem satisfies_iteratedAnnouncementReduce
    (M : Model World Atom Agent) (x : World)
    (announcement phi : Formula Atom Agent) :
    forall n,
      (M.iterateUpdate announcement n).Satisfies x phi <->
        M.Satisfies x (Formula.iteratedAnnouncementReduce announcement n phi)
  | 0 => Iff.rfl
  | n + 1 => by
      rw [iterateUpdate_succ, satisfies_announcementReduce]
      rw [Formula.iteratedAnnouncementReduce_succ_apply]
      exact satisfies_iteratedAnnouncementReduce M x announcement
        (Formula.announcementReduce announcement phi) n

/-- The announcement trace is represented by an ordinary modal formula. -/
theorem trace_iff_satisfies_iteratedAnnouncementReduce
    (M : Model World Atom Agent) (x : World)
    (phi : Formula Atom Agent) (n : Nat) :
    M.trace x phi n <->
      M.Satisfies x (Formula.iteratedAnnouncementReduce phi n phi) := by
  exact satisfies_iteratedAnnouncementReduce M x phi phi n

/-- A modal-depth-zero formula has the same truth value after one announcement. -/
theorem update_satisfies_iff_of_modalDepth_eq_zero
    (M : Model World Atom Agent) (x : World)
    (announcement phi : Formula Atom Agent) (hdepth : Formula.modalDepth phi = 0) :
    (M.update announcement).Satisfies x phi <-> M.Satisfies x phi := by
  rw [satisfies_announcementReduce,
    Formula.announcementReduce_eq_self_of_modalDepth_eq_zero announcement phi hdepth]

/-- A modal-depth-zero formula has the same truth value after any finite number
of announcements. -/
theorem iterateUpdate_satisfies_iff_of_modalDepth_eq_zero
    (M : Model World Atom Agent) (x : World)
    (announcement phi : Formula Atom Agent) (hdepth : Formula.modalDepth phi = 0)
    (n : Nat) :
    (M.iterateUpdate announcement n).Satisfies x phi <-> M.Satisfies x phi := by
  rw [satisfies_iteratedAnnouncementReduce,
    Formula.iteratedAnnouncementReduce_eq_self_of_modalDepth_eq_zero
      announcement phi hdepth n]

/-- In particular, announcing a modal-depth-zero formula repeatedly produces a
constant truth trace. -/
theorem trace_iff_of_modalDepth_eq_zero
    (M : Model World Atom Agent) (x : World)
    (phi : Formula Atom Agent) (hdepth : Formula.modalDepth phi = 0) (n : Nat) :
    M.trace x phi n <-> M.Satisfies x phi := by
  exact iterateUpdate_satisfies_iff_of_modalDepth_eq_zero
    M x phi phi hdepth n

end Model

end ClassificationSigmaValidity
