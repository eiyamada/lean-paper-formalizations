import SourcesOfUnknowability.Dynamic

/-!
# Remark 2: eventual refutation on serial transitive frames

A believer has an accessible successor whose truth persists through every
repeated public announcement. The proof stays in the original model, so it
applies to any frame class whose members are serial and transitive, without
assuming that the class is closed under generated submodels.
-/

namespace SourcesOfUnknowability.Remark2

open ClassificationSigmaValidity

universe u v

variable {Atom : Type v}

/-- If every successor of `root` remains in the announced carrier, evaluating
any formula at such a successor is unchanged. Transitivity ensures every
world reached later is still a successor of `root`. -/
private theorem satisfiesOn_iff_at_successor
    {World : Type u} (M : Model World Atom Unit) (root : World)
    (htrans : Frame.Transitive (M.rel ())) (U : Set World)
    (hU : ∀ y, M.rel () root y → y ∈ U)
    (y : World) (hry : M.rel () root y)
    (phi : Formula Atom Unit) :
    Dynamic.SatisfiesOn M U y phi ↔ M.Satisfies y phi := by
  induction phi generalizing y with
  | atom p => rfl
  | neg psi ih => exact not_congr (ih y hry)
  | conj psi theta ihPsi ihTheta =>
      exact and_congr (ihPsi y hry) (ihTheta y hry)
  | box i psi ih =>
      cases i
      constructor
      · intro h z hyz
        have hrz : M.rel () root z := htrans hry hyz
        exact (ih z hrz).mp (h z (hU z hrz) hyz)
      · intro h z hzU hyz
        exact (ih z (htrans hry hyz)).mpr (h z hyz)

/-- Every successor of a believer survives every repeated announcement of
the believed formula, provided accessibility is transitive. -/
private theorem successor_survives_all
    {World : Type u} (M : Model World Atom Unit)
    (htrans : Frame.Transitive (M.rel ()))
    (phi : Formula Atom Unit) (root : World)
    (hbox : M.Satisfies root (.box () phi)) :
    ∀ n (y : World), M.rel () root y →
      y ∈ Dynamic.survivors M phi n := by
  intro n
  induction n with
  | zero =>
      intro y hry
      trivial
  | succ n ih =>
      intro y hry
      constructor
      · exact ih y hry
      · exact (satisfiesOn_iff_at_successor M root htrans
          (Dynamic.survivors M phi n) (fun z hrz => ih z hrz)
          y hry phi).2 (hbox y hry)

/-- Remark 2's general KD4 direction: eventual self-refutation entails
unbelievability in every single-agent class whose relations are serial and
transitive. -/
theorem eventuallySelfRefuting_implies_unbelievable_of_serial_transitive
    (C : FrameClass.{u} Atom Unit)
    (hC : ∀ {World : Type u} (M : Model World Atom Unit),
      C M → Frame.Serial (M.rel ()) ∧ Frame.Transitive (M.rel ()))
    (phi : Formula Atom Unit) :
    Dynamic.EventuallySelfRefuting C phi →
      Static.Unbelievable C () phi := by
  intro hEventual ⟨World, M, hM, root, hbox⟩
  obtain ⟨hserial, htrans⟩ := hC M hM
  obtain ⟨y, hry⟩ := hserial root
  have hyphi : M.Satisfies y phi := hbox y hry
  obtain ⟨n, hn⟩ := hEventual M hM y hyphi
  apply hn
  have hall := successor_survives_all M htrans phi root hbox
  exact (Dynamic.trueAfter_iff_survives_succ M phi n y).2
    (hall (n + 1) y hry)

/-- The exact single-agent KD4 class. -/
def KD4 : FrameClass.{u} Atom Unit :=
  fun M => Frame.Serial (M.rel ()) ∧ Frame.Transitive (M.rel ())

theorem eventuallySelfRefuting_implies_unbelievable_kd4
    (phi : Formula Atom Unit) :
    Dynamic.EventuallySelfRefuting (KD4 : FrameClass.{u} Atom Unit) phi →
      Static.Unbelievable (KD4 : FrameClass.{u} Atom Unit) () phi := by
  exact eventuallySelfRefuting_implies_unbelievable_of_serial_transitive
    KD4 (fun M hM => hM) phi

end SourcesOfUnknowability.Remark2
