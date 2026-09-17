import SourcesOfUnknowability.Static
import SourcesOfUnknowability.Dynamic

/-!
# Static belief and public-announcement informativeness

These are the general implications in Remark 2 and the single-agent KD45/S5
equivalence between unbelievability and always informativeness.  The proof of
the converse restricts a model to the complete successor cluster of a point
where `box phi` holds.
-/

namespace SourcesOfUnknowability.DynamicResults

open ClassificationSigmaValidity
open SourcesOfUnknowability

universe u v

variable {Atom : Type v}

private theorem successor_cluster_closed
    {World : Type u} (M : Model World Atom Unit) (w : World)
    (ht : Frame.Transitive (M.rel ())) :
    M.ForwardClosed {x | M.rel () w x} := by
  intro x hx i y hxy
  have hi : i = () := Subsingleton.elim i ()
  subst i
  exact ht hx hxy

/-- In a single-agent KD45 model, a believable formula can be announced to
an entire serial successor cluster without removing any world. -/
theorem believable_implies_not_alwaysInformative_kd45
    (phi : Formula Atom Unit)
    (h : Static.Believable
      (Static.Classes.KD45 : FrameClass.{u} Atom Unit) () phi) :
    ¬ Dynamic.AlwaysInformative
      (Static.Classes.KD45 : FrameClass.{u} Atom Unit) phi := by
  rintro hAlways
  obtain ⟨World, M, hM, w, hbox⟩ := h
  let U : Set World := {x | M.rel () w x}
  have hU : M.ForwardClosed U :=
    successor_cluster_closed M w (hM ()).2.1
  let N : Model (Subtype U) Atom Unit := M.restrict U
  have hN : IsKD45 N := M.restrict_isKD45 hM U hU
  have hAll : ∀ x : Subtype U, N.Satisfies x phi := by
    intro x
    exact (M.restrict_satisfies_iff U hU x phi).2 (hbox x.1 x.2)
  obtain ⟨v, hv⟩ := (hM ()).1 w
  let vU : Subtype U := ⟨v, hv⟩
  apply hAlways N hN vU (hAll vU)
  ext x
  exact ⟨fun _ => Set.mem_univ x, fun _ => hAll x⟩

/-- In a single-agent S5 model, a believable formula is true throughout one
complete equivalence class. -/
theorem believable_implies_not_alwaysInformative_s5
    (phi : Formula Atom Unit)
    (h : Static.Believable
      (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi) :
    ¬ Dynamic.AlwaysInformative
      (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi := by
  rintro hAlways
  obtain ⟨World, M, hM, w, hbox⟩ := h
  let U : Set World := {x | M.rel () w x}
  have hU : M.ForwardClosed U :=
    successor_cluster_closed M w (hM ()).2.1
  let N : Model (Subtype U) Atom Unit := M.restrict U
  have hN : IsS5 N := M.restrict_isS5 hM U
  have hAll : ∀ x : Subtype U, N.Satisfies x phi := by
    intro x
    exact (M.restrict_satisfies_iff U hU x phi).2 (hbox x.1 x.2)
  let wU : Subtype U := ⟨w, (hM ()).1 w⟩
  apply hAlways N hN wU (hAll wU)
  ext x
  exact ⟨fun _ => Set.mem_univ x, fun _ => hAll x⟩

/-- Theorem 3(1) iff (5), also valid for single-agent KD45 as in Remark 2. -/
theorem unbelievable_iff_alwaysInformative_kd45
    (phi : Formula Atom Unit) :
    Static.Unbelievable
      (Static.Classes.KD45 : FrameClass.{u} Atom Unit) () phi ↔
    Dynamic.AlwaysInformative
      (Static.Classes.KD45 : FrameClass.{u} Atom Unit) phi := by
  constructor
  · intro h
    apply Dynamic.unbelievable_implies_alwaysInformative _ () phi
    intro World M hM x hbox
    exact h ⟨World, M, hM, x, hbox⟩
  · intro h
    exact fun hb => believable_implies_not_alwaysInformative_kd45 phi hb h

theorem unbelievable_iff_alwaysInformative_s5
    (phi : Formula Atom Unit) :
    Static.Unbelievable
      (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
    Dynamic.AlwaysInformative
      (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi := by
  constructor
  · intro h
    apply Dynamic.unbelievable_implies_alwaysInformative _ () phi
    intro World M hM x hbox
    exact h ⟨World, M, hM, x, hbox⟩
  · intro h
    exact fun hb => believable_implies_not_alwaysInformative_s5 phi hb h

/-- The part of Remark 2 that holds in every frame class. -/
theorem eventuallySelfRefuting_implies_alwaysInformative
    (C : FrameClass.{u} Atom Unit) (phi : Formula Atom Unit) :
    Dynamic.EventuallySelfRefuting C phi →
      Dynamic.AlwaysInformative C phi :=
  Dynamic.eventuallySelfRefuting_implies_alwaysInformative C phi

theorem eventuallySelfRefuting_implies_unbelievable_s5
    (phi : Formula Atom Unit) :
    Dynamic.EventuallySelfRefuting
      (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi →
    Static.Unbelievable
      (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi := by
  intro h
  exact (unbelievable_iff_alwaysInformative_s5 phi).2
    (Dynamic.eventuallySelfRefuting_implies_alwaysInformative _ phi h)

theorem eventuallySelfRefuting_implies_unbelievable_kd45
    (phi : Formula Atom Unit) :
    Dynamic.EventuallySelfRefuting
      (Static.Classes.KD45 : FrameClass.{u} Atom Unit) phi →
    Static.Unbelievable
      (Static.Classes.KD45 : FrameClass.{u} Atom Unit) () phi := by
  intro h
  exact (unbelievable_iff_alwaysInformative_kd45 phi).2
    (Dynamic.eventuallySelfRefuting_implies_alwaysInformative _ phi h)

end SourcesOfUnknowability.DynamicResults
