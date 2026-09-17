import SourcesOfUnknowability.Static
import SourcesOfUnknowability.DynamicResults
import SourcesOfUnknowability.Eventually
import SourcesOfUnknowability.AgentDNF

/-!
# Numbered static equivalences

The first three clauses of Theorems 3 and 4 are valid with arbitrary agents.
The dynamic always-informative clause of Theorem 3 uses one agent.
-/

namespace SourcesOfUnknowability
namespace Main

open ClassificationSigmaValidity

universe u v w

variable {Atom : Type v} {Agent : Type w}

/-- Theorem 3(1)--(3), and Theorem 4(1)--(3), for KD45. -/
theorem static_equivalences_kd45 (i : Agent) (phi : Formula Atom Agent) :
    (Static.Unbelievable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi ↔
      Static.Unknowable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi) ∧
    (Static.Unknowable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi ↔
      Static.Equivalent
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent) phi
        (Static.moore i phi)) := by
  exact ⟨Static.unbelievable_iff_unknowable_kd45 i phi,
    Static.unknowable_iff_mooreFixed _ i phi⟩

/-- Theorem 3(1)--(3), and Theorem 4(1)--(3), for S5. -/
theorem static_equivalences_s5 (i : Agent) (phi : Formula Atom Agent) :
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi ↔
      Static.Unknowable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi) ∧
    (Static.Unknowable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi ↔
      Static.Equivalent
        (Static.Classes.S5 : FrameClass.{u} Atom Agent) phi
        (Static.moore i phi)) := by
  exact ⟨Static.unbelievable_iff_unknowable_s5 i phi,
    Static.unknowable_iff_mooreFixed _ i phi⟩

/-- Theorem 3(1),(2),(3),(5) in single-agent KD45. -/
theorem static_and_informative_kd45 (phi : Formula Atom Unit) :
    (Static.Unbelievable
        (Static.Classes.KD45 : FrameClass.{u} Atom Unit) () phi ↔
      Static.Unknowable
        (Static.Classes.KD45 : FrameClass.{u} Atom Unit) () phi) ∧
    (Static.Unknowable
        (Static.Classes.KD45 : FrameClass.{u} Atom Unit) () phi ↔
      Static.Equivalent
        (Static.Classes.KD45 : FrameClass.{u} Atom Unit) phi
        (Static.moore () phi)) ∧
    (Static.Unbelievable
        (Static.Classes.KD45 : FrameClass.{u} Atom Unit) () phi ↔
      Dynamic.AlwaysInformative
        (Static.Classes.KD45 : FrameClass.{u} Atom Unit) phi) := by
  exact ⟨Static.unbelievable_iff_unknowable_kd45 () phi,
    Static.unknowable_iff_mooreFixed _ () phi,
    DynamicResults.unbelievable_iff_alwaysInformative_kd45 phi⟩

/-- Theorem 3(1),(2),(3),(5) in single-agent S5. -/
theorem static_and_informative_s5 (phi : Formula Atom Unit) :
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Static.Unknowable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi) ∧
    (Static.Unknowable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Static.Equivalent
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi
        (Static.moore () phi)) ∧
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Dynamic.AlwaysInformative
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi) := by
  exact ⟨Static.unbelievable_iff_unknowable_s5 () phi,
    Static.unknowable_iff_mooreFixed _ () phi,
    DynamicResults.unbelievable_iff_alwaysInformative_s5 phi⟩

/-- Theorem 3(1),(2),(3),(5),(6), including arbitrary infinite S5 models. -/
theorem static_dynamic_equivalences_s5 (phi : Formula Atom Unit) :
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Static.Unknowable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi) ∧
    (Static.Unknowable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Static.Equivalent
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi
        (Static.moore () phi)) ∧
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Dynamic.AlwaysInformative
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi) ∧
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Dynamic.EventuallySelfRefuting
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi) := by
  exact ⟨Static.unbelievable_iff_unknowable_s5 () phi,
    Static.unknowable_iff_mooreFixed _ () phi,
    DynamicResults.unbelievable_iff_alwaysInformative_s5 phi,
    Eventually.unbelievable_iff_eventuallySelfRefuting_s5 phi⟩

/-- Theorem 3, including the normal-form subset condition (4), stated for
any supplied semantically equivalent finite family of clauses. -/
theorem theorem3_s5 (phi : Formula Atom Unit)
    (clauses : List (AgentDNF.Clause Atom Unit))
    (hform : ∀ {World : Type u} (M : Model World Atom Unit), IsK45 M → ∀ x : World,
      M.Satisfies x phi ↔ AgentDNF.HoldsDNF clauses M x ()) :
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Static.Unknowable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi) ∧
    (Static.Unknowable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Static.Equivalent
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi
        (Static.moore () phi)) ∧
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      ∀ (World : Type u) (M : Model World Atom Unit), IsS5 M → ∀ x,
        ¬ AgentDNF.DecomposedWeak clauses M x ()) ∧
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Dynamic.AlwaysInformative
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi) ∧
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Dynamic.EventuallySelfRefuting
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi) := by
  exact ⟨Static.unbelievable_iff_unknowable_s5 () phi,
    Static.unknowable_iff_mooreFixed _ () phi,
    AgentDNF.unbelievable_iff_no_decomposedWeak_s5 clauses phi () hform,
    DynamicResults.unbelievable_iff_alwaysInformative_s5 phi,
    Eventually.unbelievable_iff_eventuallySelfRefuting_s5 phi⟩

/-- Theorem 4, the multi-agent static equivalences for KD45, including the
subset decomposition of a supplied `i`-DNF. -/
theorem theorem4_kd45 (i : Agent) (phi : Formula Atom Agent)
    (clauses : List (AgentDNF.Clause Atom Agent))
    (hform : ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x : World,
      M.Satisfies x phi ↔ AgentDNF.HoldsDNF clauses M x i) :
    (Static.Unbelievable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi ↔
      Static.Unknowable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi) ∧
    (Static.Unknowable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi ↔
      Static.Equivalent
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent) phi
        (Static.moore i phi)) ∧
    (Static.Unbelievable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi ↔
      ∀ (World : Type u) (M : Model World Atom Agent), IsKD45 M → ∀ x,
        ¬ AgentDNF.DecomposedWeak clauses M x i) := by
  exact ⟨Static.unbelievable_iff_unknowable_kd45 i phi,
    Static.unknowable_iff_mooreFixed _ i phi,
    AgentDNF.unbelievable_iff_no_decomposedWeak_kd45 clauses phi i hform⟩

theorem theorem4_s5 (i : Agent) (phi : Formula Atom Agent)
    (clauses : List (AgentDNF.Clause Atom Agent))
    (hform : ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x : World,
      M.Satisfies x phi ↔ AgentDNF.HoldsDNF clauses M x i) :
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi ↔
      Static.Unknowable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi) ∧
    (Static.Unknowable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi ↔
      Static.Equivalent
        (Static.Classes.S5 : FrameClass.{u} Atom Agent) phi
        (Static.moore i phi)) ∧
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi ↔
      ∀ (World : Type u) (M : Model World Atom Agent), IsS5 M → ∀ x,
        ¬ AgentDNF.DecomposedWeak clauses M x i) := by
  exact ⟨Static.unbelievable_iff_unknowable_s5 i phi,
    Static.unknowable_iff_mooreFixed _ i phi,
    AgentDNF.unbelievable_iff_no_decomposedWeak_s5 clauses phi i hform⟩

end Main
end SourcesOfUnknowability
