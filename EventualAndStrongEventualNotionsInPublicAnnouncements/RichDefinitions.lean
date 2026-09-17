import EventualAndStrongEventualNotionsInPublicAnnouncements.RichFoundation
import EventualAndStrongEventualNotionsInPublicAnnouncements.FiniteConditions

/-!
# Eventuality for common belief and nested announcements

Definitions for the richer languages in Remark 1. `BPALCFormula` permits
arbitrarily nested common belief and believed announcements. Every global
condition quantifies over all K45 models in the indicated universe; witnessing
times may depend on the model and distinguished world. Common belief uses
positive transitive closure.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements.Rich

open ClassificationSigmaValidity

universe u v w

variable {Atom : Type v} {Agent : Type w}

/-- Common belief, with a path of positive length. -/
def Common {World : Type u} (M : Model World Atom Agent)
    (x : World) (φ : BPALCFormula Atom Agent) : Prop :=
  ∀ y, Relation.TransGen M.AnyStep x y → M.rSatisfies y φ

/-- Eventual transition from truth value `i` to truth value `j`. -/
def Eventual (i j : Bool) (φ : BPALCFormula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (M.rSatisfies x φ) →
      ∃ n : Nat, 1 ≤ n ∧ HoldsBit j (M.rTrace x φ n)

/-- Strong eventual transition; the required value holds at every later stage. -/
def StrongEventual (i j : Bool) (φ : BPALCFormula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (M.rSatisfies x φ) →
      ∃ N : Nat, 1 ≤ N ∧ ∀ n, N ≤ n → HoldsBit j (M.rTrace x φ n)

/-- The finite-stage S condition. -/
def StageCondition (i j : Bool) (k : Nat) (φ : BPALCFormula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (M.rSatisfies x φ) →
      Common (M.rIterateUpdate φ k) x φ → HoldsBit j (M.rTrace x φ k)

def FiniteStageCondition (i j : Bool) (φ : BPALCFormula Atom Agent) : Prop :=
  ∀ k, StageCondition.{u} i j k φ

/-- A uniform finite bound is independent of the model and the point. -/
def UniformBound (i j : Bool) (φ : BPALCFormula Atom Agent) : Prop :=
  ∃ N : Nat, 1 ≤ N ∧
    ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
      HoldsBit i (M.rSatisfies x φ) →
        ∃ n : Nat, 1 ≤ n ∧ n ≤ N ∧ HoldsBit j (M.rTrace x φ n)

/-- Equality of the generated submodels before and after the announcement,
expressed on their shared ambient carrier to avoid dependent-type equality. -/
def GeneratedUnchanged {World : Type u} (M : Model World Atom Agent)
    (x : World) (φ : BPALCFormula Atom Agent) : Prop :=
  (M.rUpdate φ).generatedSet x = M.generatedSet x ∧
    M.LocallyAgrees (M.rUpdate φ) (M.generatedSet x)

def AlwaysInformative (i : Bool) (φ : BPALCFormula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (M.rSatisfies x φ) → ¬ GeneratedUnchanged M x φ

end EventualAndStrongEventualNotionsInPublicAnnouncements.Rich
