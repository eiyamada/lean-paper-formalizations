import ClassificationSigmaValidity.Locality
import ClassificationSigmaValidity.FiniteDynamics
import ClassificationSigmaValidity.DynamicLanguages
import ClassificationSigmaValidity.Patterns

/-!
# Eventual and Strong Eventual Notions in Public Announcements

Definitions for Eiji Yamada's manuscript. The underlying syntax, models and
believed announcement operation are shared with the sigma-validity development.
Every global condition quantifies over all K45 models in the indicated universe;
the witnessing time may depend on both the model and the distinguished world.
Common belief uses positive transitive closure, as in the manuscript.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity

universe u v w

variable {Atom : Type v} {Agent : Type w}

abbrev HoldsBit := Pattern.HoldsBit

/-- Common belief, with a path of positive length. -/
def Common {World : Type u} (M : Model World Atom Agent)
    (x : World) (φ : Formula Atom Agent) : Prop :=
  ∀ y, Relation.TransGen M.AnyStep x y → M.Satisfies y φ

/-- Eventual transition from truth value `i` to truth value `j`. -/
def Eventual (i j : Bool) (φ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (M.Satisfies x φ) →
      ∃ n : Nat, 1 ≤ n ∧ HoldsBit j (M.trace x φ n)

/-- Strong eventual transition; the required value holds at every later stage. -/
def StrongEventual (i j : Bool) (φ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (M.Satisfies x φ) →
      ∃ N : Nat, 1 ≤ N ∧ ∀ n, N ≤ n → HoldsBit j (M.trace x φ n)

/-- The finite-stage S condition. -/
def StageCondition (i j : Bool) (k : Nat) (φ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (M.Satisfies x φ) →
      Common (M.iterateUpdate φ k) x φ → HoldsBit j (M.trace x φ k)

def FiniteStageCondition (i j : Bool) (φ : Formula Atom Agent) : Prop :=
  ∀ k, StageCondition.{u} i j k φ

/-- A uniform finite bound is independent of the model and the point. -/
def UniformBound (i j : Bool) (φ : Formula Atom Agent) : Prop :=
  ∃ N : Nat, 1 ≤ N ∧
    ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
      HoldsBit i (M.Satisfies x φ) →
        ∃ n : Nat, 1 ≤ n ∧ n ≤ N ∧ HoldsBit j (M.trace x φ n)

/-- Equality of the generated submodels before and after the announcement,
expressed on their shared ambient carrier to avoid dependent-type equality. -/
def GeneratedUnchanged {World : Type u} (M : Model World Atom Agent)
    (x : World) (φ : Formula Atom Agent) : Prop :=
  (M.update φ).generatedSet x = M.generatedSet x ∧
    M.LocallyAgrees (M.update φ) (M.generatedSet x)

def AlwaysInformative (i : Bool) (φ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (M.Satisfies x φ) → ¬ GeneratedUnchanged M x φ

/-- The target truth value occurs arbitrarily late. -/
def CofinalValue (j : Bool) (t : Nat → Prop) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ HoldsBit j (t n)

/-- The binary trace converges to the target value. -/
def ConvergesTo (j : Bool) (t : Nat → Prop) : Prop :=
  ∃ N, ∀ n, N ≤ n → HoldsBit j (t n)

end EventualAndStrongEventualNotionsInPublicAnnouncements
