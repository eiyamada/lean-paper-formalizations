import ClassificationSigmaValidity.Patterns

/-!
# Standard frame classes used by the classification
-/

namespace ClassificationSigmaValidity

universe u v w

namespace Classes


def All {Atom : Type v} {Agent : Type w} : FrameClass.{u} Atom Agent :=
  fun _ => True

def K45 {Atom : Type v} {Agent : Type w} : FrameClass.{u} Atom Agent :=
  fun M => IsK45 M

def KD45 {Atom : Type v} {Agent : Type w} : FrameClass.{u} Atom Agent :=
  fun M => IsKD45 M

def S5 {Atom : Type v} {Agent : Type w} : FrameClass.{u} Atom Agent :=
  fun M => IsS5 M

theorem s5_subset_kd45 {Atom : Type v} {Agent : Type w}
    {World : Type u} {M : Model World Atom Agent} :
    S5 M -> KD45 M := IsS5.isKD45

theorem kd45_subset_k45 {Atom : Type v} {Agent : Type w}
    {World : Type u} {M : Model World Atom Agent} :
    KD45 M -> K45 M := IsKD45.isK45

theorem s5_subset_k45 {Atom : Type v} {Agent : Type w}
    {World : Type u} {M : Model World Atom Agent} :
    S5 M -> K45 M := IsS5.isK45

end Classes

namespace Sigma

variable {Atom : Type v} {Agent : Type w}

theorem valid_mono_class {C D : FrameClass.{u} Atom Agent}
    (hsub : forall {World : Type u} (M : Model World Atom Agent), D M -> C M)
    {phi : Formula Atom Agent} {sigma : Pattern}
    (h : Valid C phi sigma) : Valid D phi sigma := by
  intro World M hM x hx
  exact h M (hsub M hM) x hx

theorem satisfiable_mono_class {C D : FrameClass.{u} Atom Agent}
    (hsub : forall {World : Type u} (M : Model World Atom Agent), C M -> D M)
    {phi : Formula Atom Agent} {sigma : Pattern}
    (h : Satisfiable C phi sigma) : Satisfiable D phi sigma := by
  rcases h with ⟨World, M, hM, x, hx⟩
  exact ⟨World, M, hsub M hM, x, hx⟩

end Sigma

end ClassificationSigmaValidity
