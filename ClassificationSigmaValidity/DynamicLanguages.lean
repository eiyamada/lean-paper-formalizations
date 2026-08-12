import ClassificationSigmaValidity.Semantics

/-!
# Semantics of the introductory dynamic languages

The classification concerns basic modal announcements, but the paper also
introduces PAL and BPAL syntax.  We give their standard recursive semantics
using explicit domains/relations, avoiding any hidden well-foundedness or
choice assumptions.
-/

namespace ClassificationSigmaValidity

universe u v w

namespace PAL

/-- Truth of a PAL formula relative to an ambient model and a current public
domain.  Modal quantification is restricted to that domain; an announcement
intersects it with the truth set of the announced formula. -/
def Satisfies {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) :
    (domain : World -> Prop) -> World -> PALFormula Atom Agent -> Prop
  | _domain, x, .atom p => M.val p x
  | domain, x, .neg phi => Not (Satisfies M domain x phi)
  | domain, x, .conj phi psi =>
      Satisfies M domain x phi /\ Satisfies M domain x psi
  | domain, x, .box i phi =>
      forall y, domain y -> M.rel i x y -> Satisfies M domain y phi
  | domain, x, .announce phi psi =>
      Satisfies M domain x phi ->
        Satisfies M (fun y => domain y /\ Satisfies M domain y phi) x psi

/-- Truth in the initial (unrestricted) public model. -/
def InitiallySatisfies {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) (x : World) (phi : PALFormula Atom Agent) : Prop :=
  Satisfies M (fun _ => True) x phi

@[simp] theorem satisfies_atom {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) (domain : World -> Prop) (x : World) (p : Atom) :
    Satisfies M domain x (.atom p) <-> M.val p x := Iff.rfl

@[simp] theorem satisfies_neg {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) (domain : World -> Prop) (x : World)
    (phi : PALFormula Atom Agent) :
    Satisfies M domain x (.neg phi) <-> Not (Satisfies M domain x phi) := Iff.rfl

@[simp] theorem satisfies_conj {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) (domain : World -> Prop) (x : World)
    (phi psi : PALFormula Atom Agent) :
    Satisfies M domain x (.conj phi psi) <->
      Satisfies M domain x phi /\ Satisfies M domain x psi := Iff.rfl

@[simp] theorem satisfies_box {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) (domain : World -> Prop) (x : World)
    (i : Agent) (phi : PALFormula Atom Agent) :
    Satisfies M domain x (.box i phi) <->
      forall y, domain y -> M.rel i x y -> Satisfies M domain y phi := Iff.rfl

@[simp] theorem satisfies_announce {World : Type u} {Atom : Type v}
    {Agent : Type w} (M : Model World Atom Agent) (domain : World -> Prop)
    (x : World) (phi psi : PALFormula Atom Agent) :
    Satisfies M domain x (.announce phi psi) <->
      (Satisfies M domain x phi ->
        Satisfies M (fun y => domain y /\ Satisfies M domain y phi) x psi) :=
  Iff.rfl

end PAL

namespace BPAL

/-- Truth of a BPAL formula relative to the arrows currently retained from an
ambient model.  An announcement keeps precisely the arrows whose target makes
the announcement true under the current arrows. -/
def Satisfies {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) :
    (currentRel : Agent -> World -> World -> Prop) ->
      World -> BPALFormula Atom Agent -> Prop
  | _currentRel, x, .atom p => M.val p x
  | currentRel, x, .neg phi => Not (Satisfies M currentRel x phi)
  | currentRel, x, .conj phi psi =>
      Satisfies M currentRel x phi /\ Satisfies M currentRel x psi
  | currentRel, x, .box i phi =>
      forall y, currentRel i x y -> Satisfies M currentRel y phi
  | currentRel, x, .announce phi psi =>
      Satisfies M
        (fun i y z => currentRel i y z /\ Satisfies M currentRel z phi) x psi

/-- Truth in the initial believed-announcement model. -/
def InitiallySatisfies {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) (x : World) (phi : BPALFormula Atom Agent) : Prop :=
  Satisfies M M.rel x phi

@[simp] theorem satisfies_atom {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) (R : Agent -> World -> World -> Prop)
    (x : World) (p : Atom) :
    Satisfies M R x (.atom p) <-> M.val p x := Iff.rfl

@[simp] theorem satisfies_neg {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) (R : Agent -> World -> World -> Prop)
    (x : World) (phi : BPALFormula Atom Agent) :
    Satisfies M R x (.neg phi) <-> Not (Satisfies M R x phi) := Iff.rfl

@[simp] theorem satisfies_conj {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) (R : Agent -> World -> World -> Prop)
    (x : World) (phi psi : BPALFormula Atom Agent) :
    Satisfies M R x (.conj phi psi) <->
      Satisfies M R x phi /\ Satisfies M R x psi := Iff.rfl

@[simp] theorem satisfies_box {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) (R : Agent -> World -> World -> Prop)
    (x : World) (i : Agent) (phi : BPALFormula Atom Agent) :
    Satisfies M R x (.box i phi) <->
      forall y, R i x y -> Satisfies M R y phi := Iff.rfl

@[simp] theorem satisfies_announce {World : Type u} {Atom : Type v}
    {Agent : Type w} (M : Model World Atom Agent)
    (R : Agent -> World -> World -> Prop) (x : World)
    (phi psi : BPALFormula Atom Agent) :
    Satisfies M R x (.announce phi psi) <->
      Satisfies M (fun i y z => R i y z /\ Satisfies M R z phi) x psi := Iff.rfl

end BPAL

end ClassificationSigmaValidity
