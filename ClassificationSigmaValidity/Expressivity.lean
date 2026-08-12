import ClassificationSigmaValidity.DynamicLanguages
import ClassificationSigmaValidity.Reduction

/-!
# Expressive equivalence of PAL, BPAL, and the basic modal language

The paper recalls that, on Kripke models, both public-announcement logic and
believed public-announcement logic are no more expressive than the basic modal
language.  This module proves that statement for formulas with arbitrarily
nested announcements.

For PAL, the translation of `[!phi] psi` contains the usual precondition
implication.  For BPAL, announcements merely remove arrows, so its translation
is the unguarded believed-announcement reduction from `Reduction.lean`.
-/

namespace ClassificationSigmaValidity

set_option autoImplicit false

universe u v w

namespace PALFormula

/-- Eliminate every (possibly nested) public announcement. -/
def toFormula {Atom : Type v} {Agent : Type w} :
    PALFormula Atom Agent -> Formula Atom Agent
  | .atom p => .atom p
  | .neg phi => .neg (toFormula phi)
  | .conj phi psi => .conj (toFormula phi) (toFormula psi)
  | .box i phi => .box i (toFormula phi)
  | .announce phi psi =>
      Formula.imp (toFormula phi)
        (Formula.announcementReduce (toFormula phi) (toFormula psi))

end PALFormula

namespace BPALFormula

/-- Eliminate every (possibly nested) believed public announcement. -/
def toFormula {Atom : Type v} {Agent : Type w} :
    BPALFormula Atom Agent -> Formula Atom Agent
  | .atom p => .atom p
  | .neg phi => .neg (toFormula phi)
  | .conj phi psi => .conj (toFormula phi) (toFormula psi)
  | .box i phi => .box i (toFormula phi)
  | .announce phi psi =>
      Formula.announcementReduce (toFormula phi) (toFormula psi)

end BPALFormula

namespace Formula

/-- Regard a basic modal formula as a PAL formula. -/
def toPAL {Atom : Type v} {Agent : Type w} :
    Formula Atom Agent -> PALFormula Atom Agent
  | .atom p => .atom p
  | .neg phi => .neg (toPAL phi)
  | .conj phi psi => .conj (toPAL phi) (toPAL psi)
  | .box i phi => .box i (toPAL phi)

/-- Regard a basic modal formula as a BPAL formula. -/
def toBPAL {Atom : Type v} {Agent : Type w} :
    Formula Atom Agent -> BPALFormula Atom Agent
  | .atom p => .atom p
  | .neg phi => .neg (toBPAL phi)
  | .conj phi psi => .conj (toBPAL phi) (toBPAL psi)
  | .box i phi => .box i (toBPAL phi)

end Formula

namespace PALFormula

/-- Eliminating announcements after embedding a basic formula is the identity. -/
@[simp] theorem toFormula_toPAL {Atom : Type v} {Agent : Type w}
    (phi : Formula Atom Agent) : toFormula (Formula.toPAL phi) = phi := by
  induction phi with
  | atom p => rfl
  | neg phi ih => simp [Formula.toPAL, toFormula, ih]
  | conj phi psi ihPhi ihPsi =>
      simp [Formula.toPAL, toFormula, ihPhi, ihPsi]
  | box i phi ih => simp [Formula.toPAL, toFormula, ih]

end PALFormula

namespace BPALFormula

/-- Eliminating announcements after embedding a basic formula is the identity. -/
@[simp] theorem toFormula_toBPAL {Atom : Type v} {Agent : Type w}
    (phi : Formula Atom Agent) : toFormula (Formula.toBPAL phi) = phi := by
  induction phi with
  | atom p => rfl
  | neg phi ih => simp [Formula.toBPAL, toFormula, ih]
  | conj phi psi ihPhi ihPsi =>
      simp [Formula.toBPAL, toFormula, ihPhi, ihPsi]
  | box i phi ih => simp [Formula.toBPAL, toFormula, ih]

end BPALFormula

namespace PAL

/-- A same-world presentation of the current PAL submodel.  Restricting only
targets is enough: every state reached while evaluating inside the current
domain is itself in that domain.  This presentation also makes the update
identity used by the reduction proof literal. -/
def domainModel {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) (domain : World -> Prop) :
    Model World Atom Agent where
  rel i x y := domain y /\ M.rel i x y
  val := M.val

@[simp] theorem domainModel_rel {World : Type u} {Atom : Type v}
    {Agent : Type w} (M : Model World Atom Agent) (domain : World -> Prop)
    (i : Agent) (x y : World) :
    (domainModel M domain).rel i x y <-> domain y /\ M.rel i x y := Iff.rfl

@[simp] theorem domainModel_val {World : Type u} {Atom : Type v}
    {Agent : Type w} (M : Model World Atom Agent) (domain : World -> Prop)
    (p : Atom) (x : World) :
    (domainModel M domain).val p x <-> M.val p x := Iff.rfl

/-- The unrestricted same-world presentation is the original model. -/
theorem domainModel_true {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) :
    domainModel M (fun _ => True) = M := by
  apply Model.ext'
  · intro i x y
    simp
  · intro p x
    rfl

/-- Correctness of PAL announcement elimination, relative to an arbitrary
current public domain. -/
theorem satisfies_toFormula {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) :
    forall (domain : World -> Prop) (x : World) (phi : PALFormula Atom Agent),
      Satisfies M domain x phi <->
        (domainModel M domain).Satisfies x (PALFormula.toFormula phi) := by
  intro domain x phi
  induction phi generalizing domain x with
  | atom p => rfl
  | neg phi ih =>
      simp only [satisfies_neg, PALFormula.toFormula, Model.satisfies_neg]
      exact not_congr (ih domain x)
  | conj phi psi ihPhi ihPsi =>
      simp only [satisfies_conj, PALFormula.toFormula, Model.satisfies_and]
      exact and_congr (ihPhi domain x) (ihPsi domain x)
  | box i phi ih =>
      simp only [satisfies_box, PALFormula.toFormula, Model.satisfies_box,
        domainModel_rel]
      constructor
      · intro h y hy
        exact (ih domain y).mp (h y hy.1 hy.2)
      · intro h y hyDomain hxy
        exact (ih domain y).mpr (h y ⟨hyDomain, hxy⟩)
  | announce phi psi ihPhi ihPsi =>
      simp only [satisfies_announce, PALFormula.toFormula,
        Model.satisfies_imp]
      let nextDomain : World -> Prop :=
        fun y => domain y /\ Satisfies M domain y phi
      have hUpdate :
          domainModel M nextDomain =
            (domainModel M domain).update (PALFormula.toFormula phi) := by
        apply Model.ext'
        · intro i y z
          change ((domain z /\ Satisfies M domain z phi) /\ M.rel i y z) <->
            ((domain z /\ M.rel i y z) /\
              (domainModel M domain).Satisfies z (PALFormula.toFormula phi))
          rw [← ihPhi domain z]
          tauto
        · intro p y
          rfl
      constructor
      · intro h hPhiBasic
        have hPhiPAL : Satisfies M domain x phi :=
          (ihPhi domain x).mpr hPhiBasic
        have hPsiPAL : Satisfies M nextDomain x psi := h hPhiPAL
        have hPsiUpdated :
            ((domainModel M domain).update (PALFormula.toFormula phi)).Satisfies
              x (PALFormula.toFormula psi) := by
          rw [← hUpdate]
          exact (ihPsi nextDomain x).mp hPsiPAL
        exact (Model.satisfies_announcementReduce
          (domainModel M domain) x (PALFormula.toFormula phi)
            (PALFormula.toFormula psi)).mp hPsiUpdated
      · intro h hPhiPAL
        have hPhiBasic :
            (domainModel M domain).Satisfies x (PALFormula.toFormula phi) :=
          (ihPhi domain x).mp hPhiPAL
        have hPsiUpdated :
            ((domainModel M domain).update (PALFormula.toFormula phi)).Satisfies
              x (PALFormula.toFormula psi) :=
          (Model.satisfies_announcementReduce
            (domainModel M domain) x (PALFormula.toFormula phi)
              (PALFormula.toFormula psi)).mpr (h hPhiBasic)
        have hPsiDomain :
            (domainModel M nextDomain).Satisfies x
              (PALFormula.toFormula psi) := by
          rw [hUpdate]
          exact hPsiUpdated
        exact (ihPsi nextDomain x).mpr hPsiDomain

/-- Announcement elimination is correct in the initial public model. -/
theorem initiallySatisfies_toFormula {World : Type u} {Atom : Type v}
    {Agent : Type w} (M : Model World Atom Agent) (x : World)
    (phi : PALFormula Atom Agent) :
    InitiallySatisfies M x phi <->
      M.Satisfies x (PALFormula.toFormula phi) := by
  rw [InitiallySatisfies, satisfies_toFormula, domainModel_true]

/-- The basic-to-PAL embedding preserves truth at every current domain. -/
theorem satisfies_toPAL {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) (domain : World -> Prop) (x : World)
    (phi : Formula Atom Agent) :
    Satisfies M domain x (Formula.toPAL phi) <->
      (domainModel M domain).Satisfies x phi := by
  simpa using satisfies_toFormula M domain x (Formula.toPAL phi)

/-- The basic-to-PAL embedding preserves truth in the initial model. -/
theorem initiallySatisfies_toPAL {World : Type u} {Atom : Type v}
    {Agent : Type w} (M : Model World Atom Agent) (x : World)
    (phi : Formula Atom Agent) :
    InitiallySatisfies M x (Formula.toPAL phi) <-> M.Satisfies x phi := by
  simpa using initiallySatisfies_toFormula M x (Formula.toPAL phi)

/-- PAL and the basic modal language have equal expressive power on pointed
Kripke models (at any fixed universe level of worlds). -/
theorem equiexpressive_with_basic (Atom : Type v) (Agent : Type w) :
    (forall phi : PALFormula Atom Agent,
      exists psi : Formula Atom Agent,
        forall (World : Type u) (M : Model World Atom Agent) (x : World),
          InitiallySatisfies M x phi <-> M.Satisfies x psi) /\
    (forall psi : Formula Atom Agent,
      exists phi : PALFormula Atom Agent,
        forall (World : Type u) (M : Model World Atom Agent) (x : World),
          M.Satisfies x psi <-> InitiallySatisfies M x phi) := by
  constructor
  · intro phi
    exact ⟨PALFormula.toFormula phi,
      fun _ M x => initiallySatisfies_toFormula M x phi⟩
  · intro psi
    exact ⟨Formula.toPAL psi,
      fun _ M x => (initiallySatisfies_toPAL M x psi).symm⟩

end PAL

namespace BPAL

/-- A same-world model whose accessibility relation is the current BPAL
relation and whose valuation is inherited from the ambient model. -/
def relationModel {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) (R : Agent -> World -> World -> Prop) :
    Model World Atom Agent where
  rel := R
  val := M.val

@[simp] theorem relationModel_rel {World : Type u} {Atom : Type v}
    {Agent : Type w} (M : Model World Atom Agent)
    (R : Agent -> World -> World -> Prop) (i : Agent) (x y : World) :
    (relationModel M R).rel i x y <-> R i x y := Iff.rfl

@[simp] theorem relationModel_val {World : Type u} {Atom : Type v}
    {Agent : Type w} (M : Model World Atom Agent)
    (R : Agent -> World -> World -> Prop) (p : Atom) (x : World) :
    (relationModel M R).val p x <-> M.val p x := Iff.rfl

/-- Installing the original accessibility relation recovers the ambient model. -/
theorem relationModel_rel_self {World : Type u} {Atom : Type v}
    {Agent : Type w} (M : Model World Atom Agent) :
    relationModel M M.rel = M := by
  apply Model.ext'
  · intro i x y
    rfl
  · intro p x
    rfl

/-- Correctness of BPAL announcement elimination, relative to an arbitrary
current accessibility relation. -/
theorem satisfies_toFormula {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) :
    forall (R : Agent -> World -> World -> Prop) (x : World)
      (phi : BPALFormula Atom Agent),
      Satisfies M R x phi <->
        (relationModel M R).Satisfies x (BPALFormula.toFormula phi) := by
  intro R x phi
  induction phi generalizing R x with
  | atom p => rfl
  | neg phi ih =>
      simp only [satisfies_neg, BPALFormula.toFormula, Model.satisfies_neg]
      exact not_congr (ih R x)
  | conj phi psi ihPhi ihPsi =>
      simp only [satisfies_conj, BPALFormula.toFormula, Model.satisfies_and]
      exact and_congr (ihPhi R x) (ihPsi R x)
  | box i phi ih =>
      simp only [satisfies_box, BPALFormula.toFormula, Model.satisfies_box,
        relationModel_rel]
      constructor
      · intro h y hy
        exact (ih R y).mp (h y hy)
      · intro h y hxy
        exact (ih R y).mpr (h y hxy)
  | announce phi psi ihPhi ihPsi =>
      simp only [satisfies_announce, BPALFormula.toFormula]
      let nextRel : Agent -> World -> World -> Prop :=
        fun i y z => R i y z /\ Satisfies M R z phi
      have hUpdate :
          relationModel M nextRel =
            (relationModel M R).update (BPALFormula.toFormula phi) := by
        apply Model.ext'
        · intro i y z
          change (R i y z /\ Satisfies M R z phi) <->
            (R i y z /\
              (relationModel M R).Satisfies z (BPALFormula.toFormula phi))
          rw [ihPhi R z]
        · intro p y
          rfl
      constructor
      · intro hPsi
        have hPsiDomain :
            (relationModel M nextRel).Satisfies x
              (BPALFormula.toFormula psi) :=
          (ihPsi nextRel x).mp hPsi
        have hPsiUpdated :
            ((relationModel M R).update (BPALFormula.toFormula phi)).Satisfies
              x (BPALFormula.toFormula psi) := by
          rw [← hUpdate]
          exact hPsiDomain
        exact (Model.satisfies_announcementReduce
          (relationModel M R) x (BPALFormula.toFormula phi)
            (BPALFormula.toFormula psi)).mp hPsiUpdated
      · intro hBasic
        have hPsiUpdated :
            ((relationModel M R).update (BPALFormula.toFormula phi)).Satisfies
              x (BPALFormula.toFormula psi) :=
          (Model.satisfies_announcementReduce
            (relationModel M R) x (BPALFormula.toFormula phi)
              (BPALFormula.toFormula psi)).mpr hBasic
        have hPsiDomain :
            (relationModel M nextRel).Satisfies x
              (BPALFormula.toFormula psi) := by
          rw [hUpdate]
          exact hPsiUpdated
        exact (ihPsi nextRel x).mpr hPsiDomain

/-- Announcement elimination is correct for the initial BPAL relation. -/
theorem initiallySatisfies_toFormula {World : Type u} {Atom : Type v}
    {Agent : Type w} (M : Model World Atom Agent) (x : World)
    (phi : BPALFormula Atom Agent) :
    InitiallySatisfies M x phi <->
      M.Satisfies x (BPALFormula.toFormula phi) := by
  rw [InitiallySatisfies, satisfies_toFormula, relationModel_rel_self]

/-- The basic-to-BPAL embedding preserves truth at every current relation. -/
theorem satisfies_toBPAL {World : Type u} {Atom : Type v} {Agent : Type w}
    (M : Model World Atom Agent) (R : Agent -> World -> World -> Prop)
    (x : World) (phi : Formula Atom Agent) :
    Satisfies M R x (Formula.toBPAL phi) <->
      (relationModel M R).Satisfies x phi := by
  simpa using satisfies_toFormula M R x (Formula.toBPAL phi)

/-- The basic-to-BPAL embedding preserves truth in the initial model. -/
theorem initiallySatisfies_toBPAL {World : Type u} {Atom : Type v}
    {Agent : Type w} (M : Model World Atom Agent) (x : World)
    (phi : Formula Atom Agent) :
    InitiallySatisfies M x (Formula.toBPAL phi) <-> M.Satisfies x phi := by
  simpa using initiallySatisfies_toFormula M x (Formula.toBPAL phi)

/-- The recursive BPAL semantics of announcing two embedded basic formulas is
exactly the direct arrow-restriction operation iterated by `Sigma`. -/
theorem initiallySatisfies_announce_basic {World : Type u} {Atom : Type v}
    {Agent : Type w} (M : Model World Atom Agent) (x : World)
    (announcement phi : Formula Atom Agent) :
    InitiallySatisfies M x
        (.announce (Formula.toBPAL announcement) (Formula.toBPAL phi)) <->
      (M.update announcement).Satisfies x phi := by
  rw [initiallySatisfies_toFormula]
  simp only [BPALFormula.toFormula, BPALFormula.toFormula_toBPAL]
  exact (M.satisfies_announcementReduce x announcement phi).symm

/-- BPAL and the basic modal language have equal expressive power on pointed
Kripke models (at any fixed universe level of worlds). -/
theorem equiexpressive_with_basic (Atom : Type v) (Agent : Type w) :
    (forall phi : BPALFormula Atom Agent,
      exists psi : Formula Atom Agent,
        forall (World : Type u) (M : Model World Atom Agent) (x : World),
          InitiallySatisfies M x phi <-> M.Satisfies x psi) /\
    (forall psi : Formula Atom Agent,
      exists phi : BPALFormula Atom Agent,
        forall (World : Type u) (M : Model World Atom Agent) (x : World),
          M.Satisfies x psi <-> InitiallySatisfies M x phi) := by
  constructor
  · intro phi
    exact ⟨BPALFormula.toFormula phi,
      fun _ M x => initiallySatisfies_toFormula M x phi⟩
  · intro psi
    exact ⟨Formula.toBPAL psi,
      fun _ M x => (initiallySatisfies_toBPAL M x psi).symm⟩

end BPAL

end ClassificationSigmaValidity
