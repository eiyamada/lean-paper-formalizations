import ClassificationSigmaValidity.Semantics

/-!
# Finite type formulas

The existence constructions in the paper assign a fresh proposition letter to
each member of a finite set of state types.  This file packages the two formula
constructions shared by those arguments:

* `TypeFormulas.exactType atomOf typeUniverse t` is the formula `chi_t`: the atom
  assigned to `t` is true and every atom assigned to another member of the
  finite type universe is false;
* `TypeFormulas.successorTypes agent atomOf typeUniverse types` is the formula
  `E_types`: all successors have one of the listed exact types and every listed
  exact type occurs at a successor.

The definitions use lists so that the later parametrized witness families can
build their formulas directly by recursion on a natural number.  None of the
semantic statements below requires the lists to be duplicate-free.
-/

namespace ClassificationSigmaValidity

universe u v w z

namespace Formula

variable {Atom : Type v} {Agent : Type w}

/-- Finite conjunction.  Its empty value is truth. -/
def conjList [Inhabited Atom] : List (Formula Atom Agent) -> Formula Atom Agent
  | [] => verum
  | phi :: formulas => .conj phi (conjList formulas)

/-- Finite disjunction.  Its empty value is falsity. -/
def disjList [Inhabited Atom] : List (Formula Atom Agent) -> Formula Atom Agent
  | [] => falsum
  | phi :: formulas => Formula.or phi (disjList formulas)

end Formula

namespace Model

variable {World : Type u} {Atom : Type v} {Agent : Type w}

@[simp] theorem satisfies_conjList [Inhabited Atom]
    (M : Model World Atom Agent) (x : World)
    (formulas : List (Formula Atom Agent)) :
    M.Satisfies x (Formula.conjList formulas) <->
      forall phi, phi ∈ formulas -> M.Satisfies x phi := by
  induction formulas with
  | nil => simp [Formula.conjList]
  | cons phi formulas ih => simp [Formula.conjList, ih]

@[simp] theorem satisfies_disjList [Inhabited Atom]
    (M : Model World Atom Agent) (x : World)
    (formulas : List (Formula Atom Agent)) :
    M.Satisfies x (Formula.disjList formulas) <->
      exists phi, phi ∈ formulas /\ M.Satisfies x phi := by
  induction formulas with
  | nil => simp [Formula.disjList]
  | cons phi formulas ih => simp [Formula.disjList, ih]

end Model

namespace TypeFormulas

variable {World : Type u} {Atom : Type v} {Agent : Type w} {Tag : Type z}

/-- The formulas asserting that the atoms of the listed types other than `t`
are false. -/
def exclusions [Inhabited Atom] [DecidableEq Tag]
    (atomOf : Tag -> Atom) (typeUniverse : List Tag) (t : Tag) :
    Formula Atom Agent :=
  match typeUniverse with
  | [] => .verum
  | s :: rest =>
      if s = t then exclusions atomOf rest t
      else .conj (.neg (.atom (atomOf s))) (exclusions atomOf rest t)

/-- `chi_t`: exactly the proposition letter assigned to `t` is true among the
letters assigned to members of `typeUniverse`. -/
def exactType [Inhabited Atom] [DecidableEq Tag]
    (atomOf : Tag -> Atom) (typeUniverse : List Tag) (t : Tag) :
    Formula Atom Agent :=
  .conj (.atom (atomOf t)) (exclusions atomOf typeUniverse t)

/-- The list of exact-type formulas indexed by `types`. -/
def exactTypes [Inhabited Atom] [DecidableEq Tag]
    (atomOf : Tag -> Atom) (typeUniverse types : List Tag) :
    List (Formula Atom Agent) :=
  types.map (exactType atomOf typeUniverse)

/-- The box half of `E_X`: every successor has an exact type listed in `types`. -/
def allSuccessorsIn [Inhabited Atom] [DecidableEq Tag]
    (agent : Agent) (atomOf : Tag -> Atom) (typeUniverse types : List Tag) :
    Formula Atom Agent :=
  .box agent (Formula.disjList (exactTypes atomOf typeUniverse types))

/-- The diamond half of `E_X`: every exact type listed in `types` is realized
by a successor. -/
def everyTypeOccurs [Inhabited Atom] [DecidableEq Tag]
    (agent : Agent) (atomOf : Tag -> Atom) (typeUniverse types : List Tag) :
    Formula Atom Agent :=
  Formula.conjList
    ((exactTypes atomOf typeUniverse types).map (Formula.dia agent))

/-- `E_X`: the successor exact types are precisely the members of `types`. -/
def successorTypes [Inhabited Atom] [DecidableEq Tag]
    (agent : Agent) (atomOf : Tag -> Atom) (typeUniverse types : List Tag) :
    Formula Atom Agent :=
  .conj (allSuccessorsIn agent atomOf typeUniverse types)
    (everyTypeOccurs agent atomOf typeUniverse types)

@[simp] theorem satisfies_exclusions [Inhabited Atom] [DecidableEq Tag]
    (M : Model World Atom Agent) (x : World) (atomOf : Tag -> Atom)
    (typeUniverse : List Tag) (t : Tag) :
    M.Satisfies x (exclusions (Agent := Agent) atomOf typeUniverse t) <->
      forall s, s ∈ typeUniverse -> s != t -> Not (M.val (atomOf s) x) := by
  induction typeUniverse with
  | nil => simp [exclusions]
  | cons s rest ih =>
      by_cases hst : s = t
      · subst s
        simp [exclusions, ih]
      · simp [exclusions, hst, ih]

@[simp] theorem satisfies_exactType [Inhabited Atom] [DecidableEq Tag]
    (M : Model World Atom Agent) (x : World) (atomOf : Tag -> Atom)
    (typeUniverse : List Tag) (t : Tag) :
    M.Satisfies x (exactType (Agent := Agent) atomOf typeUniverse t) <->
      M.val (atomOf t) x /\
        forall s, s ∈ typeUniverse -> s != t -> Not (M.val (atomOf s) x) := by
  simp [exactType]

/-- Distinct members of the finite universe have mutually exclusive exact-type
formulas. -/
theorem exactType_mutuallyExclusive [Inhabited Atom] [DecidableEq Tag]
    (M : Model World Atom Agent) (x : World) (atomOf : Tag -> Atom)
    (typeUniverse : List Tag) {s t : Tag} (hs : s ∈ typeUniverse) (hst : s != t) :
    Not (M.Satisfies x (exactType (Agent := Agent) atomOf typeUniverse s) /\
      M.Satisfies x (exactType (Agent := Agent) atomOf typeUniverse t)) := by
  rintro ⟨hsat, htsat⟩
  have hpositive : M.val (atomOf s) x :=
    (satisfies_exactType M x atomOf typeUniverse s).mp hsat |>.1
  have hnegative : Not (M.val (atomOf s) x) :=
    (satisfies_exactType M x atomOf typeUniverse t).mp htsat |>.2 s hs hst
  exact hnegative hpositive

@[simp] theorem satisfies_exactTypes_member [Inhabited Atom] [DecidableEq Tag]
    (M : Model World Atom Agent) (x : World) (atomOf : Tag -> Atom)
    (typeUniverse types : List Tag) :
    (exists phi, phi ∈ exactTypes (Agent := Agent) atomOf typeUniverse types /\
      M.Satisfies x phi) <->
      exists t, t ∈ types /\
        M.Satisfies x (exactType (Agent := Agent) atomOf typeUniverse t) := by
  simp [exactTypes]

/-- Semantic characterization of the box half of `E_X`. -/
@[simp] theorem satisfies_allSuccessorsIn [Inhabited Atom] [DecidableEq Tag]
    (M : Model World Atom Agent) (x : World) (agent : Agent)
    (atomOf : Tag -> Atom) (typeUniverse types : List Tag) :
    M.Satisfies x (allSuccessorsIn agent atomOf typeUniverse types) <->
      forall y, M.rel agent x y ->
        exists t, t ∈ types /\
          M.Satisfies y (exactType (Agent := Agent) atomOf typeUniverse t) := by
  simp [allSuccessorsIn, exactTypes]

/-- Semantic characterization of the diamond half of `E_X`. -/
@[simp] theorem satisfies_everyTypeOccurs [Inhabited Atom] [DecidableEq Tag]
    (M : Model World Atom Agent) (x : World) (agent : Agent)
    (atomOf : Tag -> Atom) (typeUniverse types : List Tag) :
    M.Satisfies x (everyTypeOccurs agent atomOf typeUniverse types) <->
      forall t, t ∈ types ->
        exists y, M.rel agent x y /\
          M.Satisfies y (exactType (Agent := Agent) atomOf typeUniverse t) := by
  simp [everyTypeOccurs, exactTypes]

/-- Semantic characterization of `E_X`. -/
@[simp] theorem satisfies_successorTypes [Inhabited Atom] [DecidableEq Tag]
    (M : Model World Atom Agent) (x : World) (agent : Agent)
    (atomOf : Tag -> Atom) (typeUniverse types : List Tag) :
    M.Satisfies x (successorTypes agent atomOf typeUniverse types) <->
      (forall y, M.rel agent x y ->
        exists t, t ∈ types /\
          M.Satisfies y (exactType (Agent := Agent) atomOf typeUniverse t)) /\
      (forall t, t ∈ types ->
        exists y, M.rel agent x y /\
          M.Satisfies y (exactType (Agent := Agent) atomOf typeUniverse t)) := by
  simp [successorTypes]

end TypeFormulas

end ClassificationSigmaValidity
