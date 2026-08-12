import ClassificationSigmaValidity.FrameClass
import ClassificationSigmaValidity.Reduction
import ClassificationSigmaValidity.TypeFormulas
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Pi

/-!
# Finite-model property for K45, KD45, and S5

This file proves the finite-model step used in the paper.  We filter a model
through the subformulas of one target formula.  The filtered accessibility
relation records both the usual box obligation and equality of the source and
target box profiles.  The latter is valid on transitive Euclidean frames and
makes the filtered relation itself transitive and Euclidean.  Seriality and
reflexivity are inherited from the original model.

The final section applies the reduction theorem for iterated believed
announcements.  A failure of a finite truth pattern is witnessed by finitely
many ordinary modal formulas, so filtration turns any such failure into one on
a finite frame of the same class.
-/

namespace ClassificationSigmaValidity

universe u v w

namespace Formula

variable {Atom : Type v} {Agent : Type w}

noncomputable section

local instance : DecidableEq Atom := Classical.decEq Atom
local instance : DecidableEq Agent := Classical.decEq Agent

/-- The finite set consisting of a formula and all of its subformulas. -/
def subformulas : Formula Atom Agent -> Finset (Formula Atom Agent)
  | .atom p => { .atom p }
  | .neg phi => insert (.neg phi) phi.subformulas
  | .conj phi psi => insert (.conj phi psi) (phi.subformulas ∪ psi.subformulas)
  | .box i phi => insert (.box i phi) phi.subformulas

@[simp] theorem mem_subformulas_self (phi : Formula Atom Agent) :
    phi ∈ phi.subformulas := by
  cases phi <;> simp [subformulas]

/-- Subformula sets are transitively closed. -/
theorem subformulas_subset_of_mem {phi psi : Formula Atom Agent}
    (h : psi ∈ phi.subformulas) :
    psi.subformulas ⊆ phi.subformulas := by
  induction phi with
  | atom p =>
      simp only [subformulas, Finset.mem_singleton] at h
      subst psi
      exact Finset.Subset.rfl
  | neg phi ih =>
      simp only [subformulas, Finset.mem_insert] at h ⊢
      rcases h with rfl | h
      · exact Finset.Subset.rfl
      · intro chi hchi
        exact Finset.mem_insert.mpr (Or.inr (ih h hchi))
  | conj phi theta ihPhi ihTheta =>
      simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h ⊢
      rcases h with rfl | h | h
      · exact Finset.Subset.rfl
      · intro chi hchi
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_union.mpr (Or.inl (ihPhi h hchi))))
      · intro chi hchi
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_union.mpr (Or.inr (ihTheta h hchi))))
  | box i phi ih =>
      simp only [subformulas, Finset.mem_insert] at h ⊢
      rcases h with rfl | h
      · exact Finset.Subset.rfl
      · intro chi hchi
        exact Finset.mem_insert.mpr (Or.inr (ih h hchi))

theorem mem_subformulas_of_mem {phi psi chi : Formula Atom Agent}
    (hpsi : psi ∈ phi.subformulas) (hchi : chi ∈ psi.subformulas) :
    chi ∈ phi.subformulas :=
  subformulas_subset_of_mem hpsi hchi

end

end Formula

namespace Filtration

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- Worlds are equivalent when they agree on all subformulas of the target. -/
def setoid (M : Model World Atom Agent) (target : Formula Atom Agent) :
    Setoid World where
  r x y := ∀ psi, psi ∈ target.subformulas ->
    (M.Satisfies x psi ↔ M.Satisfies y psi)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x psi hpsi
      exact Iff.rfl
    · intro x y hxy psi hpsi
      exact (hxy psi hpsi).symm
    · intro x y z hxy hyz psi hpsi
      exact (hxy psi hpsi).trans (hyz psi hpsi)

/-- The filtered world type.  Keeping it as a quotient of the original world
type means it remains in the same universe. -/
abbrev FilteredWorld (M : Model World Atom Agent)
    (target : Formula Atom Agent) :=
  Quotient (setoid M target)

/-- The finite Boolean truth code used to bound the number of equivalence
classes. -/
noncomputable def code (M : Model World Atom Agent)
    (target : Formula Atom Agent) (x : World) :
    ({psi // psi ∈ target.subformulas} -> Bool) := by
  classical
  exact fun psi => if M.Satisfies x psi.1 then true else false

theorem code_eq_iff (M : Model World Atom Agent)
    (target : Formula Atom Agent) (x y : World) :
    code M target x = code M target y ↔
      (setoid M target).r x y := by
  classical
  constructor
  · intro h psi hpsi
    have hcoord := congrFun h ⟨psi, hpsi⟩
    simp only [code] at hcoord
    by_cases hx : M.Satisfies x psi <;>
      by_cases hy : M.Satisfies y psi <;> simp [hx, hy] at hcoord ⊢
  · intro h
    funext psi
    simp only [code]
    exact if_congr (h psi.1 psi.2) rfl rfl

/-- The truth code descends to the quotient. -/
noncomputable def quotientCode (M : Model World Atom Agent)
    (target : Formula Atom Agent) :
    FilteredWorld M target ->
      ({psi // psi ∈ target.subformulas} -> Bool) :=
  Quotient.lift (code M target) fun x y h =>
    (code_eq_iff M target x y).2 h

theorem quotientCode_injective (M : Model World Atom Agent)
    (target : Formula Atom Agent) :
    Function.Injective (quotientCode M target) := by
  intro a b h
  induction a using Quotient.inductionOn with
  | _ x =>
      induction b using Quotient.inductionOn with
      | _ y =>
          apply Quotient.sound
          change code M target x = code M target y at h
          exact (code_eq_iff M target x y).1 h

/-- A filtration through finitely many subformulas has finitely many worlds. -/
noncomputable instance instFiniteWorld (M : Model World Atom Agent)
    (target : Formula Atom Agent) : Finite (FilteredWorld M target) :=
  Finite.of_injective (quotientCode M target)
    (quotientCode_injective M target)

/-- The representative chosen by `Quotient.out` agrees with the world used to
form a quotient class on every formula in the filtration set. -/
theorem out_mk_satisfies_iff (M : Model World Atom Agent)
    (target : Formula Atom Agent) (x : World)
    (psi : Formula Atom Agent) (hpsi : psi ∈ target.subformulas) :
    M.Satisfies (Quotient.out (Quotient.mk (setoid M target) x)) psi <->
      M.Satisfies x psi := by
  have hout : (setoid M target).r
      (Quotient.out (Quotient.mk (setoid M target) x)) x :=
    Quotient.eq_iff_equiv.mp (Quotient.out_eq _)
  exact hout psi hpsi

/-- The transitive-Euclidean filtration relation.  Its first component says
that related worlds have the same `i`-box profile.  Its second component is the
standard filtration obligation for boxes. -/
def Related (M : Model World Atom Agent) (target : Formula Atom Agent)
    (i : Agent) (a b : FilteredWorld M target) : Prop :=
  (∀ psi, Formula.box i psi ∈ target.subformulas ->
      (M.Satisfies a.out (.box i psi) <->
        M.Satisfies b.out (.box i psi))) ∧
    (∀ psi, Formula.box i psi ∈ target.subformulas ->
      M.Satisfies a.out (.box i psi) -> M.Satisfies b.out psi)

/-- The filtration of `M` through the subformulas of `target`. -/
noncomputable def model (M : Model World Atom Agent)
    (target : Formula Atom Agent) :
    Model (FilteredWorld M target) Atom Agent where
  rel := Related M target
  val p a := M.val p a.out

@[simp] theorem model_rel (M : Model World Atom Agent)
    (target : Formula Atom Agent) (i : Agent)
    (a b : FilteredWorld M target) :
    (model M target).rel i a b <-> Related M target i a b := Iff.rfl

@[simp] theorem model_val (M : Model World Atom Agent)
    (target : Formula Atom Agent) (p : Atom)
    (a : FilteredWorld M target) :
    (model M target).val p a <-> M.val p a.out := Iff.rfl

/-- Every original arrow from the chosen representative induces an arrow to
the quotient class of its target. -/
theorem related_mk_of_rel {M : Model World Atom Agent} (hM : IsK45 M)
    (target : Formula Atom Agent) (i : Agent)
    (a : FilteredWorld M target) (y : World) (hay : M.rel i a.out y) :
    Related M target i a (Quotient.mk (setoid M target) y) := by
  constructor
  · intro psi hbox
    have houtBox := out_mk_satisfies_iff M target y (.box i psi) hbox
    exact (M.modalAgreement_box hM hay psi).trans houtBox.symm
  · intro psi hbox haBox
    have hpsi : psi ∈ target.subformulas :=
      Formula.mem_subformulas_of_mem hbox (by
        simp [Formula.subformulas])
    have hy : M.Satisfies y psi := haBox y hay
    exact (out_mk_satisfies_iff M target y psi hpsi).mpr hy

/-- Truth lemma for the transitive-Euclidean filtration. -/
theorem model_satisfies_iff {M : Model World Atom Agent} (hM : IsK45 M)
    (target : Formula Atom Agent) (a : FilteredWorld M target)
    (psi : Formula Atom Agent) (hpsi : psi ∈ target.subformulas) :
    (model M target).Satisfies a psi <-> M.Satisfies a.out psi := by
  induction psi generalizing a with
  | atom p => rfl
  | neg psi ih =>
      have hsub : psi ∈ target.subformulas :=
        Formula.mem_subformulas_of_mem hpsi (by
          simp [Formula.subformulas])
      exact not_congr (ih a hsub)
  | conj psi chi ihPsi ihChi =>
      have hsubPsi : psi ∈ target.subformulas :=
        Formula.mem_subformulas_of_mem hpsi (by
          simp [Formula.subformulas])
      have hsubChi : chi ∈ target.subformulas :=
        Formula.mem_subformulas_of_mem hpsi (by
          simp [Formula.subformulas])
      exact and_congr (ihPsi a hsubPsi) (ihChi a hsubChi)
  | box i psi ih =>
      have hsub : psi ∈ target.subformulas :=
        Formula.mem_subformulas_of_mem hpsi (by
          simp [Formula.subformulas])
      simp only [Model.satisfies_box]
      constructor
      · intro h y hay
        let b : FilteredWorld M target :=
          Quotient.mk (setoid M target) y
        have hab : (model M target).rel i a b :=
          related_mk_of_rel hM target i a y hay
        have hb : (model M target).Satisfies b psi := h b hab
        have hbOut : M.Satisfies b.out psi := (ih b hsub).mp hb
        exact (out_mk_satisfies_iff M target y psi hsub).mp hbOut
      · intro h b hab
        apply (ih b hsub).mpr
        exact hab.2 psi hpsi h

/-- The target formula itself is preserved at the quotient class of every
original world. -/
theorem model_satisfies_mk_iff {M : Model World Atom Agent} (hM : IsK45 M)
    (target : Formula Atom Agent) (x : World) :
    (model M target).Satisfies (Quotient.mk (setoid M target) x) target <->
      M.Satisfies x target := by
  rw [model_satisfies_iff hM target _ target
    (Formula.mem_subformulas_self target)]
  exact out_mk_satisfies_iff M target x target
    (Formula.mem_subformulas_self target)

/-- The filtration relation is transitive independently of the original
frame; box-profile equality supplies the middle step. -/
theorem model_transitive (M : Model World Atom Agent)
    (target : Formula Atom Agent) (i : Agent) :
    Frame.Transitive ((model M target).rel i) := by
  intro a b c hab hbc
  constructor
  · intro psi hbox
    exact (hab.1 psi hbox).trans (hbc.1 psi hbox)
  · intro psi hbox ha
    exact hbc.2 psi hbox ((hab.1 psi hbox).mp ha)

/-- The filtration relation is Euclidean independently of the original
frame. -/
theorem model_euclidean (M : Model World Atom Agent)
    (target : Formula Atom Agent) (i : Agent) :
    Frame.Euclidean ((model M target).rel i) := by
  intro a b c hab hac
  constructor
  · intro psi hbox
    exact (hab.1 psi hbox).symm.trans (hac.1 psi hbox)
  · intro psi hbox hb
    exact hac.2 psi hbox ((hab.1 psi hbox).mpr hb)

/-- Filtration preserves K45. -/
theorem model_isK45 (M : Model World Atom Agent)
    (target : Formula Atom Agent) : IsK45 (model M target) := by
  intro i
  exact ⟨model_transitive M target i, model_euclidean M target i⟩

/-- Filtration preserves KD45. -/
theorem model_isKD45 {M : Model World Atom Agent} (hM : IsKD45 M)
    (target : Formula Atom Agent) : IsKD45 (model M target) := by
  intro i
  refine ⟨?_, model_transitive M target i, model_euclidean M target i⟩
  intro a
  obtain ⟨y, hay⟩ := (hM i).1 a.out
  exact ⟨Quotient.mk (setoid M target) y,
    related_mk_of_rel hM.isK45 target i a y hay⟩

/-- Filtration preserves S5. -/
theorem model_isS5 {M : Model World Atom Agent} (hM : IsS5 M)
    (target : Formula Atom Agent) : IsS5 (model M target) := by
  intro i
  refine ⟨?_, model_transitive M target i, model_euclidean M target i⟩
  intro a
  constructor
  · intro psi hbox
    exact Iff.rfl
  · intro psi _ ha
    exact ha a.out ((hM i).1 a.out)

/-- A K45 counterexample has a finite K45 filtration counterexample in the
same universe. -/
theorem exists_finite_countermodel_isK45
    (M : Model World Atom Agent) (hM : IsK45 M)
    (target : Formula Atom Agent) (x : World)
    (hx : ¬M.Satisfies x target) :
    ∃ (FiniteWorld : Type u) (_ : Finite FiniteWorld)
      (N : Model FiniteWorld Atom Agent),
      IsK45 N ∧ ∃ z, ¬N.Satisfies z target := by
  exact ⟨FilteredWorld M target, inferInstance, model M target,
    model_isK45 M target, Quotient.mk (setoid M target) x,
    fun h => hx ((model_satisfies_mk_iff hM target x).mp h)⟩

/-- A KD45 counterexample has a finite KD45 counterexample. -/
theorem exists_finite_countermodel_isKD45
    (M : Model World Atom Agent) (hM : IsKD45 M)
    (target : Formula Atom Agent) (x : World)
    (hx : ¬M.Satisfies x target) :
    ∃ (FiniteWorld : Type u) (_ : Finite FiniteWorld)
      (N : Model FiniteWorld Atom Agent),
      IsKD45 N ∧ ∃ z, ¬N.Satisfies z target := by
  exact ⟨FilteredWorld M target, inferInstance, model M target,
    model_isKD45 hM target, Quotient.mk (setoid M target) x,
    fun h => hx ((model_satisfies_mk_iff hM.isK45 target x).mp h)⟩

/-- An S5 counterexample has a finite S5 counterexample. -/
theorem exists_finite_countermodel_isS5
    (M : Model World Atom Agent) (hM : IsS5 M)
    (target : Formula Atom Agent) (x : World)
    (hx : ¬M.Satisfies x target) :
    ∃ (FiniteWorld : Type u) (_ : Finite FiniteWorld)
      (N : Model FiniteWorld Atom Agent),
      IsS5 N ∧ ∃ z, ¬N.Satisfies z target := by
  exact ⟨FilteredWorld M target, inferInstance, model M target,
    model_isS5 hM target, Quotient.mk (setoid M target) x,
    fun h => hx ((model_satisfies_mk_iff hM.isK45 target x).mp h)⟩

/-- A satisfiable modal formula on a K45 model has a finite K45 witness. -/
theorem exists_finite_model_satisfies_isK45
    (M : Model World Atom Agent) (hM : IsK45 M)
    (target : Formula Atom Agent) (x : World)
    (hx : M.Satisfies x target) :
    ∃ (FiniteWorld : Type u) (_ : Finite FiniteWorld)
      (N : Model FiniteWorld Atom Agent),
      IsK45 N ∧ ∃ z, N.Satisfies z target := by
  exact ⟨FilteredWorld M target, inferInstance, model M target,
    model_isK45 M target, Quotient.mk (setoid M target) x,
    (model_satisfies_mk_iff hM target x).mpr hx⟩

/-- A satisfiable modal formula on a KD45 model has a finite KD45 witness. -/
theorem exists_finite_model_satisfies_isKD45
    (M : Model World Atom Agent) (hM : IsKD45 M)
    (target : Formula Atom Agent) (x : World)
    (hx : M.Satisfies x target) :
    ∃ (FiniteWorld : Type u) (_ : Finite FiniteWorld)
      (N : Model FiniteWorld Atom Agent),
      IsKD45 N ∧ ∃ z, N.Satisfies z target := by
  exact ⟨FilteredWorld M target, inferInstance, model M target,
    model_isKD45 hM target, Quotient.mk (setoid M target) x,
    (model_satisfies_mk_iff hM.isK45 target x).mpr hx⟩

/-- A satisfiable modal formula on an S5 model has a finite S5 witness. -/
theorem exists_finite_model_satisfies_isS5
    (M : Model World Atom Agent) (hM : IsS5 M)
    (target : Formula Atom Agent) (x : World)
    (hx : M.Satisfies x target) :
    ∃ (FiniteWorld : Type u) (_ : Finite FiniteWorld)
      (N : Model FiniteWorld Atom Agent),
      IsS5 N ∧ ∃ z, N.Satisfies z target := by
  exact ⟨FilteredWorld M target, inferInstance, model M target,
    model_isS5 hM target, Quotient.mk (setoid M target) x,
    (model_satisfies_mk_iff hM.isK45 target x).mpr hx⟩

end Filtration

namespace Formula

variable {Atom : Type v} {Agent : Type w}

/-- The modal formula asserting that `psi` has Boolean truth value `b`. -/
def truthLiteral (b : Bool) (psi : Formula Atom Agent) : Formula Atom Agent :=
  if b then psi else .neg psi

/-- The reduction to the basic modal language of the assertion that the trace
of `phi` has value `b` at time `n`. -/
def traceLiteral (phi : Formula Atom Agent) (n : Nat) (b : Bool) :
    Formula Atom Agent :=
  truthLiteral b (iteratedAnnouncementReduce phi n phi)

/-- A basic modal formula witnessing failure of one prescribed finite-pattern
coordinate while retaining the prescribed initial truth value. -/
def traceCounterexample (phi : Formula Atom Agent)
    (firstBit badBit : Bool) (n : Nat) : Formula Atom Agent :=
  .conj (traceLiteral phi 0 firstBit) (.neg (traceLiteral phi n badBit))

end Formula

namespace Model

variable {World : Type u} {Atom : Type v} {Agent : Type w}

@[simp] theorem satisfies_truthLiteral (M : Model World Atom Agent) (x : World)
    (b : Bool) (psi : Formula Atom Agent) :
    M.Satisfies x (Formula.truthLiteral b psi) <->
      Pattern.HoldsBit b (M.Satisfies x psi) := by
  cases b <;> rfl

/-- Correctness of the basic modal encoding of a finite trace coordinate. -/
theorem satisfies_traceLiteral (M : Model World Atom Agent) (x : World)
    (phi : Formula Atom Agent) (n : Nat) (b : Bool) :
    M.Satisfies x (Formula.traceLiteral phi n b) <->
      Pattern.HoldsBit b (M.trace x phi n) := by
  rw [Formula.traceLiteral, satisfies_truthLiteral]
  cases b
  · exact not_congr
      (M.trace_iff_satisfies_iteratedAnnouncementReduce x phi n).symm
  · exact M.trace_iff_satisfies_iteratedAnnouncementReduce x phi n |>.symm

/-- Correctness of the modal formula encoding a counterexample to one finite
pattern coordinate. -/
theorem satisfies_traceCounterexample (M : Model World Atom Agent) (x : World)
    (phi : Formula Atom Agent) (firstBit badBit : Bool) (n : Nat) :
    M.Satisfies x (Formula.traceCounterexample phi firstBit badBit n) <->
      Pattern.HoldsBit firstBit (M.trace x phi 0) ∧
        ¬Pattern.HoldsBit badBit (M.trace x phi n) := by
  simp only [Formula.traceCounterexample, satisfies_and, satisfies_neg,
    satisfies_traceLiteral]

end Model

namespace FiniteModelProperty

variable {Atom : Type v} {Agent : Type w}

/-- Any failure of a finite pattern on a K45 model already occurs on a finite
K45 model.  The construction filters the modal reduction of the initial bit
and a failing trace coordinate. -/
theorem finite_pattern_counterexample_isK45
    {World : Type u} (M : Model World Atom Agent) (hM : IsK45 M)
    (x : World) (phi : Formula Atom Agent) (bits : List Bool)
    (hlen : 2 <= bits.length)
    (hfirst : Pattern.HoldsBit (Pattern.finite bits hlen).first
      (M.trace x phi 0))
    (hfail : ¬Sigma.Realizes M x phi (Pattern.finite bits hlen)) :
    ∃ (FiniteWorld : Type u) (_ : Finite FiniteWorld)
      (N : Model FiniteWorld Atom Agent),
      IsK45 N ∧ ∃ z,
        Pattern.HoldsBit (Pattern.finite bits hlen).first (N.trace z phi 0) ∧
          ¬Sigma.Realizes N z phi (Pattern.finite bits hlen) := by
  classical
  simp only [Sigma.Realizes, Pattern.RealizesTrace] at hfail
  push_neg at hfail
  obtain ⟨n, hn, hbad⟩ := hfail
  let target := Formula.traceCounterexample phi
    (Pattern.finite bits hlen).first bits[n] n
  have hxTarget : M.Satisfies x target :=
    (M.satisfies_traceCounterexample x phi
      (Pattern.finite bits hlen).first bits[n] n).mpr ⟨hfirst, hbad⟩
  obtain ⟨FiniteWorld, hFinite, N, hN, z, hz⟩ :=
    Filtration.exists_finite_model_satisfies_isK45
      M hM target x hxTarget
  letI : Finite FiniteWorld := hFinite
  have hzBits := (N.satisfies_traceCounterexample z phi
    (Pattern.finite bits hlen).first bits[n] n).mp hz
  refine ⟨FiniteWorld, inferInstance, N, hN, z, hzBits.1, ?_⟩
  intro hreal
  exact hzBits.2 (hreal n hn)

/-- Any finite-pattern failure on a KD45 model has a finite KD45 witness. -/
theorem finite_pattern_counterexample_isKD45
    {World : Type u} (M : Model World Atom Agent) (hM : IsKD45 M)
    (x : World) (phi : Formula Atom Agent) (bits : List Bool)
    (hlen : 2 <= bits.length)
    (hfirst : Pattern.HoldsBit (Pattern.finite bits hlen).first
      (M.trace x phi 0))
    (hfail : ¬Sigma.Realizes M x phi (Pattern.finite bits hlen)) :
    ∃ (FiniteWorld : Type u) (_ : Finite FiniteWorld)
      (N : Model FiniteWorld Atom Agent),
      IsKD45 N ∧ ∃ z,
        Pattern.HoldsBit (Pattern.finite bits hlen).first (N.trace z phi 0) ∧
          ¬Sigma.Realizes N z phi (Pattern.finite bits hlen) := by
  classical
  simp only [Sigma.Realizes, Pattern.RealizesTrace] at hfail
  push_neg at hfail
  obtain ⟨n, hn, hbad⟩ := hfail
  let target := Formula.traceCounterexample phi
    (Pattern.finite bits hlen).first bits[n] n
  have hxTarget : M.Satisfies x target :=
    (M.satisfies_traceCounterexample x phi
      (Pattern.finite bits hlen).first bits[n] n).mpr ⟨hfirst, hbad⟩
  obtain ⟨FiniteWorld, hFinite, N, hN, z, hz⟩ :=
    Filtration.exists_finite_model_satisfies_isKD45
      M hM target x hxTarget
  letI : Finite FiniteWorld := hFinite
  have hzBits := (N.satisfies_traceCounterexample z phi
    (Pattern.finite bits hlen).first bits[n] n).mp hz
  refine ⟨FiniteWorld, inferInstance, N, hN, z, hzBits.1, ?_⟩
  intro hreal
  exact hzBits.2 (hreal n hn)

/-- Any finite-pattern failure on an S5 model has a finite S5 witness. -/
theorem finite_pattern_counterexample_isS5
    {World : Type u} (M : Model World Atom Agent) (hM : IsS5 M)
    (x : World) (phi : Formula Atom Agent) (bits : List Bool)
    (hlen : 2 <= bits.length)
    (hfirst : Pattern.HoldsBit (Pattern.finite bits hlen).first
      (M.trace x phi 0))
    (hfail : ¬Sigma.Realizes M x phi (Pattern.finite bits hlen)) :
    ∃ (FiniteWorld : Type u) (_ : Finite FiniteWorld)
      (N : Model FiniteWorld Atom Agent),
      IsS5 N ∧ ∃ z,
        Pattern.HoldsBit (Pattern.finite bits hlen).first (N.trace z phi 0) ∧
          ¬Sigma.Realizes N z phi (Pattern.finite bits hlen) := by
  classical
  simp only [Sigma.Realizes, Pattern.RealizesTrace] at hfail
  push_neg at hfail
  obtain ⟨n, hn, hbad⟩ := hfail
  let target := Formula.traceCounterexample phi
    (Pattern.finite bits hlen).first bits[n] n
  have hxTarget : M.Satisfies x target :=
    (M.satisfies_traceCounterexample x phi
      (Pattern.finite bits hlen).first bits[n] n).mpr ⟨hfirst, hbad⟩
  obtain ⟨FiniteWorld, hFinite, N, hN, z, hz⟩ :=
    Filtration.exists_finite_model_satisfies_isS5
      M hM target x hxTarget
  letI : Finite FiniteWorld := hFinite
  have hzBits := (N.satisfies_traceCounterexample z phi
    (Pattern.finite bits hlen).first bits[n] n).mp hz
  refine ⟨FiniteWorld, inferInstance, N, hN, z, hzBits.1, ?_⟩
  intro hreal
  exact hzBits.2 (hreal n hn)

/-- Nonvalidity of a finite-pattern implication over K45 is witnessed by a
finite K45 model. -/
theorem exists_finite_counterexample_of_not_valid_isK45
    (phi : Formula Atom Agent) (bits : List Bool) (hlen : 2 <= bits.length)
    (h : ¬Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      phi (Pattern.finite bits hlen)) :
    ∃ (FiniteWorld : Type u) (_ : Finite FiniteWorld)
      (N : Model FiniteWorld Atom Agent),
      IsK45 N ∧ ∃ z,
        Pattern.HoldsBit (Pattern.finite bits hlen).first (N.trace z phi 0) ∧
          ¬Sigma.Realizes N z phi (Pattern.finite bits hlen) := by
  classical
  simp only [Sigma.Valid, Classes.K45] at h
  push_neg at h
  obtain ⟨World, M, hM, x, hfirst, hfail⟩ := h
  exact finite_pattern_counterexample_isK45
    M hM x phi bits hlen hfirst hfail

/-- Nonvalidity of a finite-pattern implication over KD45 is witnessed by a
finite KD45 model. -/
theorem exists_finite_counterexample_of_not_valid_isKD45
    (phi : Formula Atom Agent) (bits : List Bool) (hlen : 2 <= bits.length)
    (h : ¬Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      phi (Pattern.finite bits hlen)) :
    ∃ (FiniteWorld : Type u) (_ : Finite FiniteWorld)
      (N : Model FiniteWorld Atom Agent),
      IsKD45 N ∧ ∃ z,
        Pattern.HoldsBit (Pattern.finite bits hlen).first (N.trace z phi 0) ∧
          ¬Sigma.Realizes N z phi (Pattern.finite bits hlen) := by
  classical
  simp only [Sigma.Valid, Classes.KD45] at h
  push_neg at h
  obtain ⟨World, M, hM, x, hfirst, hfail⟩ := h
  exact finite_pattern_counterexample_isKD45
    M hM x phi bits hlen hfirst hfail

/-- Nonvalidity of a finite-pattern implication over S5 is witnessed by a
finite S5 model. -/
theorem exists_finite_counterexample_of_not_valid_isS5
    (phi : Formula Atom Agent) (bits : List Bool) (hlen : 2 <= bits.length)
    (h : ¬Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      phi (Pattern.finite bits hlen)) :
    ∃ (FiniteWorld : Type u) (_ : Finite FiniteWorld)
      (N : Model FiniteWorld Atom Agent),
      IsS5 N ∧ ∃ z,
        Pattern.HoldsBit (Pattern.finite bits hlen).first (N.trace z phi 0) ∧
          ¬Sigma.Realizes N z phi (Pattern.finite bits hlen) := by
  classical
  simp only [Sigma.Valid, Classes.S5] at h
  push_neg at h
  obtain ⟨World, M, hM, x, hfirst, hfail⟩ := h
  exact finite_pattern_counterexample_isS5
    M hM x phi bits hlen hfirst hfail

end FiniteModelProperty

end ClassificationSigmaValidity
