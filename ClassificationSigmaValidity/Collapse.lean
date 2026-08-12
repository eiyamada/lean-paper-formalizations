import ClassificationSigmaValidity.FrameClass

/-!
# Collapse lemmas for iterated announcements

This module contains the update-algebraic parts of the paper's collapse
lemmas.  The single-agent KD45 `00` case is developed separately because it
uses generated-submodel locality rather than global closure under updates.
-/

namespace ClassificationSigmaValidity

universe u v w

namespace Model

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- An update cannot change a model which has no arrows. -/
theorem update_eq_self_of_rel_empty (M : Model World Atom Agent)
    (phi : Formula Atom Agent) (h : forall i x y, Not (M.rel i x y)) :
    M.update phi = M := by
  apply Model.ext'
  · intro i x y
    constructor
    · exact fun hxy => hxy.1
    · intro hxy
      exact (h i x y hxy).elim
  · intro p x
    rfl

/-- Self-refutation makes every accessibility relation empty after the second
announcement. -/
theorem iterateUpdate_two_rel_empty_of_selfRefuting
    (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (h : forall x, M.Satisfies x phi ->
      Not ((M.update phi).Satisfies x phi)) :
    forall i x y, Not ((M.iterateUpdate phi 2).rel i x y) := by
  intro i x y hxy
  have hs := (M.iterateUpdate_rel_iff phi 2 i x y).mp hxy |>.2
  have h0 : M.Satisfies y phi := hs 0 (by omega)
  have h1 : (M.update phi).Satisfies y phi := by
    simpa [Model.iterateUpdate] using hs 1 (by omega)
  exact h y h0 h1

theorem iterateUpdate_stable_from_two_of_selfRefuting
    (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (h : forall x, M.Satisfies x phi ->
      Not ((M.update phi).Satisfies x phi)) :
    forall k, M.iterateUpdate phi (2 + k) = M.iterateUpdate phi 2 := by
  have hempty := M.iterateUpdate_two_rel_empty_of_selfRefuting phi h
  have hstep : M.iterateUpdate phi 3 = M.iterateUpdate phi 2 := by
    change (M.iterateUpdate phi 2).update phi = M.iterateUpdate phi 2
    exact update_eq_self_of_rel_empty _ phi hempty
  exact M.iterateUpdate_eq_of_step phi hstep

/-- If every initially true state remains true after one announcement, the
first updated model is already a fixed point. -/
theorem iterateUpdate_two_eq_one_of_truth_mono
    (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (h : forall x, M.Satisfies x phi -> (M.update phi).Satisfies x phi) :
    M.iterateUpdate phi 2 = M.iterateUpdate phi 1 := by
  apply Model.ext'
  · intro i x y
    constructor
    · exact fun hxy => hxy.1
    · intro hxy
      exact ⟨hxy, h y hxy.2⟩
  · intro p x
    rfl

end Model

namespace Collapse

open Pattern Sigma

variable {Atom : Type v} {Agent : Type w}

/-- Paper Lemma `lem:00-validity_collapse`, multi-agent K45 half. -/
theorem k45_valid_zeroZero_implies_zerosInf
    (phi : Formula Atom Agent)
    (h : Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      phi Pattern.zeroZero) :
    Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      phi Pattern.zerosInf := by
  intro World M hM x hx
  have hx0 : Not (M.Satisfies x phi) := by simpa [Pattern.zeroZero] using hx
  intro n
  simp only [Pattern.HoldsBit]
  induction n with
  | zero => exact hx0
  | succ n ih =>
      have hMn : IsK45 (M.iterateUpdate phi n) := M.iterateUpdate_isK45 hM phi n
      have hreal := h (M.iterateUpdate phi n) hMn x
        (by simpa [Pattern.zeroZero, Model.trace] using ih)
      exact (Sigma.realizes_bits2_iff (M.iterateUpdate phi n) x phi false false).mp
        hreal |>.2

/-- Paper Lemma `lem:11-validity_collapse`, in its strongest form: no frame
condition is needed. -/
theorem valid_oneOne_implies_onesInf
    (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent)
    (h : Sigma.Valid C phi Pattern.oneOne) :
    Sigma.Valid C phi Pattern.onesInf := by
  intro World M hM x hx
  have hfinite := h M hM x (by simpa [Pattern.oneOne] using hx)
  have hpair := (Sigma.realizes_bits2_iff M x phi true true).mp hfinite
  have hmono : forall y, M.Satisfies y phi -> (M.update phi).Satisfies y phi := by
    intro y hy
    have hyreal := h M hM y (by simpa [Pattern.oneOne] using hy)
    exact (Sigma.realizes_bits2_iff M y phi true true).mp hyreal |>.2
  have hstep := M.iterateUpdate_two_eq_one_of_truth_mono phi hmono
  have hstable := M.iterateUpdate_eq_of_step phi (n := 1) hstep
  intro n
  cases n with
  | zero => simpa [Pattern.onesInf, Pattern.HoldsBit, Model.trace] using hpair.1
  | succ n =>
      have heq : M.iterateUpdate phi (Nat.succ n) = M.iterateUpdate phi 1 := by
        simpa [Nat.succ_eq_add_one, Nat.add_comm] using hstable n
      change (M.iterateUpdate phi (Nat.succ n)).Satisfies x phi
      rw [heq]
      simpa [Model.iterateUpdate] using hpair.2

/-- Paper Lemma `lem:101-validity_collapse`, again frame-independent. -/
theorem valid_oneZeroOne_implies_oneZeroOnesInf
    (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent)
    (h : Sigma.Valid C phi (Pattern.bits3 true false true)) :
    Sigma.Valid C phi Pattern.oneZeroOnesInf := by
  intro World M hM x hx
  have hfinite := h M hM x (by simpa using hx)
  have htriple : M.trace x phi 0 /\ Not (M.trace x phi 1) /\ M.trace x phi 2 := by
    simpa [Sigma.Realizes, Pattern.HoldsBit] using
      (Pattern.realizesTrace_bits3.mp hfinite)
  have hrefute : forall y, M.Satisfies y phi ->
      Not ((M.update phi).Satisfies y phi) := by
    intro y hy
    have hyreal := h M hM y (by simpa using hy)
    have hytriple := Pattern.realizesTrace_bits3.mp hyreal
    simpa [Pattern.HoldsBit, Model.trace] using hytriple.2.1
  have hstable := M.iterateUpdate_stable_from_two_of_selfRefuting phi hrefute
  intro n
  cases n with
  | zero => simpa [Pattern.oneZeroOnesInf, Pattern.HoldsBit] using htriple.1
  | succ n =>
      cases n with
      | zero => simpa [Pattern.oneZeroOnesInf, Pattern.HoldsBit] using htriple.2.1
      | succ n =>
          have heq : M.iterateUpdate phi (Nat.succ (Nat.succ n)) =
              M.iterateUpdate phi 2 := by
            rw [show Nat.succ (Nat.succ n) = 2 + n by omega]
            exact hstable n
          change (M.iterateUpdate phi (Nat.succ (Nat.succ n))).Satisfies x phi
          rw [heq]
          exact htriple.2.2

/-- The `k >= 2` half of paper Lemma `lem:10k-validity_collapse`: already
`100`-validity forces the entire tail to remain false.  No frame hypothesis is
needed for this update-algebraic fact. -/
theorem valid_oneZeroZero_implies_oneZerosInf
    (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent)
    (h : Sigma.Valid C phi (Pattern.bits3 true false false)) :
    Sigma.Valid C phi Pattern.oneZerosInf := by
  intro World M hM x hx
  have hfinite := h M hM x (by simpa using hx)
  have htriple : M.trace x phi 0 /\ Not (M.trace x phi 1) /\
      Not (M.trace x phi 2) := by
    simpa [Sigma.Realizes, Pattern.HoldsBit] using
      (Pattern.realizesTrace_bits3.mp hfinite)
  have hrefute : forall y, M.Satisfies y phi ->
      Not ((M.update phi).Satisfies y phi) := by
    intro y hy
    have hyreal := h M hM y (by simpa using hy)
    have hytriple := Pattern.realizesTrace_bits3.mp hyreal
    simpa [Pattern.HoldsBit, Model.trace] using hytriple.2.1
  have hstable := M.iterateUpdate_stable_from_two_of_selfRefuting phi hrefute
  intro n
  cases n with
  | zero => simpa [Pattern.oneZerosInf, Pattern.HoldsBit] using htriple.1
  | succ n =>
      cases n with
      | zero => simpa [Pattern.oneZerosInf, Pattern.HoldsBit] using htriple.2.1
      | succ n =>
          have heq : M.iterateUpdate phi (Nat.succ (Nat.succ n)) =
              M.iterateUpdate phi 2 := by
            rw [show Nat.succ (Nat.succ n) = 2 + n by omega]
            exact hstable n
          change Not ((M.iterateUpdate phi (Nat.succ (Nat.succ n))).Satisfies x phi)
          rw [heq]
          exact htriple.2.2

/-- The K45 half of paper Lemma `lem:10k-validity_collapse`: self-refutation
already forces permanent falsity. -/
theorem k45_valid_oneZero_implies_oneZerosInf
    (phi : Formula Atom Agent)
    (h : Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      phi Pattern.oneZero) :
    Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      phi Pattern.oneZerosInf := by
  intro World M hM x hx
  have hfinite := h M hM x (by simpa [Pattern.oneZero] using hx)
  have hpair := (Sigma.realizes_bits2_iff M x phi true false).mp hfinite
  have hrefute : forall y, M.Satisfies y phi ->
      Not ((M.update phi).Satisfies y phi) := by
    intro y hy
    have hyreal := h M hM y (by simpa [Pattern.oneZero] using hy)
    exact (Sigma.realizes_bits2_iff M y phi true false).mp hyreal |>.2
  have hempty := M.iterateUpdate_two_rel_empty_of_selfRefuting phi hrefute
  have hstep : M.iterateUpdate phi 3 = M.iterateUpdate phi 2 := by
    change (M.iterateUpdate phi 2).update phi = M.iterateUpdate phi 2
    exact Model.update_eq_self_of_rel_empty _ phi hempty
  have htwoFalse : Not (M.trace x phi 2) := by
    intro htwo
    have hMtwo : IsK45 (M.iterateUpdate phi 2) := M.iterateUpdate_isK45 hM phi 2
    have htwoReal := h (M.iterateUpdate phi 2) hMtwo x (by simpa using htwo)
    have hfalseNext :=
      (Sigma.realizes_bits2_iff (M.iterateUpdate phi 2) x phi true false).mp htwoReal |>.2
    apply hfalseNext
    change (M.iterateUpdate phi 3).Satisfies x phi
    rw [hstep]
    exact htwo
  have hstable := M.iterateUpdate_eq_of_step phi (n := 2) hstep
  intro n
  cases n with
  | zero => simpa [Pattern.oneZerosInf, Pattern.HoldsBit] using hpair.1
  | succ n =>
      cases n with
      | zero => simpa [Pattern.oneZerosInf, Pattern.HoldsBit] using hpair.2
      | succ n =>
          have heq : M.iterateUpdate phi (Nat.succ (Nat.succ n)) =
              M.iterateUpdate phi 2 := by
            rw [show Nat.succ (Nat.succ n) = 2 + n by omega]
            exact hstable n
          change Not ((M.iterateUpdate phi (Nat.succ (Nat.succ n))).Satisfies x phi)
          rw [heq]
          exact htwoFalse

end Collapse

end ClassificationSigmaValidity
