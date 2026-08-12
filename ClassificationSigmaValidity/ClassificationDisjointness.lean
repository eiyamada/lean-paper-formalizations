import ClassificationSigmaValidity.EquivalenceClasses
import ClassificationSigmaValidity.ExistenceZeroOne
import ClassificationSigmaValidity.ExistenceS5Zero
import ClassificationSigmaValidity.ExistenceKD45Zero
import ClassificationSigmaValidity.Examples

/-!
# Separation of the validity classes

The classification theorem is about equality of sets of valid formulas, not
merely inequality of bit strings.  This module records explicit separating
formulas for the representative classes and the two parametric hierarchies.
-/

namespace ClassificationSigmaValidity

universe u v w

namespace ClassificationDisjointness

open Pattern Sigma

variable {Atom : Type v} {Agent : Type w}

theorem not_valEq_of_valid_not_valid
    {C : FrameClass.{u} Atom Agent} {sigma tau : Pattern}
    {phi : Formula Atom Agent} (hsigma : Sigma.Valid C phi sigma)
    (htau : Not (Sigma.Valid C phi tau)) : Not (Sigma.ValEq C sigma tau) := by
  intro heq
  exact htau ((heq phi).mp hsigma)

theorem not_valEq_symm
    {C : FrameClass.{u} Atom Agent} {sigma tau : Pattern}
    (h : Not (Sigma.ValEq C sigma tau)) :
    Not (Sigma.ValEq C tau sigma) := by
  intro hrev
  exact h (Sigma.valEq_symm C hrev)

/-! ## Atomic and modal separators -/

theorem atom_trace_constant {World : Type u} (M : Model World Atom Agent)
    (x : World) (p : Atom) (n : Nat) :
    M.trace x (.atom p) n <-> M.val p x := by
  simp [Model.trace]

theorem atom_valid_zerosInf (C : FrameClass.{u} Atom Agent) (p : Atom) :
    Sigma.Valid C (.atom p) Pattern.zerosInf := by
  intro World M hM x hx n
  have hp : Not (M.val p x) := by simpa [Pattern.HoldsBit, Model.trace] using hx
  simpa [Pattern.HoldsBit, atom_trace_constant] using hp

theorem atom_valid_onesInf (C : FrameClass.{u} Atom Agent) (p : Atom) :
    Sigma.Valid C (.atom p) Pattern.onesInf := by
  intro World M hM x hx n
  have hp : M.val p x := by simpa [Pattern.HoldsBit, Model.trace] using hx
  simpa [Pattern.HoldsBit, atom_trace_constant] using hp

theorem atom_valid_zeros (C : FrameClass.{u} Atom Agent)
    (p : Atom) (k : Nat) (hk : 2 <= k) :
    Sigma.Valid C (.atom p) (Pattern.zeros k hk) :=
  Sigma.valid_of_prefix _ _ (Pattern.zeros_prefix_zerosInf k hk)
    (atom_valid_zerosInf C p)

/-- One-state universal S5 model in which every atom is true. -/
def trueUnitModel (Atom : Type v) (Agent : Type w) :
    Model (ULift.{u} PUnit) Atom Agent where
  rel _ _ _ := True
  val _ _ := True

theorem trueUnitModel_isS5 (Atom : Type v) (Agent : Type w) :
    IsS5 (trueUnitModel Atom Agent) := by
  intro i
  exact ⟨fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

theorem atom_not_valid_zeroOnesInf_k45 (p : Atom) :
    Not (Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (.atom p) Pattern.zeroOnesInf) := by
  intro h
  let M : Model (ULift.{u} PUnit) Atom Agent := Examples.unitModel Atom Agent
  have hM : IsK45 M := (Examples.unitModel_isS5 Atom Agent).isK45
  have hstart : Pattern.HoldsBit Pattern.zeroOnesInf.first
      (M.trace ⟨PUnit.unit⟩ (.atom p) 0) := by
    change Not (M.Satisfies ⟨PUnit.unit⟩ (.atom p))
    simp [M, Examples.unitModel]
  have hreal := h M hM ⟨PUnit.unit⟩ hstart
  have hone := hreal 1
  simp [M, Examples.unitModel, Pattern.HoldsBit, Model.trace] at hone

theorem atom_not_valid_zeroOnes_kd45 (p : Atom) (k : Nat) (hk : 1 <= k) :
    Not (Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (.atom p) (Pattern.zeroOnes k hk)) := by
  intro h
  let M : Model (ULift.{u} PUnit) Atom Agent := Examples.unitModel Atom Agent
  have hM : IsKD45 M := (Examples.unitModel_isS5 Atom Agent).isKD45
  have hstart : Pattern.HoldsBit (Pattern.zeroOnes k hk).first
      (M.trace ⟨PUnit.unit⟩ (.atom p) 0) := by
    change Not (M.Satisfies ⟨PUnit.unit⟩ (.atom p))
    simp [M, Examples.unitModel]
  have hreal := h M hM ⟨PUnit.unit⟩ hstart
  have hone := hreal 1 (by simp; omega)
  simp [M, Examples.unitModel, Pattern.HoldsBit, Model.trace] at hone

theorem atom_not_valid_oneZero_kd45 (p : Atom) :
    Not (Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (.atom p) Pattern.oneZero) := by
  intro h
  let M : Model (ULift.{u} PUnit) Atom Agent := trueUnitModel Atom Agent
  have hM : IsKD45 M := (trueUnitModel_isS5 Atom Agent).isKD45
  have hstart : Pattern.HoldsBit Pattern.oneZero.first
      (M.trace ⟨PUnit.unit⟩ (.atom p) 0) := by
    change M.Satisfies ⟨PUnit.unit⟩ (.atom p)
    simp [M, trueUnitModel]
  have hreal := h M hM ⟨PUnit.unit⟩ hstart
  have hpair := (Pattern.realizesTrace_bits2.mp hreal).2
  simp [M, Pattern.HoldsBit, Model.trace, trueUnitModel] at hpair

theorem atom_not_valid_oneZerosInf_k45 (p : Atom) :
    Not (Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (.atom p) Pattern.oneZerosInf) := by
  intro h
  let M : Model (ULift.{u} PUnit) Atom Agent := trueUnitModel Atom Agent
  have hM : IsK45 M := (trueUnitModel_isS5 Atom Agent).isK45
  have hstart : Pattern.HoldsBit Pattern.oneZerosInf.first
      (M.trace ⟨PUnit.unit⟩ (.atom p) 0) := by
    change M.Satisfies ⟨PUnit.unit⟩ (.atom p)
    simp [M, trueUnitModel]
  have hreal := h M hM ⟨PUnit.unit⟩ hstart
  have hone := hreal 1
  simp [M, Pattern.HoldsBit, Model.trace, trueUnitModel]
    at hone

theorem atom_not_valid_oneZeroOnesInf_kd45 (p : Atom) :
    Not (Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (.atom p) Pattern.oneZeroOnesInf) := by
  intro h
  let M : Model (ULift.{u} PUnit) Atom Agent := trueUnitModel Atom Agent
  have hM : IsKD45 M := (trueUnitModel_isS5 Atom Agent).isKD45
  have hstart : Pattern.HoldsBit Pattern.oneZeroOnesInf.first
      (M.trace ⟨PUnit.unit⟩ (.atom p) 0) := by
    change M.Satisfies ⟨PUnit.unit⟩ (.atom p)
    simp [M, trueUnitModel]
  have hreal := h M hM ⟨PUnit.unit⟩ hstart
  have hone := hreal 1
  simp [M, Pattern.HoldsBit, Model.trace, trueUnitModel]
    at hone

theorem atom_not_valid_oneZerosInf_kd45 (p : Atom) :
    Not (Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (.atom p) Pattern.oneZerosInf) := by
  intro h
  exact atom_not_valid_oneZero_kd45 p
    (Sigma.valid_of_prefix _ _ Pattern.oneZero_prefix_oneZerosInf h)

private theorem oneZero_prefix_oneZeroOnesInf :
    Pattern.oneZero.IsPrefix Pattern.oneZeroOnesInf := by
  intro n hn
  have hn' : n = 0 ∨ n = 1 := by
    have : n < 2 := by simpa [Pattern.oneZero, Pattern.bits2] using hn
    omega
  rcases hn' with rfl | rfl <;> rfl

private theorem zeroOnes_prefix_zeroOnesInf (k : Nat) (hk : 1 <= k) :
    (Pattern.zeroOnes k hk).IsPrefix Pattern.zeroOnesInf := by
  intro n hn
  cases n with
  | zero => rfl
  | succ n => simp

theorem atom_not_valid_zeroOnesInf_kd45 (p : Atom) :
    Not (Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (.atom p) Pattern.zeroOnesInf) := by
  intro h
  exact atom_not_valid_zeroOnes_kd45 p 1 (by omega)
    (Sigma.valid_of_prefix _ _
      (zeroOnes_prefix_zeroOnesInf 1 (by omega)) h)

theorem pOrBox_not_valid_oneZero_kd45 (p : Atom) (i : Agent) :
    Not (Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Examples.pOrBox p i) Pattern.oneZero) := by
  intro h
  let M : Model (ULift.{u} PUnit) Atom Agent := trueUnitModel Atom Agent
  have hM : IsKD45 M := (trueUnitModel_isS5 Atom Agent).isKD45
  have hstart : Pattern.HoldsBit Pattern.oneZero.first
      (M.trace ⟨PUnit.unit⟩ (Examples.pOrBox p i) 0) := by
    change M.Satisfies ⟨PUnit.unit⟩ (Examples.pOrBox p i)
    simp [M, Examples.pOrBox, trueUnitModel]
  have hreal := h M hM ⟨PUnit.unit⟩ hstart
  have hfalse := (Pattern.realizesTrace_bits2.mp hreal).2
  simp [M, Pattern.HoldsBit, Model.trace, Examples.pOrBox, trueUnitModel]
    at hfalse

theorem pOrBox_not_valid_oneZerosInf_kd45 (p : Atom) (i : Agent) :
    Not (Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Examples.pOrBox p i) Pattern.oneZerosInf) := by
  intro h
  exact pOrBox_not_valid_oneZero_kd45 p i
    (Sigma.valid_of_prefix _ _ Pattern.oneZero_prefix_oneZerosInf h)

theorem pOrBox_not_valid_oneZeroOnesInf_kd45 (p : Atom) (i : Agent) :
    Not (Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Examples.pOrBox p i) Pattern.oneZeroOnesInf) := by
  intro h
  exact pOrBox_not_valid_oneZero_kd45 p i
    (Sigma.valid_of_prefix _ _ oneZero_prefix_oneZeroOnesInf h)

theorem pOrBox_valid_zeroOnesInf_kd45 (p : Atom) (i : Agent) :
    Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Examples.pOrBox p i) Pattern.zeroOnesInf :=
  Sigma.valid_mono_class
    (fun {World} (M : Model World Atom Agent) (hM : IsKD45 M) => hM.isK45)
    (Examples.pOrBox_valid_zeroOnesInf p i)

theorem pOrBox_valid_zeroOnes_kd45 (p : Atom) (i : Agent)
    (k : Nat) (hk : 1 <= k) :
    Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Examples.pOrBox p i) (Pattern.zeroOnes k hk) :=
  Sigma.valid_of_prefix _ _ (zeroOnes_prefix_zeroOnesInf k hk)
    (pOrBox_valid_zeroOnesInf_kd45 p i)

theorem moore_valid_oneZero_kd45 (p : Atom) (i : Agent) :
    Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Examples.moore p i) Pattern.oneZero :=
  Sigma.valid_mono_class
    (fun {World} (M : Model World Atom Agent) (hM : IsKD45 M) => hM.isK45)
    (Examples.moore_valid_oneZero p i)

theorem moore_valid_oneZerosInf_kd45 (p : Atom) (i : Agent) :
    Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Examples.moore p i) Pattern.oneZerosInf :=
  Sigma.valid_mono_class
    (fun {World} (M : Model World Atom Agent) (hM : IsKD45 M) => hM.isK45)
    (Examples.moore_valid_oneZerosInf p i)

theorem moore_not_valid_oneZeroOnesInf_kd45 (p : Atom) (i : Agent) :
    Not (Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Examples.moore p i) Pattern.oneZeroOnesInf) := by
  intro h
  let M : Model (ULift.{u} Bool) Atom Agent := Examples.twoWorldModel p
  have hM : IsKD45 M := (Examples.twoWorldModel_isS5 (Agent := Agent) p).isKD45
  have hinitial : M.Satisfies (⟨true⟩ : ULift.{u} Bool)
      (Examples.moore p i) := Examples.twoWorldModel_moore_initial p i
  have h101 := h M hM ⟨true⟩ (by
    simpa [Pattern.oneZeroOnesInf, Pattern.HoldsBit, Model.trace] using hinitial)
  have h100 := moore_valid_oneZerosInf_kd45 p i M hM ⟨true⟩ (by
    simpa [Pattern.oneZerosInf, Pattern.HoldsBit, Model.trace] using hinitial)
  have htrue : M.trace ⟨true⟩ (Examples.moore p i) 2 := by
    simpa [Pattern.oneZeroOnesInf, Pattern.HoldsBit] using h101 2
  have hfalse : Not (M.trace ⟨true⟩ (Examples.moore p i) 2) := by
    simpa [Pattern.oneZerosInf, Pattern.HoldsBit] using h100 2
  exact hfalse htrue

theorem oneZeroOne_valid_oneZero_kd45 [Inhabited Atom]
    (p : Atom) (i : Agent) :
    Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Examples.oneZeroOneFormula p i) Pattern.oneZero := by
  exact (Sigma.valid_oneZero_iff_selfRefuting _ _).2
    (Examples.oneZeroOne_selfRefuting p i)

theorem oneZeroOne_not_valid_oneZerosInf_kd45 [Inhabited Atom]
    (p : Atom) (i : Agent) :
    Not (Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Examples.oneZeroOneFormula p i) Pattern.oneZerosInf) := by
  intro h
  exact Examples.oneZeroOne_not_valid_100 p i
    (Sigma.valid_of_prefix _ _ Pattern.oneZeroZero_prefix_oneZerosInf h)

def boxBottom [Inhabited Atom] (i : Agent) : Formula Atom Agent :=
  .box i Formula.falsum

theorem boxBottom_persistent [Inhabited Atom] {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent)
    (h : M.Satisfies x (boxBottom i)) :
    (M.update (boxBottom i)).Satisfies x (boxBottom i) := by
  intro y hxy
  exact h y hxy.1

theorem boxBottom_valid_onesInf [Inhabited Atom]
    (C : FrameClass.{u} Atom Agent) (i : Agent) :
    Sigma.Valid C (boxBottom i) Pattern.onesInf := by
  intro World M hM x hx n
  have hzero : M.Satisfies x (boxBottom i) := by
    simpa [Pattern.onesInf, Pattern.HoldsBit, Model.trace] using hx
  have hn : (M.iterateUpdate (boxBottom i) n).Satisfies x (boxBottom i) := by
    induction n with
    | zero => exact hzero
    | succ n ih =>
        rw [Model.iterateUpdate_succ]
        exact boxBottom_persistent _ _ i ih
  simpa [Pattern.onesInf, Pattern.HoldsBit, Model.trace] using hn

theorem boxBottom_not_valid_zerosInf_s5 [Inhabited Atom] (i : Agent) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (boxBottom i) Pattern.zerosInf) := by
  intro h
  let M : Model (ULift.{u} PUnit) Atom Agent := Examples.unitModel Atom Agent
  have hM : IsS5 M := Examples.unitModel_isS5 Atom Agent
  have hinitial : Not (M.Satisfies ⟨PUnit.unit⟩ (boxBottom i)) := by
    intro hbox
    exact Model.satisfies_falsum M ⟨PUnit.unit⟩
      (hbox ⟨PUnit.unit⟩ (by simp [M, Examples.unitModel]))
  have hreal := h M hM ⟨PUnit.unit⟩ (by
    simpa [Pattern.zerosInf, Pattern.first, Pattern.HoldsBit, Model.trace]
      using hinitial)
  have hone := hreal 1
  have hupdated : (M.update (boxBottom i)).Satisfies ⟨PUnit.unit⟩
      (boxBottom i) := by
    intro y hxy
    exact hinitial hxy.2 |>.elim
  have hfalse : Not ((M.update (boxBottom i)).Satisfies ⟨PUnit.unit⟩
      (boxBottom i)) := by
    simpa [Pattern.zerosInf, Pattern.HoldsBit, Model.trace] using hone
  exact hfalse hupdated

theorem boxBottom_not_valid_zeros_s5 [Inhabited Atom]
    (i : Agent) (n : Nat) (hn : 2 <= n) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (boxBottom i) (Pattern.zeros n hn)) := by
  intro h
  let M : Model (ULift.{u} PUnit) Atom Agent := Examples.unitModel Atom Agent
  have hM : IsS5 M := Examples.unitModel_isS5 Atom Agent
  have hinitial : Not (M.Satisfies ⟨PUnit.unit⟩ (boxBottom i)) := by
    intro hbox
    exact Model.satisfies_falsum M ⟨PUnit.unit⟩
      (hbox ⟨PUnit.unit⟩ (by simp [M, Examples.unitModel]))
  have hreal := h M hM ⟨PUnit.unit⟩ (by
    simpa [Pattern.zeros, Pattern.first, Pattern.HoldsBit, Model.trace]
      using hinitial)
  have hone := hreal 1 (by simpa [Pattern.zeros] using hn)
  have hupdated : (M.update (boxBottom i)).Satisfies ⟨PUnit.unit⟩
      (boxBottom i) := by
    intro y hxy
    exact hinitial hxy.2 |>.elim
  have hfalse : Not ((M.update (boxBottom i)).Satisfies ⟨PUnit.unit⟩
      (boxBottom i)) := by
    simpa [Pattern.zeros, Pattern.HoldsBit, Model.trace] using hone
  exact hfalse hupdated

theorem boxBottom_not_valid_zeros_kd45 [Inhabited Atom]
    (i : Agent) (n : Nat) (hn : 2 <= n) :
    Not (Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (boxBottom i) (Pattern.zeros n hn)) := by
  intro h
  exact boxBottom_not_valid_zeros_s5 i n hn
    (Sigma.valid_mono_class
      (fun {World} (M : Model World Atom Agent) (hM : IsS5 M) => hM.isKD45)
      h)

/-! ## Fixed representatives -/

theorem k45_zerosInf_ne_onesInf [Inhabited Atom] (i : Agent) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Atom Agent)
      Pattern.zerosInf Pattern.onesInf) := by
  intro heq
  have hones : Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (boxBottom i) Pattern.onesInf := boxBottom_valid_onesInf _ i
  have hzeros : Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (boxBottom i) Pattern.zerosInf := (heq (boxBottom i)).mpr hones
  exact boxBottom_not_valid_zerosInf_s5 i
    (Sigma.valid_mono_class
      (fun {World} (M : Model World Atom Agent) (hM : IsS5 M) => hM.isK45)
      hzeros)

theorem k45_zerosInf_ne_zeroOnesInf (p : Atom) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Atom Agent)
      Pattern.zerosInf Pattern.zeroOnesInf) :=
  not_valEq_of_valid_not_valid (atom_valid_zerosInf _ p)
    (atom_not_valid_zeroOnesInf_k45 p)

theorem k45_zerosInf_ne_oneZerosInf (p : Atom) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Atom Agent)
      Pattern.zerosInf Pattern.oneZerosInf) :=
  not_valEq_of_valid_not_valid (atom_valid_zerosInf _ p)
    (atom_not_valid_oneZerosInf_k45 p)

theorem k45_onesInf_ne_zeroOnesInf (p : Atom) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Atom Agent)
      Pattern.onesInf Pattern.zeroOnesInf) :=
  not_valEq_of_valid_not_valid (atom_valid_onesInf _ p)
    (atom_not_valid_zeroOnesInf_k45 p)

theorem k45_onesInf_ne_oneZerosInf (p : Atom) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Atom Agent)
      Pattern.onesInf Pattern.oneZerosInf) :=
  not_valEq_of_valid_not_valid (atom_valid_onesInf _ p)
    (atom_not_valid_oneZerosInf_k45 p)

theorem k45_zeroOnesInf_ne_oneZerosInf (p : Atom) (i : Agent) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Atom Agent)
      Pattern.zeroOnesInf Pattern.oneZerosInf) :=
  not_valEq_of_valid_not_valid (Examples.pOrBox_valid_zeroOnesInf p i) (by
    intro h
    let M : Model (ULift.{u} PUnit) Atom Agent := trueUnitModel Atom Agent
    have hM : IsK45 M := (trueUnitModel_isS5 Atom Agent).isK45
    have hstart : Pattern.HoldsBit Pattern.oneZerosInf.first
        (M.trace ⟨PUnit.unit⟩ (Examples.pOrBox p i) 0) := by
      change M.Satisfies ⟨PUnit.unit⟩ (Examples.pOrBox p i)
      simp [M, Examples.pOrBox, trueUnitModel]
    have hreal := h M hM ⟨PUnit.unit⟩ hstart
    have hone := hreal 1
    simp [M, Pattern.HoldsBit, Model.trace,
      Examples.pOrBox, trueUnitModel] at hone)

/-! The finite `01^k` representatives also have to be separated from each
fixed K45 representative.  The parametric hierarchy below separates them
from one another and from `01^omega`; these three declarations record the
remaining cross-family comparisons explicitly. -/

theorem atom_not_valid_zeroOnes_k45
    (p : Atom) (k : Nat) (hk : 1 <= k) :
    Not (Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (.atom p) (Pattern.zeroOnes k hk)) := by
  intro h
  exact atom_not_valid_zeroOnes_kd45 p k hk
    (Sigma.valid_mono_class
      (fun {World} (M : Model World Atom Agent) (hM : IsKD45 M) => hM.isK45)
      h)

theorem pOrBox_not_valid_oneZerosInf_k45 (p : Atom) (i : Agent) :
    Not (Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (Examples.pOrBox p i) Pattern.oneZerosInf) := by
  intro h
  let M : Model (ULift.{u} PUnit) Atom Agent := trueUnitModel Atom Agent
  have hM : IsK45 M := (trueUnitModel_isS5 Atom Agent).isK45
  have hstart : Pattern.HoldsBit Pattern.oneZerosInf.first
      (M.trace ⟨PUnit.unit⟩ (Examples.pOrBox p i) 0) := by
    change M.Satisfies ⟨PUnit.unit⟩ (Examples.pOrBox p i)
    simp [M, Examples.pOrBox, trueUnitModel]
  have hreal := h M hM ⟨PUnit.unit⟩ hstart
  have hone := hreal 1
  simp [M, Pattern.HoldsBit, Model.trace,
    Examples.pOrBox, trueUnitModel] at hone

theorem k45_zeroOnes_ne_zerosInf
    (p : Atom) (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.zerosInf) :=
  not_valEq_symm (not_valEq_of_valid_not_valid
    (atom_valid_zerosInf _ p) (atom_not_valid_zeroOnes_k45 p k hk))

theorem k45_zeroOnes_ne_onesInf
    (p : Atom) (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.onesInf) :=
  not_valEq_symm (not_valEq_of_valid_not_valid
    (atom_valid_onesInf _ p) (atom_not_valid_zeroOnes_k45 p k hk))

theorem k45_zeroOnes_ne_oneZerosInf
    (p : Atom) (i : Agent) (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.oneZerosInf) :=
  not_valEq_of_valid_not_valid
    (Sigma.valid_of_prefix _ _ (zeroOnes_prefix_zeroOnesInf k hk)
      (Examples.pOrBox_valid_zeroOnesInf p i))
    (pOrBox_not_valid_oneZerosInf_k45 p i)

/-! ## The three KD45 classes beginning with `10` -/

theorem kd45_zerosInf_ne_onesInf [Inhabited Atom] (i : Agent) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.zerosInf Pattern.onesInf) := by
  intro heq
  have hones : Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (boxBottom i) Pattern.onesInf := boxBottom_valid_onesInf _ i
  have hzeros : Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (boxBottom i) Pattern.zerosInf := by
    intro World M hM x hx
    exact ((heq (boxBottom i)).mpr hones) M hM x hx
  exact boxBottom_not_valid_zerosInf_s5 i
    (Sigma.valid_mono_class
      (fun {World} (M : Model World Atom Agent) (hM : IsS5 M) => hM.isKD45)
      hzeros)

theorem kd45_zerosInf_ne_zeroOnesInf (p : Atom) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.zerosInf Pattern.zeroOnesInf) :=
  not_valEq_of_valid_not_valid (atom_valid_zerosInf _ p)
    (atom_not_valid_zeroOnesInf_kd45 p)

theorem kd45_onesInf_ne_zeroOnesInf (p : Atom) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.onesInf Pattern.zeroOnesInf) :=
  not_valEq_of_valid_not_valid (atom_valid_onesInf _ p)
    (atom_not_valid_zeroOnesInf_kd45 p)

/-- The `101` witness is `10`-valid but not permanently false. -/
theorem kd45_oneZero_ne_oneZerosInf (p : Atom) (i : Agent) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.oneZero Pattern.oneZerosInf) := by
  letI : Inhabited Atom := ⟨p⟩
  exact not_valEq_of_valid_not_valid
    (oneZeroOne_valid_oneZero_kd45 p i)
    (oneZeroOne_not_valid_oneZerosInf_kd45 p i)

/-- Moore's sentence stays false and therefore separates `10` from `101ω`. -/
theorem kd45_oneZero_ne_oneZeroOnesInf (p : Atom) (i : Agent) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.oneZero Pattern.oneZeroOnesInf) :=
  not_valEq_of_valid_not_valid (moore_valid_oneZero_kd45 p i)
    (moore_not_valid_oneZeroOnesInf_kd45 p i)

/-- Moore's sentence also separates the two infinite `10`-tail classes. -/
theorem kd45_oneZerosInf_ne_oneZeroOnesInf (p : Atom) (i : Agent) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.oneZerosInf Pattern.oneZeroOnesInf) :=
  not_valEq_of_valid_not_valid (moore_valid_oneZerosInf_kd45 p i)
    (moore_not_valid_oneZeroOnesInf_kd45 p i)

/-! ## Separating the `10` classes from the other fixed families -/

theorem kd45_zerosInf_ne_oneZero (p : Atom) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.zerosInf Pattern.oneZero) :=
  not_valEq_of_valid_not_valid (atom_valid_zerosInf _ p)
    (atom_not_valid_oneZero_kd45 p)

theorem kd45_zerosInf_ne_oneZerosInf (p : Atom) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.zerosInf Pattern.oneZerosInf) :=
  not_valEq_of_valid_not_valid (atom_valid_zerosInf _ p)
    (atom_not_valid_oneZerosInf_kd45 p)

theorem kd45_zerosInf_ne_oneZeroOnesInf (p : Atom) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.zerosInf Pattern.oneZeroOnesInf) :=
  not_valEq_of_valid_not_valid (atom_valid_zerosInf _ p)
    (atom_not_valid_oneZeroOnesInf_kd45 p)

theorem kd45_onesInf_ne_oneZero (p : Atom) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.onesInf Pattern.oneZero) :=
  not_valEq_of_valid_not_valid (atom_valid_onesInf _ p)
    (atom_not_valid_oneZero_kd45 p)

theorem kd45_onesInf_ne_oneZerosInf (p : Atom) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.onesInf Pattern.oneZerosInf) :=
  not_valEq_of_valid_not_valid (atom_valid_onesInf _ p)
    (atom_not_valid_oneZerosInf_kd45 p)

theorem kd45_onesInf_ne_oneZeroOnesInf (p : Atom) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.onesInf Pattern.oneZeroOnesInf) :=
  not_valEq_of_valid_not_valid (atom_valid_onesInf _ p)
    (atom_not_valid_oneZeroOnesInf_kd45 p)

theorem kd45_zeroOnesInf_ne_oneZero (p : Atom) (i : Agent) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.zeroOnesInf Pattern.oneZero) :=
  not_valEq_of_valid_not_valid (pOrBox_valid_zeroOnesInf_kd45 p i)
    (pOrBox_not_valid_oneZero_kd45 p i)

theorem kd45_zeroOnesInf_ne_oneZerosInf (p : Atom) (i : Agent) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.zeroOnesInf Pattern.oneZerosInf) :=
  not_valEq_of_valid_not_valid (pOrBox_valid_zeroOnesInf_kd45 p i)
    (pOrBox_not_valid_oneZerosInf_kd45 p i)

theorem kd45_zeroOnesInf_ne_oneZeroOnesInf (p : Atom) (i : Agent) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      Pattern.zeroOnesInf Pattern.oneZeroOnesInf) :=
  not_valEq_of_valid_not_valid (pOrBox_valid_zeroOnesInf_kd45 p i)
    (pOrBox_not_valid_oneZeroOnesInf_kd45 p i)

theorem kd45_zeroOnes_ne_oneZero (p : Atom) (i : Agent)
    (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.oneZero) :=
  not_valEq_of_valid_not_valid (pOrBox_valid_zeroOnes_kd45 p i k hk)
    (pOrBox_not_valid_oneZero_kd45 p i)

theorem kd45_zeroOnes_ne_oneZerosInf (p : Atom) (i : Agent)
    (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.oneZerosInf) :=
  not_valEq_of_valid_not_valid (pOrBox_valid_zeroOnes_kd45 p i k hk)
    (pOrBox_not_valid_oneZerosInf_kd45 p i)

theorem kd45_zeroOnes_ne_oneZeroOnesInf (p : Atom) (i : Agent)
    (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.oneZeroOnesInf) :=
  not_valEq_of_valid_not_valid (pOrBox_valid_zeroOnes_kd45 p i k hk)
    (pOrBox_not_valid_oneZeroOnesInf_kd45 p i)

theorem kd45_zeroOnes_ne_zerosInf (p : Atom)
    (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.zerosInf) := by
  intro heq
  exact atom_not_valid_zeroOnes_kd45 p k hk
    ((heq (.atom p)).mpr (atom_valid_zerosInf _ p))

theorem kd45_zeroOnes_ne_onesInf (p : Atom)
    (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.onesInf) := by
  intro heq
  exact atom_not_valid_zeroOnes_kd45 p k hk
    ((heq (.atom p)).mpr (atom_valid_onesInf _ p))

/-! Finite all-zero classes are separated from every nonzero fixed family by
the atomic formula, except for `1ω`, where the vacuous-box witness is used. -/

theorem kd45_zeros_ne_zeroOnes (p : Atom)
    (k : Nat) (hk : 2 <= k) (m : Nat) (hm : 1 <= m) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Pattern.zeros k hk) (Pattern.zeroOnes m hm)) :=
  not_valEq_of_valid_not_valid (atom_valid_zeros _ p k hk)
    (atom_not_valid_zeroOnes_kd45 p m hm)

theorem kd45_zeros_ne_zeroOnesInf (p : Atom)
    (k : Nat) (hk : 2 <= k) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Pattern.zeros k hk) Pattern.zeroOnesInf) :=
  not_valEq_of_valid_not_valid (atom_valid_zeros _ p k hk)
    (atom_not_valid_zeroOnesInf_kd45 p)

theorem kd45_zeros_ne_oneZero (p : Atom)
    (k : Nat) (hk : 2 <= k) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Pattern.zeros k hk) Pattern.oneZero) :=
  not_valEq_of_valid_not_valid (atom_valid_zeros _ p k hk)
    (atom_not_valid_oneZero_kd45 p)

theorem kd45_zeros_ne_oneZerosInf (p : Atom)
    (k : Nat) (hk : 2 <= k) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Pattern.zeros k hk) Pattern.oneZerosInf) :=
  not_valEq_of_valid_not_valid (atom_valid_zeros _ p k hk)
    (atom_not_valid_oneZerosInf_kd45 p)

theorem kd45_zeros_ne_oneZeroOnesInf (p : Atom)
    (k : Nat) (hk : 2 <= k) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Pattern.zeros k hk) Pattern.oneZeroOnesInf) :=
  not_valEq_of_valid_not_valid (atom_valid_zeros _ p k hk)
    (atom_not_valid_oneZeroOnesInf_kd45 p)

theorem kd45_zeros_ne_onesInf [Inhabited Atom] (i : Agent)
    (k : Nat) (hk : 2 <= k) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Pattern.zeros k hk) Pattern.onesInf) := by
  intro heq
  exact boxBottom_not_valid_zeros_kd45 i k hk
    ((heq (boxBottom i)).mpr (boxBottom_valid_onesInf _ i))

/-! ## The finite `01^k` hierarchy -/

theorem zeroOnes_ne_zeroOnes_of_lt
    [Inhabited Atom] (k m : Nat) (agent : Agent)
    (atomOf : ExistenceZeroOne.Tag k -> Atom)
    (hatom : Function.Injective atomOf) (hk : 1 <= k) (hkm : k < m) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) (Pattern.zeroOnes m (by omega))) := by
  have hvalid : Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (ExistenceZeroOne.witness k agent atomOf) (Pattern.zeroOnes k hk) :=
    ExistenceZeroOne.witness_valid_zeroOnes k hk agent atomOf
  apply not_valEq_of_valid_not_valid hvalid
  intro hm
  have hprefix : (Pattern.zeroOnes (k + 1) (by omega)).IsPrefix
      (Pattern.zeroOnes m (by omega)) := by
    apply List.prefix_iff_getElem?.mpr
    intro n hn
    cases n with
    | zero => simp
    | succ n =>
        have hnm : n < m := by simp at hn; omega
        simp [hnm]
  have hnext : Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (ExistenceZeroOne.witness k agent atomOf)
      (Pattern.zeroOnes (k + 1) (by omega)) :=
    Sigma.valid_of_prefix _ _ hprefix hm
  exact ExistenceZeroOne.witness_not_valid_zeroOnes_succ_k45
    k hk agent atomOf hatom hnext

theorem zeroOnes_ne_zeroOnesInf
    [Inhabited Atom] (k : Nat) (agent : Agent)
    (atomOf : ExistenceZeroOne.Tag k -> Atom)
    (hatom : Function.Injective atomOf) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.zeroOnesInf) := by
  have hvalid : Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (ExistenceZeroOne.witness k agent atomOf) (Pattern.zeroOnes k hk) :=
    ExistenceZeroOne.witness_valid_zeroOnes k hk agent atomOf
  apply not_valEq_of_valid_not_valid hvalid
  intro hinf
  have hprefix : (Pattern.zeroOnes (k + 1) (by omega)).IsPrefix
      Pattern.zeroOnesInf := by
    intro n hn
    cases n with
    | zero => rfl
    | succ n => simp
  have hnext : Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (ExistenceZeroOne.witness k agent atomOf)
      (Pattern.zeroOnes (k + 1) (by omega)) :=
    Sigma.valid_of_prefix _ _ hprefix hinf
  exact ExistenceZeroOne.witness_not_valid_zeroOnes_succ_k45
    k hk agent atomOf hatom hnext

/-! The same `01^k` witnesses separate the KD45 hierarchy because their
countermodels are S5. -/

theorem zeroOnes_witness_valid_kd45 [Inhabited Atom]
    (k : Nat) (hk : 1 <= k) (agent : Agent)
    (atomOf : ExistenceZeroOne.Tag k -> Atom) :
    Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (ExistenceZeroOne.witness k agent atomOf) (Pattern.zeroOnes k hk) :=
  Sigma.valid_mono_class
    (fun {World} (M : Model World Atom Agent) (hM : IsKD45 M) => hM.isK45)
    (ExistenceZeroOne.witness_valid_zeroOnes k hk agent atomOf)

theorem zeroOnes_witness_not_valid_succ_kd45 [Inhabited Atom]
    (k : Nat) (hk : 1 <= k) (agent : Agent)
    (atomOf : ExistenceZeroOne.Tag k -> Atom)
    (hatom : Function.Injective atomOf) :
    Not (Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (ExistenceZeroOne.witness k agent atomOf)
      (Pattern.zeroOnes (k + 1) (by omega))) := by
  intro hvalid
  let M : Model (ULift.{u} (ExistenceZeroOne.Tag k)) Atom Agent :=
    ExistenceZeroOne.canonicalModel k atomOf
  have hM : IsKD45 M :=
    (ExistenceZeroOne.canonical_isS5 (Agent := Agent) k atomOf).isKD45
  rcases ExistenceZeroOne.canonical_root_trace k agent atomOf hatom with
    ⟨hzero, hones, hlast⟩
  have hreal := hvalid M hM ⟨ExistenceZeroOne.Tag.root⟩ (by
    simpa [Pattern.zeroOnes, Pattern.first] using hzero)
  have hAt := hreal (k + 1) (by simp)
  have htrue : M.trace ⟨ExistenceZeroOne.Tag.root⟩
      (ExistenceZeroOne.witness k agent atomOf) (k + 1) := by
    simpa [Pattern.zeroOnes, Pattern.HoldsBit, List.getElem_cons_succ,
      List.getElem_replicate] using hAt
  exact hlast htrue

theorem kd45_zeroOnes_ne_zeroOnes_of_lt
    [Inhabited Atom] (k m : Nat) (agent : Agent)
    (atomOf : ExistenceZeroOne.Tag k -> Atom)
    (hatom : Function.Injective atomOf) (hk : 1 <= k) (hkm : k < m) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) (Pattern.zeroOnes m (by omega))) := by
  apply not_valEq_of_valid_not_valid
    (zeroOnes_witness_valid_kd45 k hk agent atomOf)
  intro hm
  have hprefix : (Pattern.zeroOnes (k + 1) (by omega)).IsPrefix
      (Pattern.zeroOnes m (by omega)) := by
    apply List.prefix_iff_getElem?.mpr
    intro n hn
    cases n with
    | zero => simp
    | succ n =>
        have hnm : n < m := by simp at hn; omega
        simp [hnm]
  have hnext : Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (ExistenceZeroOne.witness k agent atomOf)
      (Pattern.zeroOnes (k + 1) (by omega)) :=
    Sigma.valid_of_prefix _ _ hprefix hm
  exact zeroOnes_witness_not_valid_succ_kd45
    k hk agent atomOf hatom hnext

theorem kd45_zeroOnes_ne_zeroOnesInf
    [Inhabited Atom] (k : Nat) (agent : Agent)
    (atomOf : ExistenceZeroOne.Tag k -> Atom)
    (hatom : Function.Injective atomOf) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.zeroOnesInf) := by
  apply not_valEq_of_valid_not_valid
    (zeroOnes_witness_valid_kd45 k hk agent atomOf)
  intro hinf
  have hnext : Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (ExistenceZeroOne.witness k agent atomOf)
      (Pattern.zeroOnes (k + 1) (by omega)) :=
    Sigma.valid_of_prefix _ _
      (zeroOnes_prefix_zeroOnesInf (k + 1) (by omega)) hinf
  exact zeroOnes_witness_not_valid_succ_kd45
    k hk agent atomOf hatom hnext

/-! ## The finite `0^k` hierarchy on multi-agent KD45 -/

/-- Distinct finite zero lengths determine distinct KD45 validity classes
when two distinct agents are available. -/
theorem kd45_zeros_ne_zeros_of_lt (a b : Agent) (hab : a ≠ b)
    (k m : Nat) (hk : 2 <= k) (hkm : k < m) :
    Not (Sigma.ValEq
      (Classes.KD45 : FrameClass.{u} Nat Agent)
      (Pattern.zeros k hk) (Pattern.zeros m (by omega))) := by
  have hvalid : Sigma.Valid
      (Classes.KD45 : FrameClass.{u} Nat Agent)
      (KD45Zero.witness a b id k) (Pattern.zeros k hk) := by
    intro World M hM x hx
    exact KD45Zero.witness_valid_zeros (World := World)
      a b id k hk M hM x hx
  apply not_valEq_of_valid_not_valid hvalid
  intro hm
  have hprefix : (Pattern.zeros (k + 1) (by omega)).IsPrefix
      (Pattern.zeros m (by omega)) := by
    apply List.prefix_iff_getElem?.mpr
    intro n hn
    have hnm : n < m := by simp at hn; omega
    simp [hnm]
  have hnext : Sigma.Valid
      (Classes.KD45 : FrameClass.{u} Nat Agent)
      (KD45Zero.witness a b id k) (Pattern.zeros (k + 1) (by omega)) :=
    Sigma.valid_of_prefix _ _ hprefix hm
  exact KD45Zero.witness_not_valid_zeros_succ a b hab k hk hnext

/-- Every finite-zero class is distinct from the infinite all-zero class. -/
theorem kd45_zeros_ne_zerosInf (a b : Agent) (hab : a ≠ b)
    (k : Nat) (hk : 2 <= k) :
    Not (Sigma.ValEq
      (Classes.KD45 : FrameClass.{u} Nat Agent)
      (Pattern.zeros k hk) Pattern.zerosInf) := by
  have hvalid : Sigma.Valid
      (Classes.KD45 : FrameClass.{u} Nat Agent)
      (KD45Zero.witness a b id k) (Pattern.zeros k hk) := by
    intro World M hM x hx
    exact KD45Zero.witness_valid_zeros (World := World)
      a b id k hk M hM x hx
  apply not_valEq_of_valid_not_valid hvalid
  intro hinf
  have hprefix : (Pattern.zeros (k + 1) (by omega)).IsPrefix
      Pattern.zerosInf := Pattern.zeros_prefix_zerosInf (k + 1) (by omega)
  have hnext : Sigma.Valid
      (Classes.KD45 : FrameClass.{u} Nat Agent)
      (KD45Zero.witness a b id k) (Pattern.zeros (k + 1) (by omega)) :=
    Sigma.valid_of_prefix _ _ hprefix hinf
  exact KD45Zero.witness_not_valid_zeros_succ a b hab k hk hnext

/-! ## The finite `0^k` hierarchy on S5 -/

theorem s5_zeros_ne_zeros_of_lt (i : Agent)
    (k m : Nat) (hk : 2 <= k) (hkm : k < m) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Nat Agent)
      (Pattern.zeros k hk) (Pattern.zeros m (by omega))) := by
  have hvalid : Sigma.Valid (Classes.S5 : FrameClass.{u} Nat Agent)
      (S5ZeroWitness.formula i k) (Pattern.zeros k hk) :=
    S5ZeroWitness.valid_zeros i k hk
  apply not_valEq_of_valid_not_valid hvalid
  intro hm
  have hprefix : (Pattern.zeros (k + 1) (by omega)).IsPrefix
      (Pattern.zeros m (by omega)) := by
    apply List.prefix_iff_getElem?.mpr
    intro n hn
    have hnm : n < m := by simp at hn; omega
    simp [hnm]
  have hnext : Sigma.Valid (Classes.S5 : FrameClass.{u} Nat Agent)
      (S5ZeroWitness.formula i k) (Pattern.zeros (k + 1) (by omega)) :=
    Sigma.valid_of_prefix _ _ hprefix hm
  exact S5ZeroWitness.not_valid_zeros_succ i k hk hnext

theorem s5_zeros_ne_zerosInf (i : Agent) (k : Nat) (hk : 2 <= k) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Nat Agent)
      (Pattern.zeros k hk) Pattern.zerosInf) := by
  have hvalid : Sigma.Valid (Classes.S5 : FrameClass.{u} Nat Agent)
      (S5ZeroWitness.formula i k) (Pattern.zeros k hk) :=
    S5ZeroWitness.valid_zeros i k hk
  apply not_valEq_of_valid_not_valid hvalid
  intro hinf
  have hprefix : (Pattern.zeros (k + 1) (by omega)).IsPrefix
      Pattern.zerosInf := Pattern.zeros_prefix_zerosInf (k + 1) (by omega)
  have hnext : Sigma.Valid (Classes.S5 : FrameClass.{u} Nat Agent)
      (S5ZeroWitness.formula i k) (Pattern.zeros (k + 1) (by omega)) :=
    Sigma.valid_of_prefix _ _ hprefix hinf
  exact S5ZeroWitness.not_valid_zeros_succ i k hk hnext

theorem s5_zeros_ne_onesInf (i : Agent) (k : Nat) (hk : 2 <= k) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Nat Agent)
      (Pattern.zeros k hk) Pattern.onesInf) := by
  intro heq
  have hones : Sigma.Valid (Classes.S5 : FrameClass.{u} Nat Agent)
      (boxBottom i) Pattern.onesInf := boxBottom_valid_onesInf _ i
  exact boxBottom_not_valid_zeros_s5 i k hk
    ((heq (boxBottom i)).mpr hones)

theorem s5_zeros_ne_zeroOnesInf (k : Nat) (hk : 2 <= k) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Nat Agent)
      (Pattern.zeros k hk) Pattern.zeroOnesInf) := by
  have hzeros : Sigma.Valid (Classes.S5 : FrameClass.{u} Nat Agent)
      (.atom 0) (Pattern.zeros k hk) :=
    Sigma.valid_of_prefix _ _ (Pattern.zeros_prefix_zerosInf k hk)
      (atom_valid_zerosInf _ 0)
  apply not_valEq_of_valid_not_valid hzeros
  intro h
  let M : Model (ULift.{u} PUnit) Nat Agent := Examples.unitModel Nat Agent
  have hM : IsS5 M := Examples.unitModel_isS5 Nat Agent
  have hstart : Pattern.HoldsBit Pattern.zeroOnesInf.first
      (M.trace ⟨PUnit.unit⟩ (.atom 0) 0) := by
    change Not (M.Satisfies ⟨PUnit.unit⟩ (.atom 0))
    simp [M, Examples.unitModel]
  have hreal := h M hM ⟨PUnit.unit⟩ hstart
  have hone := hreal 1
  simp [M, Examples.unitModel, Pattern.HoldsBit, Model.trace] at hone

/-! ## Complete separation on S5

All countermodels used in the elementary KD45 separators above are already
S5.  We record the S5 statements explicitly: inequality of KD45 validity sets
by itself would not imply inequality of S5 validity sets. -/

theorem atom_not_valid_zeroOnes_s5 (p : Atom) (k : Nat) (hk : 1 <= k) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (.atom p) (Pattern.zeroOnes k hk)) := by
  intro h
  let M : Model (ULift.{u} PUnit) Atom Agent := Examples.unitModel Atom Agent
  have hM : IsS5 M := Examples.unitModel_isS5 Atom Agent
  have hstart : Pattern.HoldsBit (Pattern.zeroOnes k hk).first
      (M.trace ⟨PUnit.unit⟩ (.atom p) 0) := by
    change Not (M.Satisfies ⟨PUnit.unit⟩ (.atom p))
    simp [M, Examples.unitModel]
  have hreal := h M hM ⟨PUnit.unit⟩ hstart
  have hone := hreal 1 (by simp; omega)
  simp [M, Examples.unitModel, Pattern.HoldsBit, Model.trace] at hone

theorem atom_not_valid_zeroOnesInf_s5 (p : Atom) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (.atom p) Pattern.zeroOnesInf) := by
  intro h
  exact atom_not_valid_zeroOnes_s5 p 1 (by omega)
    (Sigma.valid_of_prefix _ _
      (zeroOnes_prefix_zeroOnesInf 1 (by omega)) h)

theorem atom_not_valid_oneZero_s5 (p : Atom) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (.atom p) Pattern.oneZero) := by
  intro h
  let M : Model (ULift.{u} PUnit) Atom Agent := trueUnitModel Atom Agent
  have hM : IsS5 M := trueUnitModel_isS5 Atom Agent
  have hstart : Pattern.HoldsBit Pattern.oneZero.first
      (M.trace ⟨PUnit.unit⟩ (.atom p) 0) := by
    change M.Satisfies ⟨PUnit.unit⟩ (.atom p)
    simp [M, trueUnitModel]
  have hreal := h M hM ⟨PUnit.unit⟩ hstart
  have hpair := (Pattern.realizesTrace_bits2.mp hreal).2
  simp [M, Pattern.HoldsBit, Model.trace, trueUnitModel] at hpair

theorem atom_not_valid_oneZerosInf_s5 (p : Atom) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (.atom p) Pattern.oneZerosInf) := by
  intro h
  exact atom_not_valid_oneZero_s5 p
    (Sigma.valid_of_prefix _ _ Pattern.oneZero_prefix_oneZerosInf h)

theorem atom_not_valid_oneZeroOnesInf_s5 (p : Atom) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (.atom p) Pattern.oneZeroOnesInf) := by
  intro h
  exact atom_not_valid_oneZero_s5 p
    (Sigma.valid_of_prefix _ _ oneZero_prefix_oneZeroOnesInf h)

theorem pOrBox_valid_zeroOnesInf_s5 (p : Atom) (i : Agent) :
    Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (Examples.pOrBox p i) Pattern.zeroOnesInf :=
  Sigma.valid_mono_class
    (fun {World} (M : Model World Atom Agent) (hM : IsS5 M) => hM.isK45)
    (Examples.pOrBox_valid_zeroOnesInf p i)

theorem pOrBox_valid_zeroOnes_s5 (p : Atom) (i : Agent)
    (k : Nat) (hk : 1 <= k) :
    Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (Examples.pOrBox p i) (Pattern.zeroOnes k hk) :=
  Sigma.valid_of_prefix _ _ (zeroOnes_prefix_zeroOnesInf k hk)
    (pOrBox_valid_zeroOnesInf_s5 p i)

theorem pOrBox_not_valid_oneZero_s5 (p : Atom) (i : Agent) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (Examples.pOrBox p i) Pattern.oneZero) := by
  intro h
  let M : Model (ULift.{u} PUnit) Atom Agent := trueUnitModel Atom Agent
  have hM : IsS5 M := trueUnitModel_isS5 Atom Agent
  have hstart : Pattern.HoldsBit Pattern.oneZero.first
      (M.trace ⟨PUnit.unit⟩ (Examples.pOrBox p i) 0) := by
    change M.Satisfies ⟨PUnit.unit⟩ (Examples.pOrBox p i)
    simp [M, Examples.pOrBox, trueUnitModel]
  have hreal := h M hM ⟨PUnit.unit⟩ hstart
  have hfalse := (Pattern.realizesTrace_bits2.mp hreal).2
  simp [M, Pattern.HoldsBit, Model.trace, Examples.pOrBox, trueUnitModel]
    at hfalse

theorem pOrBox_not_valid_oneZerosInf_s5 (p : Atom) (i : Agent) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (Examples.pOrBox p i) Pattern.oneZerosInf) := by
  intro h
  exact pOrBox_not_valid_oneZero_s5 p i
    (Sigma.valid_of_prefix _ _ Pattern.oneZero_prefix_oneZerosInf h)

theorem pOrBox_not_valid_oneZeroOnesInf_s5 (p : Atom) (i : Agent) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (Examples.pOrBox p i) Pattern.oneZeroOnesInf) := by
  intro h
  exact pOrBox_not_valid_oneZero_s5 p i
    (Sigma.valid_of_prefix _ _ oneZero_prefix_oneZeroOnesInf h)

theorem moore_valid_oneZero_s5 (p : Atom) (i : Agent) :
    Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (Examples.moore p i) Pattern.oneZero :=
  Sigma.valid_mono_class
    (fun {World} (M : Model World Atom Agent) (hM : IsS5 M) => hM.isK45)
    (Examples.moore_valid_oneZero p i)

theorem moore_valid_oneZerosInf_s5 (p : Atom) (i : Agent) :
    Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (Examples.moore p i) Pattern.oneZerosInf :=
  Sigma.valid_mono_class
    (fun {World} (M : Model World Atom Agent) (hM : IsS5 M) => hM.isK45)
    (Examples.moore_valid_oneZerosInf p i)

theorem moore_not_valid_oneZeroOnesInf_s5 (p : Atom) (i : Agent) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (Examples.moore p i) Pattern.oneZeroOnesInf) := by
  intro h
  let M : Model (ULift.{u} Bool) Atom Agent := Examples.twoWorldModel p
  have hM : IsS5 M := Examples.twoWorldModel_isS5 (Agent := Agent) p
  have hinitial : M.Satisfies (⟨true⟩ : ULift.{u} Bool)
      (Examples.moore p i) := Examples.twoWorldModel_moore_initial p i
  have h101 := h M hM ⟨true⟩ (by
    simpa [Pattern.oneZeroOnesInf, Pattern.HoldsBit, Model.trace] using hinitial)
  have h100 := moore_valid_oneZerosInf_s5 p i M hM ⟨true⟩ (by
    simpa [Pattern.oneZerosInf, Pattern.HoldsBit, Model.trace] using hinitial)
  have htrue : M.trace ⟨true⟩ (Examples.moore p i) 2 := by
    simpa [Pattern.oneZeroOnesInf, Pattern.HoldsBit] using h101 2
  have hfalse : Not (M.trace ⟨true⟩ (Examples.moore p i) 2) := by
    simpa [Pattern.oneZerosInf, Pattern.HoldsBit] using h100 2
  exact hfalse htrue

theorem oneZeroOne_valid_oneZero_s5 [Inhabited Atom]
    (p : Atom) (i : Agent) :
    Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (Examples.oneZeroOneFormula p i) Pattern.oneZero :=
  Sigma.valid_mono_class
    (fun {World} (M : Model World Atom Agent) (hM : IsS5 M) => hM.isKD45)
    (oneZeroOne_valid_oneZero_kd45 p i)

theorem oneZeroOne_not_valid_oneZerosInf_s5 [Inhabited Atom]
    (p : Atom) (i : Agent) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (Examples.oneZeroOneFormula p i) Pattern.oneZerosInf) := by
  intro h
  let M : Model (ULift.{u} (Fin 3)) Atom Agent := Examples.threeWorldModel p
  have hM : IsS5 M := Examples.threeWorldModel_isS5 (Agent := Agent) p
  have hinitial : M.Satisfies (⟨0⟩ : ULift.{u} (Fin 3))
      (Examples.oneZeroOneFormula p i) :=
    Examples.threeWorldModel_oneZeroOne_initial p i
  have hreal := h M hM ⟨0⟩ (by
    simpa [Pattern.oneZerosInf, Pattern.HoldsBit, Model.trace] using hinitial)
  have hfalse : Not (M.trace ⟨0⟩ (Examples.oneZeroOneFormula p i) 2) := by
    simpa [Pattern.oneZerosInf, Pattern.HoldsBit] using hreal 2
  exact hfalse (Examples.threeWorldModel_oneZeroOne_trace_101 p i).2.2

/-! The fixed S5 representatives. -/

theorem s5_zerosInf_ne_onesInf [Inhabited Atom] (i : Agent) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.zerosInf Pattern.onesInf) := by
  intro heq
  exact boxBottom_not_valid_zerosInf_s5 i
    ((heq (boxBottom i)).mpr (boxBottom_valid_onesInf _ i))

theorem s5_zerosInf_ne_zeroOnesInf (p : Atom) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.zerosInf Pattern.zeroOnesInf) :=
  not_valEq_of_valid_not_valid (atom_valid_zerosInf _ p)
    (atom_not_valid_zeroOnesInf_s5 p)

theorem s5_zerosInf_ne_oneZero (p : Atom) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.zerosInf Pattern.oneZero) :=
  not_valEq_of_valid_not_valid (atom_valid_zerosInf _ p)
    (atom_not_valid_oneZero_s5 p)

theorem s5_zerosInf_ne_oneZerosInf (p : Atom) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.zerosInf Pattern.oneZerosInf) :=
  not_valEq_of_valid_not_valid (atom_valid_zerosInf _ p)
    (atom_not_valid_oneZerosInf_s5 p)

theorem s5_zerosInf_ne_oneZeroOnesInf (p : Atom) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.zerosInf Pattern.oneZeroOnesInf) :=
  not_valEq_of_valid_not_valid (atom_valid_zerosInf _ p)
    (atom_not_valid_oneZeroOnesInf_s5 p)

theorem s5_onesInf_ne_zeroOnesInf (p : Atom) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.onesInf Pattern.zeroOnesInf) :=
  not_valEq_of_valid_not_valid (atom_valid_onesInf _ p)
    (atom_not_valid_zeroOnesInf_s5 p)

theorem s5_onesInf_ne_oneZero (p : Atom) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.onesInf Pattern.oneZero) :=
  not_valEq_of_valid_not_valid (atom_valid_onesInf _ p)
    (atom_not_valid_oneZero_s5 p)

theorem s5_onesInf_ne_oneZerosInf (p : Atom) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.onesInf Pattern.oneZerosInf) :=
  not_valEq_of_valid_not_valid (atom_valid_onesInf _ p)
    (atom_not_valid_oneZerosInf_s5 p)

theorem s5_onesInf_ne_oneZeroOnesInf (p : Atom) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.onesInf Pattern.oneZeroOnesInf) :=
  not_valEq_of_valid_not_valid (atom_valid_onesInf _ p)
    (atom_not_valid_oneZeroOnesInf_s5 p)

theorem s5_zeroOnesInf_ne_oneZero (p : Atom) (i : Agent) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.zeroOnesInf Pattern.oneZero) :=
  not_valEq_of_valid_not_valid (pOrBox_valid_zeroOnesInf_s5 p i)
    (pOrBox_not_valid_oneZero_s5 p i)

theorem s5_zeroOnesInf_ne_oneZerosInf (p : Atom) (i : Agent) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.zeroOnesInf Pattern.oneZerosInf) :=
  not_valEq_of_valid_not_valid (pOrBox_valid_zeroOnesInf_s5 p i)
    (pOrBox_not_valid_oneZerosInf_s5 p i)

theorem s5_zeroOnesInf_ne_oneZeroOnesInf (p : Atom) (i : Agent) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.zeroOnesInf Pattern.oneZeroOnesInf) :=
  not_valEq_of_valid_not_valid (pOrBox_valid_zeroOnesInf_s5 p i)
    (pOrBox_not_valid_oneZeroOnesInf_s5 p i)

theorem s5_oneZero_ne_oneZerosInf (p : Atom) (i : Agent) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.oneZero Pattern.oneZerosInf) := by
  letI : Inhabited Atom := ⟨p⟩
  exact not_valEq_of_valid_not_valid
    (oneZeroOne_valid_oneZero_s5 p i)
    (oneZeroOne_not_valid_oneZerosInf_s5 p i)

theorem s5_oneZero_ne_oneZeroOnesInf (p : Atom) (i : Agent) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.oneZero Pattern.oneZeroOnesInf) :=
  not_valEq_of_valid_not_valid (moore_valid_oneZero_s5 p i)
    (moore_not_valid_oneZeroOnesInf_s5 p i)

theorem s5_oneZerosInf_ne_oneZeroOnesInf (p : Atom) (i : Agent) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      Pattern.oneZerosInf Pattern.oneZeroOnesInf) :=
  not_valEq_of_valid_not_valid (moore_valid_oneZerosInf_s5 p i)
    (moore_not_valid_oneZeroOnesInf_s5 p i)

/-! Finite `01^k` representatives against every fixed S5 representative. -/

theorem s5_zeroOnes_ne_zerosInf (p : Atom) (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.zerosInf) := by
  intro heq
  exact atom_not_valid_zeroOnes_s5 p k hk
    ((heq (.atom p)).mpr (atom_valid_zerosInf _ p))

theorem s5_zeroOnes_ne_onesInf (p : Atom) (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.onesInf) := by
  intro heq
  exact atom_not_valid_zeroOnes_s5 p k hk
    ((heq (.atom p)).mpr (atom_valid_onesInf _ p))

theorem s5_zeroOnes_ne_oneZero (p : Atom) (i : Agent)
    (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.oneZero) :=
  not_valEq_of_valid_not_valid (pOrBox_valid_zeroOnes_s5 p i k hk)
    (pOrBox_not_valid_oneZero_s5 p i)

theorem s5_zeroOnes_ne_oneZerosInf (p : Atom) (i : Agent)
    (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.oneZerosInf) :=
  not_valEq_of_valid_not_valid (pOrBox_valid_zeroOnes_s5 p i k hk)
    (pOrBox_not_valid_oneZerosInf_s5 p i)

theorem s5_zeroOnes_ne_oneZeroOnesInf (p : Atom) (i : Agent)
    (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.oneZeroOnesInf) :=
  not_valEq_of_valid_not_valid (pOrBox_valid_zeroOnes_s5 p i k hk)
    (pOrBox_not_valid_oneZeroOnesInf_s5 p i)

/-! Finite-zero representatives against all nonzero S5 families. -/

theorem s5_zeros_ne_zeroOnes (k : Nat) (hk : 2 <= k)
    (m : Nat) (hm : 1 <= m) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Nat Agent)
      (Pattern.zeros k hk) (Pattern.zeroOnes m hm)) :=
  not_valEq_of_valid_not_valid (atom_valid_zeros _ 0 k hk)
    (atom_not_valid_zeroOnes_s5 0 m hm)

theorem s5_zeros_ne_oneZero (k : Nat) (hk : 2 <= k) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Nat Agent)
      (Pattern.zeros k hk) Pattern.oneZero) :=
  not_valEq_of_valid_not_valid (atom_valid_zeros _ 0 k hk)
    (atom_not_valid_oneZero_s5 0)

theorem s5_zeros_ne_oneZerosInf (k : Nat) (hk : 2 <= k) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Nat Agent)
      (Pattern.zeros k hk) Pattern.oneZerosInf) :=
  not_valEq_of_valid_not_valid (atom_valid_zeros _ 0 k hk)
    (atom_not_valid_oneZerosInf_s5 0)

theorem s5_zeros_ne_oneZeroOnesInf (k : Nat) (hk : 2 <= k) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Nat Agent)
      (Pattern.zeros k hk) Pattern.oneZeroOnesInf) :=
  not_valEq_of_valid_not_valid (atom_valid_zeros _ 0 k hk)
    (atom_not_valid_oneZeroOnesInf_s5 0)

/-! The finite `01^k` hierarchy remains strict on S5 because the separating
countermodel in `ExistenceZeroOne` is itself S5. -/

theorem zeroOnes_witness_valid_s5 [Inhabited Atom]
    (k : Nat) (hk : 1 <= k) (agent : Agent)
    (atomOf : ExistenceZeroOne.Tag k -> Atom) :
    Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (ExistenceZeroOne.witness k agent atomOf) (Pattern.zeroOnes k hk) :=
  Sigma.valid_mono_class
    (fun {World} (M : Model World Atom Agent) (hM : IsS5 M) => hM.isK45)
    (ExistenceZeroOne.witness_valid_zeroOnes k hk agent atomOf)

theorem zeroOnes_witness_not_valid_succ_s5 [Inhabited Atom]
    (k : Nat) (hk : 1 <= k) (agent : Agent)
    (atomOf : ExistenceZeroOne.Tag k -> Atom)
    (hatom : Function.Injective atomOf) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (ExistenceZeroOne.witness k agent atomOf)
      (Pattern.zeroOnes (k + 1) (by omega))) := by
  intro hvalid
  let M : Model (ULift.{u} (ExistenceZeroOne.Tag k)) Atom Agent :=
    ExistenceZeroOne.canonicalModel k atomOf
  have hM : IsS5 M :=
    ExistenceZeroOne.canonical_isS5 (Agent := Agent) k atomOf
  rcases ExistenceZeroOne.canonical_root_trace k agent atomOf hatom with
    ⟨hzero, hones, hlast⟩
  have hreal := hvalid M hM ⟨ExistenceZeroOne.Tag.root⟩ (by
    simpa [Pattern.zeroOnes, Pattern.first] using hzero)
  have hAt := hreal (k + 1) (by simp)
  have htrue : M.trace ⟨ExistenceZeroOne.Tag.root⟩
      (ExistenceZeroOne.witness k agent atomOf) (k + 1) := by
    simpa [Pattern.zeroOnes, Pattern.HoldsBit, List.getElem_cons_succ,
      List.getElem_replicate] using hAt
  exact hlast htrue

theorem s5_zeroOnes_ne_zeroOnes_of_lt
    [Inhabited Atom] (k m : Nat) (agent : Agent)
    (atomOf : ExistenceZeroOne.Tag k -> Atom)
    (hatom : Function.Injective atomOf) (hk : 1 <= k) (hkm : k < m) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) (Pattern.zeroOnes m (by omega))) := by
  apply not_valEq_of_valid_not_valid
    (zeroOnes_witness_valid_s5 k hk agent atomOf)
  intro hm
  have hprefix : (Pattern.zeroOnes (k + 1) (by omega)).IsPrefix
      (Pattern.zeroOnes m (by omega)) := by
    apply List.prefix_iff_getElem?.mpr
    intro n hn
    cases n with
    | zero => simp
    | succ n =>
        have hnm : n < m := by simp at hn; omega
        simp [hnm]
  exact zeroOnes_witness_not_valid_succ_s5 k hk agent atomOf hatom
    (Sigma.valid_of_prefix _ _ hprefix hm)

theorem s5_zeroOnes_ne_zeroOnesInf
    [Inhabited Atom] (k : Nat) (agent : Agent)
    (atomOf : ExistenceZeroOne.Tag k -> Atom)
    (hatom : Function.Injective atomOf) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnes k hk) Pattern.zeroOnesInf) := by
  apply not_valEq_of_valid_not_valid
    (zeroOnes_witness_valid_s5 k hk agent atomOf)
  intro hinf
  exact zeroOnes_witness_not_valid_succ_s5 k hk agent atomOf hatom
    (Sigma.valid_of_prefix _ _
      (zeroOnes_prefix_zeroOnesInf (k + 1) (by omega)) hinf)

/-- Publication-facing specialization using the canonical injection of the
finite type names into the paper's countable atom supply. -/
theorem k45_zeroOnes_nat_ne_zeroOnes_of_lt
    (k m : Nat) (agent : Agent) (hk : 1 <= k) (hkm : k < m) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Nat Agent)
      (Pattern.zeroOnes k hk) (Pattern.zeroOnes m (by omega))) :=
  zeroOnes_ne_zeroOnes_of_lt k m agent ExistenceZeroOne.Tag.toNat
    ExistenceZeroOne.Tag.toNat_injective hk hkm

theorem k45_zeroOnes_nat_ne_zeroOnesInf
    (k : Nat) (agent : Agent) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Nat Agent)
      (Pattern.zeroOnes k hk) Pattern.zeroOnesInf) :=
  zeroOnes_ne_zeroOnesInf k agent ExistenceZeroOne.Tag.toNat
    ExistenceZeroOne.Tag.toNat_injective hk

theorem k45_zeroOnes_nat_ne_zerosInf
    (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Nat Agent)
      (Pattern.zeroOnes k hk) Pattern.zerosInf) :=
  k45_zeroOnes_ne_zerosInf 0 k hk

theorem k45_zeroOnes_nat_ne_onesInf
    (k : Nat) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Nat Agent)
      (Pattern.zeroOnes k hk) Pattern.onesInf) :=
  k45_zeroOnes_ne_onesInf 0 k hk

theorem k45_zeroOnes_nat_ne_oneZerosInf
    (k : Nat) (agent : Agent) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.K45 : FrameClass.{u} Nat Agent)
      (Pattern.zeroOnes k hk) Pattern.oneZerosInf) :=
  k45_zeroOnes_ne_oneZerosInf 0 agent k hk

theorem kd45_zeroOnes_nat_ne_zeroOnes_of_lt
    (k m : Nat) (agent : Agent) (hk : 1 <= k) (hkm : k < m) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Nat Agent)
      (Pattern.zeroOnes k hk) (Pattern.zeroOnes m (by omega))) :=
  kd45_zeroOnes_ne_zeroOnes_of_lt k m agent ExistenceZeroOne.Tag.toNat
    ExistenceZeroOne.Tag.toNat_injective hk hkm

theorem kd45_zeroOnes_nat_ne_zeroOnesInf
    (k : Nat) (agent : Agent) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.KD45 : FrameClass.{u} Nat Agent)
      (Pattern.zeroOnes k hk) Pattern.zeroOnesInf) :=
  kd45_zeroOnes_ne_zeroOnesInf k agent ExistenceZeroOne.Tag.toNat
    ExistenceZeroOne.Tag.toNat_injective hk

theorem s5_zeroOnes_nat_ne_zeroOnes_of_lt
    (k m : Nat) (agent : Agent) (hk : 1 <= k) (hkm : k < m) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Nat Agent)
      (Pattern.zeroOnes k hk) (Pattern.zeroOnes m (by omega))) :=
  s5_zeroOnes_ne_zeroOnes_of_lt k m agent ExistenceZeroOne.Tag.toNat
    ExistenceZeroOne.Tag.toNat_injective hk hkm

theorem s5_zeroOnes_nat_ne_zeroOnesInf
    (k : Nat) (agent : Agent) (hk : 1 <= k) :
    Not (Sigma.ValEq (Classes.S5 : FrameClass.{u} Nat Agent)
      (Pattern.zeroOnes k hk) Pattern.zeroOnesInf) :=
  s5_zeroOnes_ne_zeroOnesInf k agent ExistenceZeroOne.Tag.toNat
    ExistenceZeroOne.Tag.toNat_injective hk


end ClassificationDisjointness

end ClassificationSigmaValidity
