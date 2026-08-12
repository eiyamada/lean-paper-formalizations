import ClassificationSigmaValidity.ExistenceKD45Zero
import ClassificationSigmaValidity.ExistenceS5Zero
import ClassificationSigmaValidity.ExistenceZeroOne
import ClassificationSigmaValidity.Examples
import ClassificationSigmaValidity.EquivalenceClasses

/-!
# Well-definedness of every displayed representative class

These theorems collect the witness side of the paper's classification theorem.
The proposition-letter type is specialized to `Nat`, matching the paper's
countably infinite supply of fresh letters.  Agent hypotheses are exactly the
ones used by the formulas: nonempty for modal witnesses, and two distinct
agents for the multi-agent KD45 all-zero hierarchy.
-/

namespace ClassificationSigmaValidity

universe u w

namespace WellDefinedness

open Pattern Sigma

variable {Agent : Type w}

theorem k45_zerosInf :
    Sigma.Admissible (Classes.K45 : FrameClass.{u} Nat Agent)
      Pattern.zerosInf :=
  ⟨Formula.falsum, Examples.falsum_nontriviallyValid_zerosInf_k45⟩

theorem kd45_zerosInf :
    Sigma.Admissible (Classes.KD45 : FrameClass.{u} Nat Agent)
      Pattern.zerosInf :=
  ⟨Formula.falsum, Examples.falsum_nontriviallyValid_zerosInf_kd45⟩

theorem s5_zerosInf :
    Sigma.Admissible (Classes.S5 : FrameClass.{u} Nat Agent)
      Pattern.zerosInf :=
  ⟨Formula.falsum, Examples.falsum_nontriviallyValid_zerosInf_s5⟩

theorem k45_onesInf :
    Sigma.Admissible (Classes.K45 : FrameClass.{u} Nat Agent)
      Pattern.onesInf :=
  ⟨Formula.verum, Examples.verum_nontriviallyValid_onesInf_k45⟩

theorem kd45_onesInf :
    Sigma.Admissible (Classes.KD45 : FrameClass.{u} Nat Agent)
      Pattern.onesInf :=
  ⟨Formula.verum, Examples.verum_nontriviallyValid_onesInf_kd45⟩

theorem s5_onesInf :
    Sigma.Admissible (Classes.S5 : FrameClass.{u} Nat Agent)
      Pattern.onesInf :=
  ⟨Formula.verum, Examples.verum_nontriviallyValid_onesInf_s5⟩

theorem k45_oneZerosInf (i : Agent) :
    Sigma.Admissible (Classes.K45 : FrameClass.{u} Nat Agent)
      Pattern.oneZerosInf :=
  ⟨Examples.moore 0 i, Examples.moore_nontriviallyValid_oneZerosInf 0 i⟩

theorem k45_zeroOnesInf (i : Agent) :
    Sigma.Admissible (Classes.K45 : FrameClass.{u} Nat Agent)
      Pattern.zeroOnesInf :=
  ⟨Examples.pOrBox 0 i, Examples.pOrBox_nontriviallyValid_zeroOnesInf 0 i⟩

theorem kd45_oneZeroOnesInf (i : Agent) :
    Sigma.Admissible (Classes.KD45 : FrameClass.{u} Nat Agent)
      Pattern.oneZeroOnesInf :=
  ⟨Examples.oneZeroOneFormula 0 i,
    Examples.oneZeroOne_nontriviallyValid_oneZeroOnesInf 0 i⟩

theorem kd45_oneZero (i : Agent) :
    Sigma.Admissible (Classes.KD45 : FrameClass.{u} Nat Agent)
      Pattern.oneZero := by
  refine ⟨Examples.moore 0 i, ?_⟩
  constructor
  · exact Sigma.valid_mono_class
      (fun {World} (M : Model World Nat Agent) (hM : IsKD45 M) => hM.isK45)
      (Examples.moore_valid_oneZero 0 i)
  · let M : Model (ULift.{u} Bool) Nat Agent := Examples.twoWorldModel 0
    refine ⟨ULift.{u} Bool, M, (Examples.twoWorldModel_isS5 0).isKD45,
      ⟨true⟩, ?_⟩
    have h0 := Examples.twoWorldModel_moore_initial (Agent := Agent) 0 i
    have h1 := Examples.moore_selfRefuting 0 i M
      (Examples.twoWorldModel_isS5 0).isK45 ⟨true⟩ h0
    apply (Pattern.realizesTrace_bits2).mpr
    exact ⟨by simpa [Pattern.HoldsBit, Model.trace] using h0,
      by simpa [Pattern.HoldsBit, Model.trace] using h1⟩

theorem kd45_oneZerosInf (i : Agent) :
    Sigma.Admissible (Classes.KD45 : FrameClass.{u} Nat Agent)
      Pattern.oneZerosInf := by
  refine ⟨Examples.moore 0 i, ?_⟩
  constructor
  · exact Sigma.valid_mono_class
      (fun {World} (M : Model World Nat Agent) (hM : IsKD45 M) => hM.isK45)
      (Examples.moore_valid_oneZerosInf 0 i)
  · let M : Model (ULift.{u} Bool) Nat Agent := Examples.twoWorldModel 0
    refine ⟨ULift.{u} Bool, M, (Examples.twoWorldModel_isS5 0).isKD45,
      ⟨true⟩, ?_⟩
    have h0 := Examples.twoWorldModel_moore_initial (Agent := Agent) 0 i
    exact Examples.moore_valid_oneZerosInf 0 i M
      (Examples.twoWorldModel_isS5 0).isK45 ⟨true⟩ (by simpa using h0)

theorem s5_oneZero (i : Agent) :
    Sigma.Admissible (Classes.S5 : FrameClass.{u} Nat Agent)
      Pattern.oneZero := by
  refine ⟨Examples.moore 0 i, ?_⟩
  constructor
  · exact Sigma.valid_mono_class
      (fun {World} (M : Model World Nat Agent) (hM : IsS5 M) => hM.isK45)
      (Examples.moore_valid_oneZero 0 i)
  · let M : Model (ULift.{u} Bool) Nat Agent := Examples.twoWorldModel 0
    refine ⟨ULift.{u} Bool, M, Examples.twoWorldModel_isS5 0,
      ⟨true⟩, ?_⟩
    have h0 := Examples.twoWorldModel_moore_initial (Agent := Agent) 0 i
    have h1 := Examples.moore_selfRefuting 0 i M
      (Examples.twoWorldModel_isS5 0).isK45 ⟨true⟩ h0
    exact (Pattern.realizesTrace_bits2.mpr ⟨by simpa [Model.trace] using h0,
      by simpa [Pattern.HoldsBit, Model.trace] using h1⟩)

theorem s5_oneZerosInf (i : Agent) :
    Sigma.Admissible (Classes.S5 : FrameClass.{u} Nat Agent)
      Pattern.oneZerosInf := by
  refine ⟨Examples.moore 0 i, ?_⟩
  constructor
  · exact Sigma.valid_mono_class
      (fun {World} (M : Model World Nat Agent) (hM : IsS5 M) => hM.isK45)
      (Examples.moore_valid_oneZerosInf 0 i)
  · let M : Model (ULift.{u} Bool) Nat Agent := Examples.twoWorldModel 0
    refine ⟨ULift.{u} Bool, M, Examples.twoWorldModel_isS5 0,
      ⟨true⟩, ?_⟩
    have h0 := Examples.twoWorldModel_moore_initial (Agent := Agent) 0 i
    exact Examples.moore_valid_oneZerosInf 0 i M
      (Examples.twoWorldModel_isS5 0).isK45 ⟨true⟩ (by simpa using h0)

theorem s5_oneZeroOnesInf (i : Agent) :
    Sigma.Admissible (Classes.S5 : FrameClass.{u} Nat Agent)
      Pattern.oneZeroOnesInf := by
  refine ⟨Examples.oneZeroOneFormula 0 i, ?_⟩
  constructor
  · exact Sigma.valid_mono_class
      (fun {World} (M : Model World Nat Agent) (hM : IsS5 M) => hM.isKD45)
      (Examples.oneZeroOne_valid_oneZeroOnesInf 0 i)
  · let M : Model (ULift.{u} (Fin 3)) Nat Agent := Examples.threeWorldModel 0
    have hM : IsS5 M := Examples.threeWorldModel_isS5 0
    have h0 := Examples.threeWorldModel_oneZeroOne_initial (Agent := Agent) 0 i
    refine ⟨ULift.{u} (Fin 3), M, hM, ⟨0⟩, ?_⟩
    exact Examples.oneZeroOne_valid_oneZeroOnesInf 0 i M hM.isKD45 ⟨0⟩
      (by simpa using h0)

/-- Every finite `01^k` representative is admissible in K45. -/
theorem k45_zeroOnes (i : Agent) (k : Nat) (hk : 1 <= k) :
    Sigma.Admissible (Classes.K45 : FrameClass.{u} Nat Agent)
      (Pattern.zeroOnes k hk) :=
  ⟨ExistenceZeroOne.witness k i ExistenceZeroOne.Tag.toNat,
    ExistenceZeroOne.witness_nontriviallyValid_zeroOnes_k45
      k hk i ExistenceZeroOne.Tag.toNat
      ExistenceZeroOne.Tag.toNat_injective⟩

theorem kd45_zeroOnes (i : Agent) (k : Nat) (hk : 1 <= k) :
    Sigma.Admissible (Classes.KD45 : FrameClass.{u} Nat Agent)
      (Pattern.zeroOnes k hk) := by
  refine ⟨ExistenceZeroOne.witness k i ExistenceZeroOne.Tag.toNat, ?_⟩
  have hk45 : Sigma.NontriviallyValid
      (Classes.K45 : FrameClass.{u} Nat Agent)
      (ExistenceZeroOne.witness k i ExistenceZeroOne.Tag.toNat)
      (Pattern.zeroOnes k hk) :=
    ExistenceZeroOne.witness_nontriviallyValid_zeroOnes_k45
      k hk i ExistenceZeroOne.Tag.toNat
    ExistenceZeroOne.Tag.toNat_injective
  have hs5 : Sigma.Satisfiable (Classes.S5 : FrameClass.{u} Nat Agent)
      (ExistenceZeroOne.witness k i ExistenceZeroOne.Tag.toNat)
      (Pattern.zeroOnes k hk) :=
    ExistenceZeroOne.witness_satisfiable_zeroOnes_s5 k hk i
      ExistenceZeroOne.Tag.toNat ExistenceZeroOne.Tag.toNat_injective
  exact ⟨Sigma.valid_mono_class
      (fun {World} (M : Model World Nat Agent) (hM : IsKD45 M) => hM.isK45)
      hk45.1,
    Sigma.satisfiable_mono_class
      (fun {World} (M : Model World Nat Agent) (hM : IsS5 M) => hM.isKD45) hs5⟩

theorem s5_zeroOnes (i : Agent) (k : Nat) (hk : 1 <= k) :
    Sigma.Admissible (Classes.S5 : FrameClass.{u} Nat Agent)
      (Pattern.zeroOnes k hk) := by
  refine ⟨ExistenceZeroOne.witness k i ExistenceZeroOne.Tag.toNat, ?_⟩
  have hvalid : Sigma.Valid (Classes.K45 : FrameClass.{u} Nat Agent)
      (ExistenceZeroOne.witness k i ExistenceZeroOne.Tag.toNat)
      (Pattern.zeroOnes k hk) :=
    ExistenceZeroOne.witness_valid_zeroOnes k hk i ExistenceZeroOne.Tag.toNat
  exact ⟨Sigma.valid_mono_class
      (fun {World} (M : Model World Nat Agent) (hM : IsS5 M) => hM.isK45)
      hvalid,
    ExistenceZeroOne.witness_satisfiable_zeroOnes_s5 k hk i
      ExistenceZeroOne.Tag.toNat ExistenceZeroOne.Tag.toNat_injective⟩

theorem s5_zeros (i : Agent) (k : Nat) (hk : 2 <= k) :
    Sigma.Admissible (Classes.S5 : FrameClass.{u} Nat Agent)
      (Pattern.zeros k hk) :=
  ⟨S5ZeroWitness.formula i k, S5ZeroWitness.nontriviallyValid_zeros i k hk⟩

theorem kd45_zeros (a b : Agent) (hab : Not (a = b))
    (k : Nat) (hk : 2 <= k) :
    Sigma.Admissible (Classes.KD45 : FrameClass.{u} Nat Agent)
      (Pattern.zeros k hk) := by
  have hex : ∃ phi : Formula Nat Agent,
      Sigma.NontriviallyValid
        (Classes.KD45 : FrameClass.{u} Nat Agent) phi (Pattern.zeros k hk) ∧
      ¬Sigma.Valid (Classes.KD45 : FrameClass.{u} Nat Agent) phi
        (Pattern.zeros (k + 1) (by omega)) :=
    KD45Zero.exists_nontriviallyValid_zeros_not_succ a b hab k hk
  rcases hex with ⟨phi, hphi, _⟩
  exact ⟨phi, hphi⟩

end WellDefinedness

end ClassificationSigmaValidity
