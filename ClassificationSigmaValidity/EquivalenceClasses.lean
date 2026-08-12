import ClassificationSigmaValidity.NonexistenceK45S5
import ClassificationSigmaValidity.SingleAgentKD45
import ClassificationSigmaValidity.PatternLemmas

/-!
# Equivalence-class collapse theorems

These are the `Val(sigma) = Val(tau)` forms of the collapse lemmas used in the
classification theorem.
-/

namespace ClassificationSigmaValidity

universe u v w

namespace Pattern

theorem zeroZero_prefix_zerosInf : zeroZero.IsPrefix zerosInf := by
  intro n hn
  have hn' : n = 0 ∨ n = 1 := by
    have : n < 2 := by simpa [zeroZero, bits2] using hn
    omega
  rcases hn' with rfl | rfl <;> rfl

theorem oneOne_prefix_onesInf : oneOne.IsPrefix onesInf := by
  intro n hn
  have hn' : n = 0 ∨ n = 1 := by
    have : n < 2 := by simpa [oneOne, bits2] using hn
    omega
  rcases hn' with rfl | rfl <;> rfl

theorem oneZero_prefix_oneZerosInf : oneZero.IsPrefix oneZerosInf := by
  intro n hn
  have hn' : n = 0 ∨ n = 1 := by
    have : n < 2 := by simpa [oneZero, bits2] using hn
    omega
  rcases hn' with rfl | rfl <;> rfl

theorem oneZeroZero_prefix_oneZerosInf :
    (bits3 true false false).IsPrefix oneZerosInf := by
  intro n hn
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by
    have : n < 3 := by simpa [bits3] using hn
    omega
  rcases hn' with rfl | rfl | rfl <;> rfl

theorem oneZeroOne_prefix_oneZeroOnesInf :
    (bits3 true false true).IsPrefix oneZeroOnesInf := by
  intro n hn
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by
    have : n < 3 := by simpa [bits3] using hn
    omega
  rcases hn' with rfl | rfl | rfl <;> rfl

theorem zeros_two_prefix_zeros (n : Nat) (hn : 2 <= n) :
    zeroZero.IsPrefix (zeros n hn) := by
  apply List.prefix_iff_eq_take.mpr
  simp [min_eq_left hn]

theorem oneOne_prefix_ones (n : Nat) (hn : 2 <= n) :
    oneOne.IsPrefix (ones n hn) := by
  apply List.prefix_iff_eq_take.mpr
  simp [min_eq_left hn]

theorem oneZeroZero_prefix_oneZeros (k : Nat) (hk : 2 <= k) :
    (bits3 true false false).IsPrefix (oneZeros k (by omega)) := by
  apply List.prefix_iff_eq_take.mpr
  rcases k with _ | _ | k
  · omega
  · omega
  · simp

theorem oneZeroOne_prefix_oneZeroOnes (k : Nat) :
    (bits3 true false true).IsPrefix
      (.finite (true :: false :: List.replicate (k + 1) true) (by simp)) := by
  apply List.prefix_iff_eq_take.mpr
  simp

theorem zeros_prefix_zerosInf (n : Nat) (hn : 2 <= n) :
    (zeros n hn).IsPrefix zerosInf := by
  intro j hj
  simp

theorem ones_prefix_onesInf (n : Nat) (hn : 2 <= n) :
    (ones n hn).IsPrefix onesInf := by
  intro j hj
  simp

theorem oneZeros_prefix_oneZerosInf (k : Nat) (hk : 1 <= k) :
    (oneZeros k hk).IsPrefix oneZerosInf := by
  intro j hj
  cases j with
  | zero => rfl
  | succ j => simp

end Pattern

namespace EquivalenceClasses

open Pattern Sigma

variable {Atom : Type v} {Agent : Type w}

/-- Paper Lemma `00-validity_collapse`, expressed as equality of validity
classes over K45. -/
theorem k45_zeroZero_valEq_zerosInf :
    Sigma.ValEq (Classes.K45 : FrameClass.{u} Atom Agent)
      Pattern.zeroZero Pattern.zerosInf := by
  intro phi
  constructor
  · exact Collapse.k45_valid_zeroZero_implies_zerosInf phi
  · exact Sigma.valid_of_prefix _ phi Pattern.zeroZero_prefix_zerosInf

/-- The single-agent KD45 half of the same collapse. -/
theorem single_kd45_zeroZero_valEq_zerosInf :
    Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Unit)
      Pattern.zeroZero Pattern.zerosInf := by
  intro phi
  constructor
  · exact Collapse.singleAgentKD45_valid_zeroZero_implies_zerosInf phi
  · exact Sigma.valid_of_prefix _ phi Pattern.zeroZero_prefix_zerosInf

/-- Paper Lemma `11-validity_collapse` as a `ValEq`, for an arbitrary frame
class. -/
theorem oneOne_valEq_onesInf (C : FrameClass.{u} Atom Agent) :
    Sigma.ValEq C Pattern.oneOne Pattern.onesInf := by
  intro phi
  constructor
  · exact Collapse.valid_oneOne_implies_onesInf C phi
  · exact Sigma.valid_of_prefix C phi Pattern.oneOne_prefix_onesInf

/-- Paper Lemma `101-validity_collapse` as a `ValEq`. -/
theorem oneZeroOne_valEq_oneZeroOnesInf (C : FrameClass.{u} Atom Agent) :
    Sigma.ValEq C (Pattern.bits3 true false true) Pattern.oneZeroOnesInf := by
  intro phi
  constructor
  · exact Collapse.valid_oneZeroOne_implies_oneZeroOnesInf C phi
  · exact Sigma.valid_of_prefix C phi Pattern.oneZeroOne_prefix_oneZeroOnesInf

/-- The `k >= 2` portion of the `10^k` collapse. -/
theorem oneZeroZero_valEq_oneZerosInf (C : FrameClass.{u} Atom Agent) :
    Sigma.ValEq C (Pattern.bits3 true false false) Pattern.oneZerosInf := by
  intro phi
  constructor
  · exact Collapse.valid_oneZeroZero_implies_oneZerosInf C phi
  · exact Sigma.valid_of_prefix C phi Pattern.oneZeroZero_prefix_oneZerosInf

/-- In K45, already `10` determines the permanent-zero tail. -/
theorem k45_oneZero_valEq_oneZerosInf :
    Sigma.ValEq (Classes.K45 : FrameClass.{u} Atom Agent)
      Pattern.oneZero Pattern.oneZerosInf := by
  intro phi
  constructor
  · exact Collapse.k45_valid_oneZero_implies_oneZerosInf phi
  · exact Sigma.valid_of_prefix _ phi Pattern.oneZero_prefix_oneZerosInf

/-- Every finite all-zero pattern collapses to `0^omega` over K45. -/
theorem k45_zeros_valEq_zerosInf (n : Nat) (hn : 2 <= n) :
    Sigma.ValEq (Classes.K45 : FrameClass.{u} Atom Agent)
      (Pattern.zeros n hn) Pattern.zerosInf := by
  intro phi
  constructor
  · intro h
    exact Collapse.k45_valid_zeroZero_implies_zerosInf phi
      (Sigma.valid_of_prefix _ phi (Pattern.zeros_two_prefix_zeros n hn) h)
  · exact Sigma.valid_of_prefix _ phi (Pattern.zeros_prefix_zerosInf n hn)

/-- Every finite all-zero pattern collapses to `0^omega` in single-agent
KD45. -/
theorem single_kd45_zeros_valEq_zerosInf (n : Nat) (hn : 2 <= n) :
    Sigma.ValEq (Classes.KD45 : FrameClass.{u} Atom Unit)
      (Pattern.zeros n hn) Pattern.zerosInf := by
  intro phi
  constructor
  · intro h
    exact Collapse.singleAgentKD45_valid_zeroZero_implies_zerosInf phi
      (Sigma.valid_of_prefix _ phi (Pattern.zeros_two_prefix_zeros n hn) h)
  · exact Sigma.valid_of_prefix _ phi (Pattern.zeros_prefix_zerosInf n hn)

/-- Every finite all-one pattern collapses to `1^omega` over any class. -/
theorem ones_valEq_onesInf (C : FrameClass.{u} Atom Agent)
    (n : Nat) (hn : 2 <= n) :
    Sigma.ValEq C (Pattern.ones n hn) Pattern.onesInf := by
  intro phi
  constructor
  · intro h
    exact Collapse.valid_oneOne_implies_onesInf C phi
      (Sigma.valid_of_prefix C phi (Pattern.oneOne_prefix_ones n hn) h)
  · exact Sigma.valid_of_prefix C phi (Pattern.ones_prefix_onesInf n hn)

/-- Every finite `10^k`, `k >= 2`, lies in the permanent-zero class. -/
theorem oneZeros_valEq_oneZerosInf (C : FrameClass.{u} Atom Agent)
    (k : Nat) (hk : 2 <= k) :
    Sigma.ValEq C (Pattern.oneZeros k (by omega)) Pattern.oneZerosInf := by
  intro phi
  constructor
  · intro h
    exact Collapse.valid_oneZeroZero_implies_oneZerosInf C phi
      (Sigma.valid_of_prefix C phi
        (Pattern.oneZeroZero_prefix_oneZeros k hk) h)
  · exact Sigma.valid_of_prefix C phi
      (Pattern.oneZeros_prefix_oneZerosInf k (by omega))

end EquivalenceClasses

end ClassificationSigmaValidity
