import EventualAndStrongEventualNotionsInPublicAnnouncements.FiniteConditions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.NormNum

/-! Real-valued limits, limsup and liminf of the manuscript's binary traces. -/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open Filter
open scoped Topology

noncomputable section

def realTrace (t : Nat → Prop) (n : Nat) : ℝ := by
  classical
  exact if t n then 1 else 0

theorem realTrace_bounds (t : Nat → Prop) (n : Nat) :
    0 ≤ realTrace t n ∧ realTrace t n ≤ 1 := by
  classical
  by_cases h : t n <;> simp [realTrace, h]

theorem realTrace_bddAbove (t : Nat → Prop) :
    IsBoundedUnder (· ≤ ·) atTop (realTrace t) :=
  isBoundedUnder_of ⟨1, fun n => (realTrace_bounds t n).2⟩

theorem realTrace_bddBelow (t : Nat → Prop) :
    IsBoundedUnder (· ≥ ·) atTop (realTrace t) :=
  isBoundedUnder_of ⟨0, fun n => (realTrace_bounds t n).1⟩

theorem convergesTo_iff_real_limit (b : Bool) (t : Nat → Prop) :
    ConvergesTo b t ↔ Tendsto (realTrace t) atTop (𝓝 (if b then 1 else 0)) := by
  classical
  constructor
  · rintro ⟨N, hN⟩
    apply tendsto_nhds_of_eventually_eq
    rw [eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    cases b <;> simp only [HoldsBit, ClassificationSigmaValidity.Pattern.HoldsBit,
      Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> simp [realTrace, h]
  · intro h
    cases b
    · have he := h.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
      rw [eventually_atTop] at he
      obtain ⟨N, hN⟩ := he
      refine ⟨N, fun n hn => ?_⟩
      change ¬ t n
      intro ht
      have := hN n hn
      norm_num [realTrace, ht] at this
    · have he := h.eventually_const_lt (by norm_num : (1 : ℝ) / 2 < 1)
      rw [eventually_atTop] at he
      obtain ⟨N, hN⟩ := he
      refine ⟨N, fun n hn => ?_⟩
      change t n
      by_contra ht
      have := hN n hn
      norm_num [realTrace, ht] at this

theorem cofinal_true_iff_real_limsup (t : Nat → Prop) :
    CofinalValue true t ↔ limsup (realTrace t) atTop = 1 := by
  classical
  constructor
  · intro h
    apply le_antisymm
    · exact limsup_le_of_le (realTrace_bddBelow t).isCoboundedUnder_le
        (Eventually.of_forall fun n => (realTrace_bounds t n).2)
    · apply le_limsup_of_frequently_le _ (realTrace_bddAbove t)
      rw [frequently_atTop]
      intro N
      obtain ⟨n, hn, ht⟩ := h N
      refine ⟨n, hn, ?_⟩
      change t n at ht
      simp [realTrace, ht]
  · intro h
    have hf : ∃ᶠ n in atTop, (1 : ℝ) / 2 < realTrace t n :=
      frequently_lt_of_lt_limsup (realTrace_bddBelow t).isCoboundedUnder_le
        (by rw [h]; norm_num)
    rw [frequently_atTop] at hf
    intro N
    obtain ⟨n, hn, ht⟩ := hf N
    refine ⟨n, hn, ?_⟩
    change t n
    by_contra hh
    norm_num [realTrace, hh] at ht

theorem cofinal_false_iff_real_liminf (t : Nat → Prop) :
    CofinalValue false t ↔ liminf (realTrace t) atTop = 0 := by
  classical
  constructor
  · intro h
    apply le_antisymm
    · apply liminf_le_of_frequently_le _ (realTrace_bddBelow t)
      rw [frequently_atTop]
      intro N
      obtain ⟨n, hn, ht⟩ := h N
      refine ⟨n, hn, ?_⟩
      change ¬ t n at ht
      simp [realTrace, ht]
    · exact le_liminf_of_le (realTrace_bddAbove t).isCoboundedUnder_ge
        (Eventually.of_forall fun n => (realTrace_bounds t n).1)
  · intro h
    have hf : ∃ᶠ n in atTop, realTrace t n < (1 : ℝ) / 2 :=
      frequently_lt_of_liminf_lt (realTrace_bddAbove t).isCoboundedUnder_ge
        (by rw [h]; norm_num)
    rw [frequently_atTop] at hf
    intro N
    obtain ⟨n, hn, ht⟩ := hf N
    refine ⟨n, hn, ?_⟩
    change ¬ t n
    intro hh
    norm_num [realTrace, hh] at ht

end

end EventualAndStrongEventualNotionsInPublicAnnouncements
