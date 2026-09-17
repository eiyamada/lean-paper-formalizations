import EventualAndStrongEventualNotionsInPublicAnnouncements.RichOrdinalDynamics
import EventualAndStrongEventualNotionsInPublicAnnouncements.RichFiniteConditions

/-!
# Ordinal eventuality and common-belief conditions in BPALC

The global ordinal notions quantify over every K45 model and every ordinal
stage in a universe large enough for its set of labelled arrows. This file
formalizes Lemma `lem:ordinal-eventual-facts`.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements
namespace Rich

open ClassificationSigmaValidity
open Order

universe u v w
variable {Atom : Type v} {Agent : Type w}
variable {φ : BPALCFormula Atom Agent} {i j : Bool}

/-- Some positive ordinal repetition attains the required truth value. -/
def OrdinalEventual (i j : Bool) (φ : BPALCFormula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (M.rSatisfies x φ) →
      ∃ α : Ordinal.{max u w}, 0 < α ∧
        HoldsBit j ((ordinalUpdate M φ α).rSatisfies x φ)

/-- The required truth value persists from some positive ordinal onward. -/
def OrdinalStrongEventual (i j : Bool) (φ : BPALCFormula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (M.rSatisfies x φ) →
      ∃ α : Ordinal.{max u w}, 0 < α ∧ ∀ β, α ≤ β →
        HoldsBit j ((ordinalUpdate M φ β).rSatisfies x φ)

/-- The S condition at every ordinal stage. -/
def OrdinalStageCondition (i j : Bool) (φ : BPALCFormula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (M.rSatisfies x φ) → ∀ α : Ordinal.{max u w},
      Common (ordinalUpdate M φ α) x φ →
        HoldsBit j ((ordinalUpdate M φ α).rSatisfies x φ)

theorem ordinalStrongEventual_implies_ordinalEventual
    (h : OrdinalStrongEventual.{u} i j φ) : OrdinalEventual.{u} i j φ := by
  intro World M hM x hx
  obtain ⟨α, hα, htail⟩ := h M hM x hx
  exact ⟨α, hα, htail α le_rfl⟩

theorem eventual_implies_ordinalEventual (h : Eventual.{u} i j φ) :
    OrdinalEventual.{u} i j φ := by
  intro World M hM x hx
  obtain ⟨n, hn, hv⟩ := h M hM x hx
  refine ⟨n, ?_, ?_⟩
  · exact_mod_cast (show 0 < n by omega)
  · simpa only [ordinalUpdate_natCast] using hv

theorem ordinalStageCondition_implies_finiteStageCondition
    (h : OrdinalStageCondition.{u} i j φ) : FiniteStageCondition.{u} i j φ := by
  intro k World M hM x hx hC
  have hC' : Common (ordinalUpdate M φ (k : Ordinal.{max u w})) x φ := by
    simpa only [ordinalUpdate_natCast] using hC
  simpa only [ordinalUpdate_natCast] using h M hM x hx k hC'

/-- Common belief and eventual permanent truth are equivalent at ordinal scale. -/
theorem ordinalStageCondition_iff_ordinalStrongEventual :
    OrdinalStageCondition.{u} i j φ ↔ OrdinalStrongEventual.{u} i j φ := by
  constructor
  · intro h World M hM x hx
    obtain ⟨α, hstep, hcommon⟩ := ordinal_stabilization M φ
    have hv := h M hM x hx α (hcommon x)
    refine ⟨Order.succ α, Ordinal.succ_pos α, fun β hβ => ?_⟩
    rw [ordinalUpdate_eq_of_ge_of_step M φ hstep (le_trans (Order.le_succ α) hβ)]
    exact hv
  · intro h World M hM x hx α hC
    obtain ⟨β, _, htail⟩ := h M hM x hx
    exact (holdsBit_congr j (common_ordinal_stage_permanent M φ hC
      (le_max_left α β) φ)).mp (htail (max α β) (le_max_right α β))

/-- For truth-value reversals the finite-stage common-belief condition already
forces permanent truth at ordinal scale. -/
theorem finiteStageCondition_reversal_implies_ordinalStrongEventual
    (h : FiniteStageCondition.{u} i (!i) φ) :
    OrdinalStrongEventual.{u} i (!i) φ := by
  apply ordinalStageCondition_iff_ordinalStrongEventual.mp
  intro World M hM x _ α hC
  exact (finiteStageCondition_reversal_iff i φ).mp h
    (ordinalUpdate M φ α) (ordinalUpdate_isK45 M φ hM α) x hC

/-- Every ordinal below a natural-number ordinal is a natural-number ordinal. -/
theorem exists_natCast_of_lt_natCast {α : Ordinal.{u}} {k : Nat}
    (h : α < (k : Ordinal.{u})) : ∃ n : Nat, n < k ∧ α = n := by
  induction k with
  | zero => exact (not_lt_of_ge (Ordinal.zero_le α) h).elim
  | succ k ih =>
    rw [Ordinal.natCast_succ, Order.lt_succ_iff] at h
    rcases lt_or_eq_of_le h with hk | hk
    · obtain ⟨n, hn, rfl⟩ := ih hk
      exact ⟨n, by omega, rfl⟩
    · exact ⟨k, Nat.lt_succ_self k, hk⟩

/-- Return eventuality determines truth at every finite common-belief stage.
The induction restarts at a strictly positive finite witnessing stage whenever
the ordinal witness precedes the common-belief stage. -/
theorem ordinalEventual_same_implies_finiteStageCondition
    (h : OrdinalEventual.{u} i i φ) : FiniteStageCondition.{u} i i φ := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro World M hM x hx hC
    have hC' : Common (ordinalUpdate M φ (k : Ordinal.{max u w})) x φ := by
      simpa only [ordinalUpdate_natCast] using hC
    obtain ⟨α, hα, hv⟩ := h M hM x hx
    by_cases hkα : (k : Ordinal.{max u w}) ≤ α
    · have hval := (holdsBit_congr i
        (common_ordinal_stage_permanent M φ hC' hkα φ)).mp hv
      simpa only [ordinalUpdate_natCast] using hval
    · obtain ⟨n, hnk, rfl⟩ := exists_natCast_of_lt_natCast (lt_of_not_ge hkα)
      have hn : 0 < n := by exact_mod_cast hα
      have hnk' : k - n < k := by omega
      have hsum : n + (k - n) = k := by omega
      have hv' : HoldsBit i ((M.rIterateUpdate φ n).rSatisfies x φ) := by
        simpa only [ordinalUpdate_natCast] using hv
      have hCtail : Common ((M.rIterateUpdate φ n).rIterateUpdate φ (k - n)) x φ := by
        rw [← Model.rIterateUpdate_add, hsum]
        exact hC
      have htail := ih (k - n) hnk' (M.rIterateUpdate φ n)
        (M.rIterateUpdate_isK45 hM φ n) x hv' hCtail
      change HoldsBit i (((M.rIterateUpdate φ n).rIterateUpdate φ (k - n)).rSatisfies x φ)
        at htail
      rw [← Model.rIterateUpdate_add, hsum] at htail
      exact htail

/-- Reversal eventuality determines truth at every finite common-belief stage. -/
theorem ordinalEventual_reversal_implies_finiteStageCondition
    (h : OrdinalEventual.{u} i (!i) φ) : FiniteStageCondition.{u} i (!i) φ := by
  classical
  intro k World M hM x _ hC
  by_contra hv
  have hi : HoldsBit i ((M.rIterateUpdate φ k).rSatisfies x φ) := by
    simpa only [holdsBit_not_iff, not_not] using hv
  obtain ⟨α, _, hα⟩ := h (M.rIterateUpdate φ k)
    (M.rIterateUpdate_isK45 hM φ k) x hi
  have hval := (holdsBit_congr (!i) (common_ordinal_permanent hC α φ)).mp hα
  exact hv hval

/-- The implication from ordinal eventuality to all finite S conditions. -/
theorem ordinalEventual_implies_finiteStageCondition
    (h : OrdinalEventual.{u} i j φ) : FiniteStageCondition.{u} i j φ := by
  by_cases hij : j = i
  · subst j
    exact ordinalEventual_same_implies_finiteStageCondition h
  · have hj : j = !i := by cases i <;> cases j <;> simp_all
    subst j
    exact ordinalEventual_reversal_implies_finiteStageCondition h

/-- Lemma `lem:ordinal-eventual-facts`: all four ordinal and S notions coincide
for truth-value reversal. -/
theorem ordinal_reversal_equivalences :
    (OrdinalEventual.{u} i (!i) φ ↔ OrdinalStrongEventual.{u} i (!i) φ) ∧
    (OrdinalStrongEventual.{u} i (!i) φ ↔ OrdinalStageCondition.{u} i (!i) φ) ∧
    (OrdinalStageCondition.{u} i (!i) φ ↔ FiniteStageCondition.{u} i (!i) φ) := by
  refine ⟨⟨fun h => finiteStageCondition_reversal_implies_ordinalStrongEventual
    (ordinalEventual_implies_finiteStageCondition h),
    ordinalStrongEventual_implies_ordinalEventual⟩,
    ordinalStageCondition_iff_ordinalStrongEventual.symm, ?_⟩
  exact ⟨ordinalStageCondition_implies_finiteStageCondition,
    fun h => ordinalStageCondition_iff_ordinalStrongEventual.mpr
      (finiteStageCondition_reversal_implies_ordinalStrongEventual h)⟩

end Rich
end EventualAndStrongEventualNotionsInPublicAnnouncements
