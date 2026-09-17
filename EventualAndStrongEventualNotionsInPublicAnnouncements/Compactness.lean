import EventualAndStrongEventualNotionsInPublicAnnouncements.Definitions
import EventualAndStrongEventualNotionsInPublicAnnouncements.FirstOrder
import ClassificationSigmaValidity.Reduction

/-!
# A uniform finite bound for eventual announcements

Lemma 4(3) of the manuscript follows from K45 compactness and reduction of
finite announcement sequences to modal formulas. Compactness is proved from
mathlib's first-order compactness theorem in `FirstOrder.lean`; it is not an
additional hypothesis. Atom and agent types, and the quantified models, live in
`Type`, which includes the manuscript's countable atoms and finite agent set.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity

variable {Atom Agent : Type}

/-- The modal formula saying that `φ` has the indicated Boolean truth value. -/
def signedFormula (b : Bool) (φ : Formula Atom Agent) : Formula Atom Agent :=
  if b then φ else .neg φ

@[simp] theorem satisfies_signedFormula {World : Type*} (M : Model World Atom Agent)
    (x : World) (b : Bool) (φ : Formula Atom Agent) :
    M.Satisfies x (signedFormula b φ) ↔ HoldsBit b (M.Satisfies x φ) := by
  cases b <;> simp [signedFormula, HoldsBit, Pattern.HoldsBit]

@[simp] theorem holdsBit_not (b : Bool) (P : Prop) :
    HoldsBit (!b) P ↔ ¬ HoldsBit b P := by
  cases b <;> simp [HoldsBit, Pattern.HoldsBit]

/-- Eventual truth-value change has a uniform finite bound over all K45 models. -/
theorem eventual_iff_uniformBound (i j : Bool) (φ : Formula Atom Agent) :
    Eventual.{0} i j φ ↔ UniformBound.{0} i j φ := by
  classical
  constructor
  · intro he
    by_contra hb
    have hc : ∀ N : Nat, 1 ≤ N →
        ∃ (World : Type) (M : Model World Atom Agent), IsK45 M ∧ ∃ x,
          HoldsBit i (M.Satisfies x φ) ∧
            ∀ n, 1 ≤ n → n ≤ N → ¬ HoldsBit j (M.trace x φ n) := by
      intro N hN
      have hn : ¬ (∀ {World : Type} (M : Model World Atom Agent),
          IsK45 M → ∀ x, HoldsBit i (M.Satisfies x φ) →
          ∃ n : Nat, 1 ≤ n ∧ n ≤ N ∧ HoldsBit j (M.trace x φ n)) := by
        intro hn
        exact hb ⟨N, hN, hn⟩
      push_neg at hn
      exact hn
    let ψ : Nat → Formula Atom Agent
      | 0 => signedFormula i φ
      | n + 1 => signedFormula (!j) (Formula.iteratedAnnouncementReduce φ (n + 1) φ)
    have hprefix : ∀ N : Nat, ∃ (World : Type) (M : Model World Atom Agent),
        IsK45 M ∧ ∃ x, ∀ n, n ≤ N → M.Satisfies x (ψ n) := by
      intro N
      obtain ⟨World, M, hM, x, hx, hnever⟩ := hc (N + 1) (by omega)
      refine ⟨World, M, hM, x, ?_⟩
      intro n hn
      cases n with
      | zero => exact (satisfies_signedFormula M x i φ).mpr hx
      | succ n =>
        change M.Satisfies x (signedFormula (!j)
          (Formula.iteratedAnnouncementReduce φ (n + 1) φ))
        rw [satisfies_signedFormula, holdsBit_not,
          ← M.trace_iff_satisfies_iteratedAnnouncementReduce x φ (n + 1)]
        exact hnever (n + 1) (by omega) (by omega)
    obtain ⟨World, M, hM, x, hx⟩ := FirstOrderEncoding.compactness_sequence ψ hprefix
    have hi : HoldsBit i (M.Satisfies x φ) :=
      (satisfies_signedFormula M x i φ).mp (hx 0)
    obtain ⟨n, hn, htarget⟩ := he M hM x hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hneg := hx (k + 1)
    change M.Satisfies x (signedFormula (!j)
      (Formula.iteratedAnnouncementReduce φ (k + 1) φ)) at hneg
    rw [satisfies_signedFormula, holdsBit_not,
      ← M.trace_iff_satisfies_iteratedAnnouncementReduce x φ (k + 1)] at hneg
    exact hneg htarget
  · rintro ⟨N, _, hN⟩ World M hM x hx
    obtain ⟨n, hn, _, hj⟩ := hN M hM x hx
    exact ⟨n, hn, hj⟩

end EventualAndStrongEventualNotionsInPublicAnnouncements
