import EventualAndStrongEventualNotionsInPublicAnnouncements.Definitions
import EventualAndStrongEventualNotionsInPublicAnnouncements.FiniteConditions

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

theorem common_target {M : Model World Atom Agent} {x y z : World}
    {φ : Formula Atom Agent} (h : Common M x φ) (hy : M.Reachable x y)
    {a : Agent} (hyz : M.rel a y z) : M.Satisfies z φ :=
  h z (Relation.TransGen.tail' hy ⟨a, hyz⟩)

theorem common_locallyAgrees {M : Model World Atom Agent} {x : World}
    {φ : Formula Atom Agent} (h : Common M x φ) :
    M.LocallyAgrees (M.update φ) (M.generatedSet x) := by
  constructor
  · intro p y hy
    rfl
  · intro a y hy z hz
    exact ⟨fun hyz => ⟨hyz, common_target h hy hyz⟩, fun hyz => hyz.1⟩

theorem generatedUnchanged_iff_common (M : Model World Atom Agent)
    (x : World) (φ : Formula Atom Agent) :
    GeneratedUnchanged M x φ ↔ Common M x φ := by
  constructor
  · rintro ⟨_, hagree⟩ y hy
    obtain ⟨z, hz, a, hzy⟩ := Relation.TransGen.tail'_iff.mp hy
    have hy' : M.Reachable x y := hy.to_reflTransGen
    exact ((hagree.2 a z hz y hy').mp hzy).2
  · intro h
    refine ⟨?_, common_locallyAgrees h⟩
    ext y
    change (M.update φ).Reachable x y ↔ M.Reachable x y
    constructor
    · exact Relation.ReflTransGen.mono (fun _ _ ⟨a, ha⟩ => ⟨a, ha.1⟩)
    · intro hy
      induction hy with
      | refl => exact Relation.ReflTransGen.refl
      | @tail z y hz hzy ih =>
          obtain ⟨a, ha⟩ := hzy
          exact Relation.ReflTransGen.tail ih ⟨a, ha, common_target h hz ha⟩

theorem common_generated_fixed {M : Model World Atom Agent} {x : World}
    {φ : Formula Atom Agent} (h : Common M x φ) :
    (M.generatedSubmodel x).update φ = M.generatedSubmodel x := by
  have heq := Model.restrict_eq_of_locallyAgrees (common_locallyAgrees h)
  rw [M.restrict_update_eq _ (M.generatedSet_forwardClosed x) φ] at heq
  exact heq.symm

/-- Common belief makes every formula at the point permanent under finite
repetition of the announcement, without any frame assumptions. -/
theorem common_finite_permanent {M : Model World Atom Agent} {x : World}
    {φ : Formula Atom Agent} (h : Common M x φ) (n : Nat)
    (ψ : Formula Atom Agent) :
    (M.iterateUpdate φ n).Satisfies x ψ ↔ M.Satisfies x ψ := by
  have hfixed := common_generated_fixed h
  have hn : (M.generatedSubmodel x).iterateUpdate φ n = M.generatedSubmodel x := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Model.iterateUpdate_succ, ih, hfixed]
  have hU : M.ForwardClosed (M.generatedSet x) := M.generatedSet_forwardClosed x
  have ht := (M.iterateUpdate φ n).restrict_satisfies_iff
    (M.generatedSet x) (Model.forwardClosed_iterateUpdate hU φ n)
    (M.generatedPoint x) ψ
  rw [M.restrict_iterateUpdate_eq _ hU φ n] at ht
  change ((M.generatedSubmodel x).iterateUpdate φ n).Satisfies (M.generatedPoint x) ψ ↔ _ at ht
  rw [hn] at ht
  exact ht.symm.trans (M.generatedSubmodel_root_satisfies_iff x ψ)

theorem common_at_fixed {M : Model World Atom Agent} {φ : Formula Atom Agent}
    (h : M.update φ = M) (x : World) : Common M x φ := by
  intro y hy
  obtain ⟨z, _, a, hzy⟩ := Relation.TransGen.tail'_iff.mp hy
  have hz : (M.update φ).rel a z y := by rw [h]; exact hzy
  exact hz.2

/-- Lemma 4(2): eventuality implies the common-belief test at every finite stage. -/
theorem eventual_implies_finiteStageCondition {i j : Bool} {φ : Formula Atom Agent}
    (h : Eventual.{u} i j φ) : FiniteStageCondition.{u} i j φ := by
  intro k W M hM x hx hC
  apply eventual_value_at_stable_stage h M hM x hx k
  intro n hkn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [Model.trace, M.iterateUpdate_add φ k d]
  exact common_finite_permanent hC d φ

/-- Always informativeness is exactly the common-belief implication. -/
theorem alwaysInformative_iff (i : Bool) (φ : Formula Atom Agent) :
    AlwaysInformative.{u} i φ ↔
      ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
        Common M x φ → HoldsBit (!i) (M.Satisfies x φ) := by
  classical
  simp only [AlwaysInformative, generatedUnchanged_iff_common]
  cases i <;> simp only [HoldsBit, Pattern.HoldsBit, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte] <;> constructor
  · intro h W M hM x hC
    by_contra hn
    exact h M hM x hn hC
  · intro h W M hM x hn hC
    exact hn (h M hM x hC)
  · intro h W M hM x hC ht
    exact h M hM x ht hC
  · intro h W M hM x ht hC
    exact h M hM x hC ht

theorem finiteStageCondition_reversal_iff (i : Bool) (φ : Formula Atom Agent) :
    FiniteStageCondition.{u} i (!i) φ ↔
      ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
        Common M x φ → HoldsBit (!i) (M.Satisfies x φ) := by
  classical
  constructor
  · intro h W M hM x hC
    have hzero := h 0 M hM x
    cases i <;> simp only [HoldsBit, Pattern.HoldsBit, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte] at *
    · by_contra hn
      exact hn (hzero hn hC)
    · intro ht
      exact hzero ht hC ht
  · intro h k W M hM x _ hC
    exact h (M.iterateUpdate φ k) (Model.iterateUpdate_isK45 hM φ k) x hC

theorem alwaysInformative_iff_finiteStageCondition (i : Bool) (φ : Formula Atom Agent) :
    AlwaysInformative.{u} i φ ↔ FiniteStageCondition.{u} i (!i) φ :=
  (alwaysInformative_iff i φ).trans (finiteStageCondition_reversal_iff i φ).symm

/-- No formula is always informative for both initial truth values in K45. -/
theorem not_alwaysInformative_both (φ : Formula Atom Agent) :
    ¬ (AlwaysInformative.{u} true φ ∧ AlwaysInformative.{u} false φ) := by
  rintro ⟨h₁, h₀⟩
  let M : Model (ULift.{u} Unit) Atom Agent :=
    ⟨fun _ _ _ => False, fun _ _ => False⟩
  have hM : IsK45 M := fun _ => ⟨fun h => h.elim, fun h => h.elim⟩
  have hfixed : M.update φ = M := by
    apply Model.ext'
    · intro a x y
      simp [M, Model.update_rel]
    · intro p x
      rfl
  have hC := common_at_fixed hfixed (ULift.up ())
  exact (alwaysInformative_iff true φ).mp h₁ M hM (ULift.up ()) hC
    ((alwaysInformative_iff false φ).mp h₀ M hM (ULift.up ()) hC)

end EventualAndStrongEventualNotionsInPublicAnnouncements
