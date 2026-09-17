import EventualAndStrongEventualNotionsInPublicAnnouncements.CommonBelief
import EventualAndStrongEventualNotionsInPublicAnnouncements.FiniteConditions

/-!
# True-preservation witnesses

The two formulas used in Lemma `lem:two-agent-11-limit-loss-separations`.
The membership proofs work for arbitrary choices of atoms and agents; distinct
choices are needed only for the countermodels proving nonmembership.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements
namespace TruePreservation

open ClassificationSigmaValidity

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

abbrev C (r t : Atom) : Formula Atom Agent := .conj (.neg (.atom r)) (.neg (.atom t))
abbrev P (r t : Atom) : Formula Atom Agent := .conj (.neg (.atom r)) (.atom t)
def D (r s t : Atom) (a b : Agent) : Formula Atom Agent :=
  Formula.or (.conj (.atom s) (Formula.dia a (.conj (C r t) (.neg (.atom s)))))
    (.conj (.neg (.atom s)) (Formula.dia b (.conj (C r t) (.atom s))))
def A (r s t : Atom) (a b : Agent) : Formula Atom Agent :=
  .conj (.neg (.atom r)) (.box b (Formula.or (.atom r) (Formula.or (.atom t) (D r s t a b))))
def Q (r s t : Atom) (a b : Agent) : Formula Atom Agent :=
  .box a (Formula.imp (P r t) (.neg (A r s t a b)))
def B (r s t : Atom) (a b : Agent) : Formula Atom Agent :=
  Formula.or (A r s t a b) (Q r s t a b)
def Y (r t : Atom) (a : Agent) : Formula Atom Agent := Formula.dia a (P r t)
def Z (r t q : Atom) (a : Agent) : Formula Atom Agent :=
  Formula.dia a (.conj (P r t) (.atom q))
def H (r s t : Atom) (a b : Agent) : Formula Atom Agent :=
  .box a (Formula.imp (P r t) (B r s t a b))
def base (r s t : Atom) (a b : Agent) : Formula Atom Agent :=
  Formula.or (.conj (C r t) (A r s t a b)) (.conj (P r t) (B r s t a b))
def strongFormula (r s t : Atom) (a b : Agent) : Formula Atom Agent :=
  Formula.or (base r s t a b) (.conj (.atom r) (Y r t a))
def stageFormula (r s t q : Atom) (a b : Agent) : Formula Atom Agent :=
  Formula.or (base r s t a b)
    (.conj (.atom r) (Formula.or (Z r t q a) (.conj (Y r t a) (H r s t a b))))

variable (r s t q : Atom) (a b : Agent)

@[simp] theorem strong_at_C (M : Model World Atom Agent) (x : World)
    (hx : M.Satisfies x (C r t)) :
    M.Satisfies x (strongFormula r s t a b) ↔ M.Satisfies x (A r s t a b) := by
  have hr : ¬M.val r x := hx.1
  have ht : ¬M.val t x := hx.2
  simp [strongFormula, base, C, P, hr, ht]

@[simp] theorem strong_at_P (M : Model World Atom Agent) (x : World)
    (hx : M.Satisfies x (P r t)) :
    M.Satisfies x (strongFormula r s t a b) ↔ M.Satisfies x (B r s t a b) := by
  have hr : ¬M.val r x := hx.1
  have ht : M.val t x := hx.2
  simp [strongFormula, base, C, P, hr, ht]

@[simp] theorem stage_at_C (M : Model World Atom Agent) (x : World)
    (hx : M.Satisfies x (C r t)) :
    M.Satisfies x (stageFormula r s t q a b) ↔ M.Satisfies x (A r s t a b) := by
  have hr : ¬M.val r x := hx.1
  have ht : ¬M.val t x := hx.2
  simp [stageFormula, base, C, P, hr, ht]

@[simp] theorem stage_at_P (M : Model World Atom Agent) (x : World)
    (hx : M.Satisfies x (P r t)) :
    M.Satisfies x (stageFormula r s t q a b) ↔ M.Satisfies x (B r s t a b) := by
  have hr : ¬M.val r x := hx.1
  have ht : M.val t x := hx.2
  simp [stageFormula, base, C, P, hr, ht]

/-- At a non-root state, A implies the common non-root disjunct. -/
theorem base_of_A (M : Model World Atom Agent) (x : World)
    (hA : M.Satisfies x (A r s t a b)) : M.Satisfies x (base r s t a b) := by
  classical
  have hr : ¬M.val r x := hA.1
  by_cases ht : M.val t x
  · exact (M.satisfies_or x _ _).mpr (Or.inr ⟨⟨hr, ht⟩,
      (M.satisfies_or x _ _).mpr (Or.inl hA)⟩)
  · exact (M.satisfies_or x _ _).mpr (Or.inl ⟨⟨hr, ht⟩, hA⟩)

/-- Once all b-successors satisfy the propositional disjunction r or t, they
continue doing so under every later arrow deletion. -/
def CleanB (M : Model World Atom Agent) (x : World) : Prop :=
  ∀ y, M.rel b x y → M.val r y ∨ M.val t y

theorem A_of_cleanB (M : Model World Atom Agent) (x : World)
    (hr : ¬M.val r x) (hclean : CleanB r t b M x) :
    M.Satisfies x (A r s t a b) := by
  refine ⟨hr, fun y hy => ?_⟩
  rcases hclean y hy with hyr | hyt
  · exact (M.satisfies_or y _ _).mpr (Or.inl hyr)
  · exact (M.satisfies_or y _ _).mpr (Or.inr
      ((M.satisfies_or y _ _).mpr (Or.inl hyt)))

/-- Falsity of A at a non-root state removes every C-valued b-target. -/
theorem repair_A (M : Model World Atom Agent) (hM : IsK45 M)
    (θ : Formula Atom Agent)
    (hC : ∀ y, M.Satisfies y (C r t) → M.Satisfies y θ → M.Satisfies y (A r s t a b))
    (x : World) (hr : ¬M.val r x) (hnA : ¬M.Satisfies x (A r s t a b)) :
    CleanB r t b (M.update θ) x := by
  classical
  intro y hy
  by_cases hyr : M.val r y
  · exact Or.inl hyr
  by_cases hyt : M.val t y
  · exact Or.inr hyt
  have hyA := hC y ⟨hyr, hyt⟩ hy.2
  have hxBox := (Model.modalAgreement_box hM hy.1
    (Formula.or (.atom r) (Formula.or (.atom t) (D r s t a b)))).mpr hyA.2
  exact (hnA ⟨hr, hxBox⟩).elim

/-- P-target existence survives a finite update when the announcement agrees
with B at P-states. -/
theorem preserve_Y (M : Model World Atom Agent) (hM : IsK45 M)
    (θ : Formula Atom Agent)
    (hP : ∀ y, M.Satisfies y (P r t) → M.Satisfies y (B r s t a b) → M.Satisfies y θ)
    (x : World) (hY : M.Satisfies x (Y r t a)) :
    (M.update θ).Satisfies x (Y r t a) := by
  classical
  obtain ⟨y, hxy, hyP⟩ := (M.satisfies_dia x a _).mp hY
  by_cases hex : ∃ z, M.rel a x z ∧ M.Satisfies z (P r t) ∧ M.Satisfies z (A r s t a b)
  · obtain ⟨z, hxz, hzP, hzA⟩ := hex
    exact ((M.update θ).satisfies_dia x a _).mpr ⟨z,
      ⟨hxz, hP z hzP ((M.satisfies_or z _ _).mpr (Or.inl hzA))⟩, hzP⟩
  · have hyQ : M.Satisfies y (Q r s t a b) := by
      intro z hyz
      apply (M.satisfies_imp z _ _).mpr
      intro hzP hzA
      exact hex ⟨z, (hM a).1 hxy hyz, hzP, hzA⟩
    exact ((M.update θ).satisfies_dia x a _).mpr ⟨y,
      ⟨hxy, hP y hyP ((M.satisfies_or y _ _).mpr (Or.inr hyQ))⟩, hyP⟩

/-- The special propositional b-successor condition is permanent. -/
theorem cleanB_later (M : Model World Atom Agent) (θ : Formula Atom Agent)
    (x : World) {n m : Nat} (hnm : n ≤ m)
    (hclean : CleanB r t b (M.iterateUpdate θ n) x) :
    CleanB r t b (M.iterateUpdate θ m) x := by
  intro y hy
  have hval := hclean y (M.iterateUpdate_rel_antitone θ hnm hy)
  simpa only [Model.iterateUpdate_val] using hval

/-- Lemma 11: the first witness is strongly eventually successful. -/
theorem strongFormula_strongEventual :
    StrongEventual.{u} true true (strongFormula r s t a b) := by
  classical
  intro World M hM x hx
  change M.Satisfies x (strongFormula r s t a b) at hx
  by_cases hr : M.val r x
  · have hY : M.Satisfies x (Y r t a) := by
      simpa [strongFormula, base, C, P, hr] using hx
    have hYall : ∀ n, (M.iterateUpdate (strongFormula r s t a b) n).Satisfies x (Y r t a) := by
      intro n
      induction n with
      | zero => exact hY
      | succ n ih =>
        exact preserve_Y r s t a b _ (M.iterateUpdate_isK45 hM _ n) _
          (fun y hy hB => (strong_at_P r s t a b _ y hy).mpr hB) x ih
    refine ⟨1, le_rfl, fun n _ => ?_⟩
    have hrn : (M.iterateUpdate (strongFormula r s t a b) n).val r x := by
      simpa only [Model.iterateUpdate_val] using hr
    exact ((M.iterateUpdate _ n).satisfies_or x _ _).mpr (Or.inr ⟨hrn, hYall n⟩)
  · by_cases hall : ∀ n, (M.iterateUpdate (strongFormula r s t a b) n).Satisfies x (A r s t a b)
    · refine ⟨1, le_rfl, fun n _ => ?_⟩
      exact ((M.iterateUpdate _ n).satisfies_or x _ _).mpr
        (Or.inl (base_of_A r s t a b _ x (hall n)))
    · push_neg at hall
      obtain ⟨n, hn⟩ := hall
      have hrn : ¬(M.iterateUpdate (strongFormula r s t a b) n).val r x := by
        simpa only [Model.iterateUpdate_val] using hr
      have hc := repair_A r s t a b _ (M.iterateUpdate_isK45 hM _ n) _
        (fun y hy hθ => (strong_at_C r s t a b _ y hy).mp hθ) x hrn hn
      refine ⟨n + 1, by omega, fun m hm => ?_⟩
      have hcm := cleanB_later r t b M (strongFormula r s t a b) x hm hc
      have hrm : ¬(M.iterateUpdate (strongFormula r s t a b) m).val r x := by
        simpa only [Model.iterateUpdate_val] using hr
      exact ((M.iterateUpdate _ m).satisfies_or x _ _).mpr
        (Or.inl (base_of_A r s t a b _ x (A_of_cleanB r s t a b _ x hrm hcm)))

/-- Lemma 11: the second witness satisfies the S condition at every finite stage. -/
theorem stageFormula_finiteStageCondition :
    FiniteStageCondition.{u} true true (stageFormula r s t q a b) := by
  classical
  intro k World M hM x hx hC
  change M.Satisfies x (stageFormula r s t q a b) at hx
  let N := M.iterateUpdate (stageFormula r s t q a b) k
  have hN : IsK45 N := M.iterateUpdate_isK45 hM _ k
  change N.Satisfies x (stageFormula r s t q a b)
  by_cases hr : M.val r x
  · have hY : M.Satisfies x (Y r t a) := by
      have hh : M.Satisfies x (Z r t q a) ∨
          (M.Satisfies x (Y r t a) ∧ M.Satisfies x (H r s t a b)) := by
        simpa [stageFormula, base, C, P, hr] using hx
      rcases hh with hZ | hh
      · obtain ⟨y, hxy, hyP, _⟩ := (M.satisfies_dia x a _).mp hZ
        exact (M.satisfies_dia x a _).mpr ⟨y, hxy, hyP⟩
      · exact hh.1
    have hYall : ∀ n, (M.iterateUpdate (stageFormula r s t q a b) n).Satisfies x (Y r t a) := by
      intro n
      induction n with
      | zero => exact hY
      | succ n ih =>
        exact preserve_Y r s t a b _ (M.iterateUpdate_isK45 hM _ n) _
          (fun y hy hB => (stage_at_P r s t q a b _ y hy).mpr hB) x ih
    have hH : N.Satisfies x (H r s t a b) := by
      intro y hxy
      apply (N.satisfies_imp y _ _).mpr
      intro hyP
      exact (stage_at_P r s t q a b N y hyP).mp
        (hC y (Relation.TransGen.single ⟨a, hxy⟩))
    have hrN : N.val r x := by simpa only [N, Model.iterateUpdate_val] using hr
    exact (N.satisfies_or x _ _).mpr (Or.inr ⟨hrN,
      (N.satisfies_or x _ _).mpr (Or.inr ⟨hYall k, hH⟩)⟩)
  · have hrN : ¬N.val r x := by simpa only [N, Model.iterateUpdate_val] using hr
    have hA : N.Satisfies x (A r s t a b) := by
      refine ⟨hrN, fun y hxy => ?_⟩
      by_cases hyr : N.val r y
      · exact (N.satisfies_or y _ _).mpr (Or.inl hyr)
      by_cases hyt : N.val t y
      · exact (N.satisfies_or y _ _).mpr (Or.inr ((N.satisfies_or y _ _).mpr (Or.inl hyt)))
      have hyA : N.Satisfies y (A r s t a b) :=
        (stage_at_C r s t q a b N y ⟨hyr, hyt⟩).mp
          (hC y (Relation.TransGen.single ⟨b, hxy⟩))
      have hyy : N.rel b y y := (hN b).2 hxy hxy
      exact hyA.2 y hyy
    exact (N.satisfies_or x _ _).mpr (Or.inl (base_of_A r s t a b N x hA))

end TruePreservation
end EventualAndStrongEventualNotionsInPublicAnnouncements
