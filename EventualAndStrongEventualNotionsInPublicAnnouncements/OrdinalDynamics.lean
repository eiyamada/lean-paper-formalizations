import EventualAndStrongEventualNotionsInPublicAnnouncements.CommonBelief
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

/-!
# Transfinite believed announcements

The relation at stage `α` consists of the original arrows whose targets satisfy
the announcement at every earlier stage. This well-founded recursive definition
is proved to satisfy the zero, successor and limit clauses in the paper. No
monotonicity of formula satisfaction is assumed.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity
open Order

universe u v w

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- Transfinite iteration of a believed public announcement. -/
def ordinalUpdate (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) : Model World Atom Agent :=
  { rel := fun i x y => M.rel i x y ∧ ∀ β, β < α → (ordinalUpdate M φ β).Satisfies y φ
    val := M.val }
termination_by α
decreasing_by assumption

/-- Unfolding the relation does not require any frame hypothesis. -/
theorem ordinalUpdate_rel_iff (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) (i : Agent) (x y : World) :
    (ordinalUpdate M φ α).rel i x y ↔
      M.rel i x y ∧ ∀ β < α, (ordinalUpdate M φ β).Satisfies y φ := by
  rw [ordinalUpdate]

@[simp] theorem ordinalUpdate_val (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) (p : Atom) (x : World) :
    (ordinalUpdate M φ α).val p x ↔ M.val p x := by
  rw [ordinalUpdate]

@[simp] theorem ordinalUpdate_zero (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    ordinalUpdate M φ 0 = M := by
  apply Model.ext'
  · intro i x y
    simp [ordinalUpdate_rel_iff]
  · intro p x
    exact ordinalUpdate_val M φ 0 p x

@[simp] theorem ordinalUpdate_succ (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) :
    ordinalUpdate M φ (Order.succ α) = (ordinalUpdate M φ α).update φ := by
  apply Model.ext'
  · intro i x y
    rw [ordinalUpdate_rel_iff, Model.update_rel, ordinalUpdate_rel_iff]
    constructor
    · rintro ⟨hxy, h⟩
      exact ⟨⟨hxy, fun β hβ => h β (lt_trans hβ (Order.lt_succ α))⟩,
        h α (Order.lt_succ α)⟩
    · rintro ⟨⟨hxy, h⟩, hα⟩
      refine ⟨hxy, fun β hβ => ?_⟩
      rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hβ) with hβα | rfl
      · exact h β hβα
      · exact hα
  · intro p x
    simp

/-- Later stages have fewer arrows. -/
theorem ordinalUpdate_rel_antitone (M : Model World Atom Agent)
    (φ : Formula Atom Agent) {α β : Ordinal.{max u w}} (hαβ : α ≤ β)
    {i : Agent} {x y : World} :
    (ordinalUpdate M φ β).rel i x y → (ordinalUpdate M φ α).rel i x y := by
  rw [ordinalUpdate_rel_iff, ordinalUpdate_rel_iff]
  exact fun ⟨hxy, h⟩ => ⟨hxy, fun γ hγ => h γ (lt_of_lt_of_le hγ hαβ)⟩

/-- The limit-stage accessibility relation is the intersection of its predecessors. -/
theorem ordinalUpdate_limit_rel_iff (M : Model World Atom Agent)
    (φ : Formula Atom Agent) {α : Ordinal.{max u w}} (hα : IsSuccLimit α)
    (i : Agent) (x y : World) :
    (ordinalUpdate M φ α).rel i x y ↔
      ∀ β < α, (ordinalUpdate M φ β).rel i x y := by
  constructor
  · exact fun h β hβ => ordinalUpdate_rel_antitone M φ hβ.le h
  · intro h
    rw [ordinalUpdate_rel_iff]
    refine ⟨?_, fun β hβ => ?_⟩
    · simpa using h 0 hα.bot_lt
    · have hsucc := h (Order.succ β) (hα.succ_lt hβ)
      rw [ordinalUpdate_succ, Model.update_rel] at hsucc
      exact hsucc.2

/-- The ordinal definition extends the existing natural-number iteration. -/
@[simp] theorem ordinalUpdate_natCast (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (n : Nat) :
    ordinalUpdate M φ (n : Ordinal.{max u w}) = M.iterateUpdate φ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Ordinal.natCast_succ, ordinalUpdate_succ, ih, Model.iterateUpdate_succ]

/-- Restarting at an ordinal stage gives the tail of the same transfinite run.
Ordinal addition has the order corresponding to first `α`, then `β` updates. -/
theorem ordinalUpdate_add (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α β : Ordinal.{max u w}) :
    ordinalUpdate M φ (α + β) = ordinalUpdate (ordinalUpdate M φ α) φ β := by
  induction β using Ordinal.induction with
  | h β ih =>
    apply Model.ext'
    · intro i x y
      rw [ordinalUpdate_rel_iff, ordinalUpdate_rel_iff, ordinalUpdate_rel_iff]
      constructor
      · rintro ⟨hxy, h⟩
        refine ⟨⟨hxy, fun γ hγ => h γ (lt_of_lt_of_le hγ (Ordinal.le_add_right α β))⟩,
          fun γ hγ => ?_⟩
        rw [← ih γ hγ]
        exact h (α + γ) ((add_lt_add_iff_left α).mpr hγ)
      · rintro ⟨⟨hxy, hα⟩, hβ⟩
        refine ⟨hxy, fun γ hγ => ?_⟩
        by_cases hγα : γ < α
        · exact hα γ hγα
        · have heq : α + (γ - α) = γ :=
            Ordinal.add_sub_cancel_of_le (le_of_not_gt hγα)
          have hsub : γ - α < β :=
            (add_lt_add_iff_left α).mp (by rw [heq]; exact hγ)
          have ht := hβ (γ - α) hsub
          rw [← ih (γ - α) hsub, heq] at ht
          exact ht
    · intro p x
      simp

/-- Transitivity and Euclideanness are preserved at every ordinal stage. -/
theorem ordinalUpdate_isK45 (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (hM : IsK45 M) (α : Ordinal.{max u w}) :
    IsK45 (ordinalUpdate M φ α) := by
  intro i
  constructor
  · intro x y z hxy hyz
    rw [ordinalUpdate_rel_iff] at hxy hyz ⊢
    exact ⟨(hM i).1 hxy.1 hyz.1, hyz.2⟩
  · intro x y z hxy hxz
    rw [ordinalUpdate_rel_iff] at hxy hxz ⊢
    exact ⟨(hM i).2 hxy.1 hxz.1, hxz.2⟩

/-- A fixed stage remains fixed at every later ordinal. -/
theorem ordinalUpdate_eq_of_ge_of_step (M : Model World Atom Agent)
    (φ : Formula Atom Agent) {α β : Ordinal.{max u w}}
    (hstep : ordinalUpdate M φ (Order.succ α) = ordinalUpdate M φ α)
    (hαβ : α ≤ β) : ordinalUpdate M φ β = ordinalUpdate M φ α := by
  induction β using Ordinal.induction with
  | h β ih =>
    apply Model.ext'
    · intro i x y
      constructor
      · exact ordinalUpdate_rel_antitone M φ hαβ
      · intro hxy
        rw [ordinalUpdate_rel_iff] at hxy ⊢
        refine ⟨hxy.1, fun γ hγ => ?_⟩
        by_cases hγα : γ < α
        · exact hxy.2 γ hγα
        · have heq := ih γ hγ (le_of_not_gt hγα)
          rw [heq]
          have harrow : (ordinalUpdate M φ (Order.succ α)).rel i x y := by
            rw [hstep, ordinalUpdate_rel_iff]
            exact hxy
          rw [ordinalUpdate_succ, Model.update_rel] at harrow
          exact harrow.2
    · intro p x
      simp

/-- A set closed under the arrows at a stage is still closed at every later stage. -/
theorem ordinalUpdate_forwardClosed_of_le (M : Model World Atom Agent)
    (φ : Formula Atom Agent) {α β : Ordinal.{max u w}} (hαβ : α ≤ β)
    {U : Set World} (hU : (ordinalUpdate M φ α).ForwardClosed U) :
    (ordinalUpdate M φ β).ForwardClosed U :=
  hU.mono_rel (fun _ _ _ => ordinalUpdate_rel_antitone M φ hαβ)

/-- Common belief at any stage makes the generated part of the model permanent. -/
theorem common_ordinal_locallyAgrees (M : Model World Atom Agent)
    (φ : Formula Atom Agent) {α : Ordinal.{max u w}} {x : World}
    (hC : Common (ordinalUpdate M φ α) x φ)
    {β : Ordinal.{max u w}} (hαβ : α ≤ β) :
    (ordinalUpdate M φ α).LocallyAgrees (ordinalUpdate M φ β)
      ((ordinalUpdate M φ α).generatedSet x) := by
  induction β using Ordinal.induction with
  | h β ih =>
    constructor
    · intro p y hy
      simp
    · intro i y hy z hz
      constructor
      · intro hyz
        have hbase := (ordinalUpdate_rel_iff M φ α i y z).mp hyz
        rw [ordinalUpdate_rel_iff]
        refine ⟨hbase.1, fun γ hγ => ?_⟩
        by_cases hγα : γ < α
        · exact hbase.2 γ hγα
        · have hαγ := le_of_not_gt hγα
          have hlocal := ih γ hγ hαγ
          have hU : (ordinalUpdate M φ α).ForwardClosed
              ((ordinalUpdate M φ α).generatedSet x) :=
            (ordinalUpdate M φ α).generatedSet_forwardClosed x
          exact (Model.satisfies_iff_of_locallyAgrees hU
            (ordinalUpdate_forwardClosed_of_le M φ hαγ hU) hlocal z hz φ).mp
              (common_target hC hy hyz)
      · exact ordinalUpdate_rel_antitone M φ hαβ

/-- Common belief at a stage freezes the truth of every formula at the point
through all later ordinals. -/
theorem common_ordinal_stage_permanent (M : Model World Atom Agent)
    (φ : Formula Atom Agent) {α : Ordinal.{max u w}} {x : World}
    (hC : Common (ordinalUpdate M φ α) x φ)
    {β : Ordinal.{max u w}} (hαβ : α ≤ β) (ψ : Formula Atom Agent) :
    (ordinalUpdate M φ β).Satisfies x ψ ↔ (ordinalUpdate M φ α).Satisfies x ψ := by
  have hU : (ordinalUpdate M φ α).ForwardClosed
      ((ordinalUpdate M φ α).generatedSet x) :=
    (ordinalUpdate M φ α).generatedSet_forwardClosed x
  exact (Model.satisfies_iff_of_locallyAgrees hU
    (ordinalUpdate_forwardClosed_of_le M φ hαβ hU)
    (common_ordinal_locallyAgrees M φ hC hαβ) x
    ((ordinalUpdate M φ α).reachable_refl x) ψ).symm

/-- Common belief makes every ordinal repetition preserve all truth at the root. -/
theorem common_ordinal_permanent {M : Model World Atom Agent} {x : World}
    {φ : Formula Atom Agent} (hC : Common M x φ)
    (α : Ordinal.{max u w}) (ψ : Formula Atom Agent) :
    (ordinalUpdate M φ α).Satisfies x ψ ↔ M.Satisfies x ψ := by
  have hC' : Common (ordinalUpdate M φ 0) x φ := by simpa using hC
  simpa using common_ordinal_stage_permanent M φ hC' (Ordinal.zero_le α) ψ

/-- The set of original labelled accessibility arrows. -/
def OriginalArrow (M : Model World Atom Agent) :=
  {e : Agent × World × World // M.rel e.1 e.2.1 e.2.2}

/-- Distinct consecutive stages delete an original labelled arrow. -/
theorem exists_deleted_originalArrow (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (α : Ordinal.{max u w})
    (h : ordinalUpdate M φ (Order.succ α) ≠ ordinalUpdate M φ α) :
    ∃ e : OriginalArrow M,
      (ordinalUpdate M φ α).rel e.1.1 e.1.2.1 e.1.2.2 ∧
      ¬(ordinalUpdate M φ (Order.succ α)).rel e.1.1 e.1.2.1 e.1.2.2 := by
  classical
  by_contra! hn
  apply h
  apply Model.ext'
  · intro i x y
    constructor
    · exact ordinalUpdate_rel_antitone M φ (Order.le_succ α)
    · intro hxy
      have hbase := (ordinalUpdate_rel_iff M φ α i x y).mp hxy |>.1
      exact hn ⟨(i, x, y), hbase⟩ hxy
  · intro p x
    simp

/-- Proposition 3: stabilization occurs before the successor cardinal of the
set of original labelled arrows. -/
theorem exists_ordinalUpdate_stableStep_bounded (M : Model World Atom Agent)
    (φ : Formula Atom Agent) :
    ∃ α < (Order.succ (Cardinal.mk (OriginalArrow M))).ord,
      ordinalUpdate M φ (Order.succ α) = ordinalUpdate M φ α := by
  classical
  let κ := (Order.succ (Cardinal.mk (OriginalArrow M))).ord
  by_contra! hnone
  have hκ : (0 : Ordinal.{max u w}) < κ := by
    simpa only [Cardinal.ord_zero] using
      Cardinal.ord_strictMono (Cardinal.succ_pos (Cardinal.mk (OriginalArrow M)))
  have hex : ∀ α < κ, ∃ e : OriginalArrow M,
      (ordinalUpdate M φ α).rel e.1.1 e.1.2.1 e.1.2.2 ∧
      ¬(ordinalUpdate M φ (Order.succ α)).rel e.1.1 e.1.2.1 e.1.2.2 :=
    fun α hα => exists_deleted_originalArrow M φ α (hnone α hα)
  obtain ⟨e₀, _⟩ := hex 0 hκ
  let f : Ordinal.{max u w} → OriginalArrow M := fun α =>
    if hα : α < κ then Classical.choose (hex α hα) else e₀
  have hf (α : Ordinal.{max u w}) (hα : α < κ) :
      (ordinalUpdate M φ α).rel (f α).1.1 (f α).1.2.1 (f α).1.2.2 ∧
      ¬(ordinalUpdate M φ (Order.succ α)).rel (f α).1.1 (f α).1.2.1 (f α).1.2.2 := by
    simpa only [f, dif_pos hα] using Classical.choose_spec (hex α hα)
  apply Cardinal.not_injective_limitation_set f
  intro α hα β hβ heq
  have hnotlt : ∀ a < κ, ∀ b < κ, f a = f b → ¬a < b := by
    intro a ha b hb hab hlt
    have hremain := ordinalUpdate_rel_antitone M φ (Order.succ_le_of_lt hlt) (hf b hb).1
    rw [← hab] at hremain
    exact (hf a ha).2 hremain
  exact le_antisymm (le_of_not_gt (hnotlt β hβ α hα heq.symm))
    (le_of_not_gt (hnotlt α hα β hβ heq))

theorem exists_ordinalUpdate_stableStep (M : Model World Atom Agent)
    (φ : Formula Atom Agent) :
    ∃ α : Ordinal.{max u w},
      ordinalUpdate M φ (Order.succ α) = ordinalUpdate M φ α := by
  obtain ⟨α, _, hα⟩ := exists_ordinalUpdate_stableStep_bounded M φ
  exact ⟨α, hα⟩

/-- Any globally fixed model satisfies common belief of its announcement. -/
theorem common_of_update_eq_self (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (h : M.update φ = M) : ∀ x, Common M x φ :=
  common_at_fixed h

/-- Proposition 3, including common belief at the fixed stage. -/
theorem ordinal_stabilization (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    ∃ α : Ordinal.{max u w},
      ordinalUpdate M φ (Order.succ α) = ordinalUpdate M φ α ∧
      ∀ x, Common (ordinalUpdate M φ α) x φ := by
  obtain ⟨α, hα⟩ := exists_ordinalUpdate_stableStep M φ
  refine ⟨α, hα, common_of_update_eq_self _ φ ?_⟩
  simpa only [ordinalUpdate_succ] using hα

end EventualAndStrongEventualNotionsInPublicAnnouncements
