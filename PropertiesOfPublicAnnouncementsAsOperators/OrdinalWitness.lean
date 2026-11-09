import PropertiesOfPublicAnnouncementsAsOperators.Dynamics

/-! # A single formula attaining every positive ordinal stabilization rank -/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u

namespace OrdinalWitness

/-- The one-agent formula in Theorem 24(4): `p ∧ ◇(p ∧ □¬p)`. -/
def formula : Formula Unit Unit :=
  .conj (.atom ()) (Formula.dia () (.conj (.atom ()) (.box () (.neg (.atom ())))))

noncomputable def index {α : Ordinal.{u}} (x : α.toType) : Ordinal.{u} :=
  ((Ordinal.enumIsoToType α).symm x).val

theorem index_lt {α : Ordinal.{u}} (x : α.toType) : index x < α :=
  ((Ordinal.enumIsoToType α).symm x).property

theorem exists_index {α β : Ordinal.{u}} (h : β < α) : ∃ x : α.toType, index x = β := by
  refine ⟨Ordinal.enumIsoToType α ⟨β, h⟩, ?_⟩
  simp [index]

/-- A fresh predecessor sees every ordinal state and itself. -/
def base {α : Ordinal.{u}} : Option α.toType → Option α.toType → Prop
  | none, _ => True
  | some _, none => False
  | some x, some y => index y < index x

def alive {α : Ordinal.{u}} (β : Ordinal.{u}) : Option α.toType → Prop
  | none => β = 0
  | some x => β ≤ index x

/-- Exact BPAL stage of the ordinal peeling model. -/
def stage (α β : Ordinal.{u}) : Model (Option α.toType) Unit Unit where
  rel _ x y := base x y ∧ alive β y
  val _ x := x.isSome

theorem leaf_iff (α β : Ordinal.{u}) (x : α.toType) :
    (stage α β).Satisfies (some x) (.conj (.atom ()) (.box () (.neg (.atom ())))) ↔
      index x ≤ β := by
  constructor
  · intro h
    by_contra hn
    have hlt : β < index x := lt_of_not_ge hn
    obtain ⟨y, hy⟩ := exists_index (lt_trans hlt (index_lt x))
    have harrow : (stage α β).rel () (some x) (some y) := by
      change index y < index x ∧ β ≤ index y
      rw [hy]
      exact ⟨hlt, le_rfl⟩
    exact h.2 (some y) harrow (by trivial)
  · intro h
    refine ⟨by trivial, ?_⟩
    intro y hy
    cases y with
    | none => exact hy.1.elim
    | some y =>
        have hlt : index y < index x := hy.1
        have hle : β ≤ index y := hy.2
        exact (not_lt_of_ge (le_trans h hle) hlt).elim

theorem formula_some_iff (α β : Ordinal.{u}) (x : α.toType) :
    (stage α β).Satisfies (some x) formula ↔ β < index x := by
  rw [formula, Model.satisfies_and, Model.satisfies_dia]
  constructor
  · rintro ⟨_, y, hy, hleaf⟩
    cases y with
    | none => exact hy.1.elim
    | some y =>
        exact lt_of_le_of_lt hy.2 hy.1
  · intro h
    obtain ⟨y, hy⟩ := exists_index (lt_trans h (index_lt x))
    refine ⟨by trivial, some y, ?_, (leaf_iff α β y).mpr ?_⟩
    · change index y < index x ∧ β ≤ index y
      rw [hy]
      exact ⟨h, le_rfl⟩
    · rw [hy]

@[simp] theorem formula_none (α β : Ordinal.{u}) :
    ¬(stage α β).Satisfies none formula := by
  intro h
  exact Bool.false_ne_true h.1

theorem all_lt_iff_le (β γ : Ordinal.{u}) : (∀ δ < β, δ < γ) ↔ β ≤ γ := by
  constructor
  · intro h
    by_contra hn
    exact (lt_irrefl γ) (h γ (lt_of_not_ge hn))
  · intro h δ hδ
    exact lt_of_lt_of_le hδ h

/-- The ordinal recursion removes exactly the targets below the stage index. -/
theorem ordinalUpdate_eq_stage (α β : Ordinal.{u}) :
    ordinalUpdate (stage α 0) formula β = stage α β := by
  induction β using Ordinal.induction with
  | h β ih =>
      apply Model.ext'
      · intro i x y
        rw [ordinalUpdate_rel_iff]
        have heval : (∀ γ < β, (ordinalUpdate (stage α 0) formula γ).Satisfies y formula) ↔
            (∀ γ < β, (stage α γ).Satisfies y formula) := by
          apply forall_congr'
          intro γ
          apply forall_congr'
          intro hγ
          rw [ih γ hγ]
        rw [heval]
        cases y with
        | none =>
            change (base x none ∧ (0 : Ordinal.{u}) = 0) ∧
              (∀ γ < β, (stage α γ).Satisfies none formula) ↔ base x none ∧ β = 0
            simp only [formula_none, imp_false, not_lt, and_true]
            constructor
            · rintro ⟨hb, h⟩
              exact ⟨hb, le_antisymm (h 0) (Ordinal.zero_le β)⟩
            · rintro ⟨hb, rfl⟩
              exact ⟨hb, fun γ => Ordinal.zero_le γ⟩
        | some y =>
            change (base x (some y) ∧ (0 : Ordinal.{u}) ≤ index y) ∧
              (∀ γ < β, (stage α γ).Satisfies (some y) formula) ↔
              base x (some y) ∧ β ≤ index y
            simp only [formula_some_iff, all_lt_iff_le, zero_le, and_true]
      · intro p x
        exact ordinalUpdate_val (stage α 0) formula β p x

theorem incoming (α : Ordinal.{u}) : HasIncoming (stage α 0) := by
  intro y
  refine ⟨(), none, ?_⟩
  cases y <;> simp [stage, base, alive]

/-- The terminal stage is edgeless and hence fixed. -/
theorem stable_at (α : Ordinal.{u}) (hα : 0 < α) : BPALStable (stage α 0) formula α := by
  unfold BPALStable
  rw [ordinalUpdate_eq_stage, ordinalUpdate_eq_stage]
  apply Model.ext'
  · intro i x y
    cases y with
    | none =>
        simp [stage, alive, ne_of_gt hα, Ordinal.succ_ne_zero]
    | some y =>
        have hn : ¬α ≤ index y := not_le_of_gt (index_lt y)
        have hn' : ¬Order.succ α ≤ index y := fun h => hn (le_trans (Order.le_succ α) h)
        exact iff_of_false (fun h => hn' h.2) (fun h => hn h.2)
  · intro p x
    rfl

/-- Every earlier stage deletes the state whose ordinal index equals that stage. -/
theorem not_stable_before (α β : Ordinal.{u}) (h : β < α) :
    ¬BPALStable (stage α 0) formula β := by
  intro heq
  obtain ⟨y, hy⟩ := exists_index h
  have hrel : (stage α β).rel () none (some y) := by
    change True ∧ β ≤ index y
    exact ⟨trivial, hy ▸ le_rfl⟩
  have heq' : stage α (Order.succ β) = stage α β := by
    simpa only [BPALStable, ordinalUpdate_eq_stage] using heq
  have hrel' : (stage α (Order.succ β)).rel () none (some y) := by rw [heq']; exact hrel
  have hbad : Order.succ β ≤ β := by
    have hle : Order.succ β ≤ index y := hrel'.2
    simpa only [hy] using hle
  exact (not_le_of_gt (Order.lt_succ β)) hbad

/-- Theorem 24(4), arbitrary frames, with a fixed formula independent of `α`. -/
theorem ranks_eq (α : Ordinal.{u}) (hα : 0 < α) :
    palRank (stage α 0) formula = α ∧ bpalRank (stage α 0) formula = α := by
  have hB : bpalRank (stage α 0) formula = α := by
    apply le_antisymm (bpalRank_le_of_stable _ _ (stable_at α hα))
    apply le_of_not_gt
    intro hlt
    exact not_stable_before α _ hlt (bpalRank_stable _ _)
  exact ⟨(stabilization_rank_eq_of_incoming _ _ (incoming α)).trans hB, hB⟩

section ArbitraryLanguage

variable {Atom Agent : Type} (p : Atom) (a : Agent)

/-- Interpret the one-atom, one-agent construction in any specified language. -/
def replicate {W : Type u} (M : Model W Unit Unit) : Model W Atom Agent where
  rel _ := M.rel ()
  val _ := M.val ()

def formulaMany : Formula Atom Agent := formula.map (fun _ => p) (fun _ => a)

def stageMany (α β : Ordinal.{u}) : Model (Option α.toType) Atom Agent :=
  replicate (stage α β)

theorem replicate_satisfies {W : Type u} (M : Model W Unit Unit)
    (χ : Formula Unit Unit) (x : W) :
    (replicate M).Satisfies x (χ.map (fun _ => p) (fun _ => a)) ↔ M.Satisfies x χ := by
  induction χ generalizing x with
  | atom q => cases q; rfl
  | neg χ ih => exact not_congr (ih x)
  | conj χ ψ ihχ ihψ => exact and_congr (ihχ x) (ihψ x)
  | box i χ ih =>
      cases i
      exact forall_congr' fun y => imp_congr_right (fun _ => ih y)

theorem ordinalUpdate_stageMany (α β : Ordinal.{u}) :
    ordinalUpdate (stageMany α 0) (formulaMany p a) β = stageMany α β := by
  induction β using Ordinal.induction with
  | h β ih =>
      apply Model.ext'
      · intro i x y
        rw [ordinalUpdate_rel_iff]
        have heval : (∀ γ < β,
            (ordinalUpdate (stageMany α 0) (formulaMany p a) γ).Satisfies y (formulaMany p a)) ↔
            (∀ γ < β, (ordinalUpdate (stage α 0) formula γ).Satisfies y formula) := by
          apply forall_congr'
          intro γ
          apply forall_congr'
          intro hγ
          rw [ih γ hγ, ordinalUpdate_eq_stage]
          exact replicate_satisfies p a (stage α γ) formula y
        rw [heval]
        change ((stage α 0).rel () x y ∧
          ∀ γ < β, (ordinalUpdate (stage α 0) formula γ).Satisfies y formula) ↔
          (stage α β).rel () x y
        rw [← ordinalUpdate_rel_iff, ordinalUpdate_eq_stage]
      · intro q x
        exact ordinalUpdate_val (stageMany α 0) (formulaMany p a) β q x

theorem stageMany_stable_at (α : Ordinal.{u}) (hα : 0 < α) :
    BPALStable (stageMany α 0) (formulaMany p a) α := by
  unfold BPALStable
  rw [ordinalUpdate_stageMany, ordinalUpdate_stageMany]
  have heq : stage α (Order.succ α) = stage α α := by
    simpa only [BPALStable, ordinalUpdate_eq_stage] using stable_at α hα
  exact congrArg replicate heq

theorem stageMany_not_stable_before (α β : Ordinal.{u}) (h : β < α) :
    ¬BPALStable (stageMany α 0) (formulaMany p a) β := by
  intro heq
  apply not_stable_before α β h
  unfold BPALStable
  rw [ordinalUpdate_eq_stage, ordinalUpdate_eq_stage]
  have heq' : stageMany (Atom := Atom) (Agent := Agent) α (Order.succ β) =
      stageMany α β := by
    simpa only [BPALStable, ordinalUpdate_stageMany] using heq
  apply Model.ext'
  · intro _i x y
    exact Iff.of_eq (congrArg (fun M => M.rel a x y) heq')
  · intro q x
    rfl

/-- Theorem 24(4) over K for an arbitrary atom and an arbitrary chosen agent.
In particular this applies to the paper's countably infinite atom language and
every nonempty finite group of agents. -/
theorem ranks_eq_many (α : Ordinal.{u}) (hα : 0 < α) :
    palRank (stageMany α 0) (formulaMany p a) = α ∧
      bpalRank (stageMany α 0) (formulaMany p a) = α := by
  have hB : bpalRank (stageMany α 0) (formulaMany p a) = α := by
    apply le_antisymm (bpalRank_le_of_stable _ _ (stageMany_stable_at p a α hα))
    apply le_of_not_gt
    intro hlt
    exact stageMany_not_stable_before p a α _ hlt (bpalRank_stable _ _)
  have hin : HasIncoming (stageMany (Atom := Atom) (Agent := Agent) α 0) := by
    intro y
    refine ⟨a, none, ?_⟩
    cases y <;> simp [stageMany, replicate, stage, base, alive]
  exact ⟨(stabilization_rank_eq_of_incoming _ _ hin).trans hB, hB⟩

end ArbitraryLanguage

end OrdinalWitness

end PropertiesOfPublicAnnouncementsAsOperators
