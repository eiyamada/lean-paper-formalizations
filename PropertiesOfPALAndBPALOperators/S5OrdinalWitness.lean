import PropertiesOfPALAndBPALOperators.OrdinalWitness
import Lean.Elab.Tactic.Omega

/-!
# Arbitrary ordinal ranks on S5 frames

Worlds are nonempty finite histories, encoded by their current entry and a
list of preceding entries. A history can extend its parent's active
equivalence class only when its current ordinal is smaller. Invalid histories
are harmless additional roots. Each agent's relation is equality of a block
key, so equivalence of the accessibility relations holds by construction.
-/

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements
open OrdinalWitness

universe u

namespace S5OrdinalWitness

abbrev World (α : Ordinal.{u}) := α.toType × List α.toType

noncomputable def rank {α : Ordinal.{u}} (s : World α) : Ordinal.{u} := index s.1

def active {α : Ordinal.{u}} (s : World α) : Bool := decide (s.2.length % 2 = 0)

def parent {α : Ordinal.{u}} (s : World α) : Option (World α) :=
  match s.2 with
  | [] => none
  | x :: xs => some (x, xs)

def child {α : Ordinal.{u}} (s : World α) (x : α.toType) : World α :=
  (x, s.1 :: s.2)

@[simp] theorem parent_child {α : Ordinal.{u}} (s : World α) (x : α.toType) :
    parent (child s x) = some s := rfl

theorem active_child {α : Ordinal.{u}} (s : World α) (x : α.toType) :
    active (child s x) = ! active s := by
  by_cases h : s.2.length % 2 = 0
  · have h' : (s.2.length + 1) % 2 ≠ 0 := by omega
    simp [active, child, h, h']
  · have h' : (s.2.length + 1) % 2 = 0 := by omega
    simp [active, child, h, h']

theorem active_ne_of_parent {α : Ordinal.{u}} {s t : World α}
    (h : parent t = some s) : active t ≠ active s := by
  rcases t with ⟨x, xs⟩
  cases xs with
  | nil => simp [parent] at h
  | cons y ys =>
      have hs : (y, ys) = s := Option.some.inj h
      subst s
      change active (child (y, ys) x) ≠ active (y, ys)
      rw [active_child]
      exact Bool.not_ne_self _

noncomputable def block {α : Ordinal.{u}} (i : Bool) (s : World α) :
    Sum (World α) (World α) := by
  classical
  exact if i = active s then Sum.inl s else
    match parent s with
    | none => Sum.inr s
    | some t => if rank s < rank t then Sum.inl t else Sum.inr s

noncomputable def model (α : Ordinal.{u}) : Model (World α) Unit Bool where
  rel i s t := block i s = block i t
  val _ s := active s = true

theorem model_isS5 (α : Ordinal.{u}) : IsS5 (model α) := by
  intro i
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro x y z hxy hyz
    exact hxy.trans hyz
  · intro x y z hxy hxz
    exact hxy.symm.trans hxz

theorem active_edge_iff {α : Ordinal.{u}} (s t : World α) :
    ((model α).rel (active s) s t ∧ active t ≠ active s) ↔
      parent t = some s ∧ rank t < rank s := by
  classical
  have hs : block (active s) s = Sum.inl s := by simp [block]
  constructor
  · rintro ⟨he, hne⟩
    change block (active s) s = block (active s) t at he
    rw [hs] at he
    have ht := he.symm
    simp only [block, if_neg hne.symm] at ht
    cases hp : parent t with
    | none => simp [hp] at ht
    | some z =>
        by_cases hz : rank t < rank z
        · simp only [hp, if_pos hz, Sum.inl.injEq] at ht
          subst z
          exact ⟨rfl, hz⟩
        · simp [hp, hz] at ht
  · rintro ⟨hp, hr⟩
    have hne := active_ne_of_parent hp
    refine ⟨?_, hne⟩
    change block (active s) s = block (active s) t
    rw [hs]
    simp only [block, if_neg hne.symm, hp, if_pos hr]

noncomputable def stage (α β : Ordinal.{u}) : Model (World α) Unit Bool where
  rel i s t := (model α).rel i s t ∧ β ≤ rank t
  val := (model α).val

def L (χ : Formula Unit Bool) : Formula Unit Bool :=
  Formula.or
    (.conj (.atom ()) (Formula.dia true (.conj (.neg (.atom ())) χ)))
    (.conj (.neg (.atom ())) (Formula.dia false (.conj (.atom ()) χ)))

def delta : Formula Unit Bool := L Formula.verum

/-- The formula from the manuscript; it remains informative whenever true. -/
def formula : Formula Unit Bool := L (.neg delta)

theorem satisfies_L_iff (α β : Ordinal.{u}) (s : World α) (χ : Formula Unit Bool) :
    (stage α β).Satisfies s (L χ) ↔
      ∃ t, parent t = some s ∧ rank t < rank s ∧ β ≤ rank t ∧
        (stage α β).Satisfies t χ := by
  have hsemantic : (stage α β).Satisfies s (L χ) ↔
      ∃ t, (stage α β).rel (active s) s t ∧ active t ≠ active s ∧
        (stage α β).Satisfies t χ := by
    cases hs : active s <;>
      simp [L, Model.satisfies_or, Model.satisfies_and, Model.satisfies_dia,
        Model.satisfies_neg, Model.satisfies_atom, stage, model, hs, Bool.not_eq_false]
  rw [hsemantic]
  apply exists_congr
  intro t
  change (((model α).rel (active s) s t ∧ β ≤ rank t) ∧ active t ≠ active s ∧
      (stage α β).Satisfies t χ) ↔ _
  have he := active_edge_iff s t
  tauto

theorem delta_iff (α β : Ordinal.{u}) (s : World α) :
    (stage α β).Satisfies s delta ↔ β < rank s := by
  rw [delta, satisfies_L_iff]
  constructor
  · rintro ⟨t, _, ht, hβ, _⟩
    exact lt_of_le_of_lt hβ ht
  · intro h
    obtain ⟨x, hx⟩ := exists_index (lt_trans h (index_lt s.1))
    refine ⟨child s x, parent_child s x, ?_, ?_, Model.satisfies_verum _ _⟩
    · change index x < rank s
      simpa only [hx] using h
    · change β ≤ index x
      rw [hx]

theorem formula_iff (α β : Ordinal.{u}) (s : World α) :
    (stage α β).Satisfies s formula ↔ β < rank s := by
  rw [formula, satisfies_L_iff]
  constructor
  · rintro ⟨t, _, ht, hβ, _⟩
    exact lt_of_le_of_lt hβ ht
  · intro h
    obtain ⟨x, hx⟩ := exists_index (lt_trans h (index_lt s.1))
    refine ⟨child s x, parent_child s x, ?_, ?_, ?_⟩
    · change index x < rank s
      simpa only [hx] using h
    · change β ≤ index x
      rw [hx]
    · change ¬ (stage α β).Satisfies (child s x) delta
      rw [delta_iff]
      change ¬ β < index x
      rw [hx]
      exact lt_irrefl _

theorem ordinalUpdate_eq_stage (α β : Ordinal.{u}) :
    ordinalUpdate (model α) formula β = stage α β := by
  induction β using Ordinal.induction with
  | h β ih =>
      apply Model.ext'
      · intro i s t
        rw [ordinalUpdate_rel_iff]
        have heval : (∀ γ < β, (ordinalUpdate (model α) formula γ).Satisfies t formula) ↔
            (∀ γ < β, (stage α γ).Satisfies t formula) := by
          apply forall_congr'; intro γ
          apply forall_congr'; intro hγ
          rw [ih γ hγ]
        rw [heval]
        change ((model α).rel i s t ∧ (∀ γ < β, (stage α γ).Satisfies t formula)) ↔
          (model α).rel i s t ∧ β ≤ rank t
        simp only [formula_iff, all_lt_iff_le]
      · intro p s
        exact ordinalUpdate_val (model α) formula β p s

theorem stable_at (α : Ordinal.{u}) : BPALStable (model α) formula α := by
  unfold BPALStable
  rw [ordinalUpdate_eq_stage, ordinalUpdate_eq_stage]
  apply Model.ext'
  · intro i s t
    have hn : ¬ α ≤ rank t := not_le_of_gt (index_lt t.1)
    have hn' : ¬ Order.succ α ≤ rank t := fun h => hn (le_trans (Order.le_succ α) h)
    exact iff_of_false (fun h => hn' h.2) (fun h => hn h.2)
  · intro p s; rfl

theorem not_stable_before (α β : Ordinal.{u}) (h : β < α) :
    ¬ BPALStable (model α) formula β := by
  intro heq
  obtain ⟨x, hx⟩ := exists_index h
  let s : World α := (x, [])
  have hrank : rank s = β := hx
  have hrel : (stage α β).rel true s s := ⟨rfl, hrank ▸ le_rfl⟩
  have heq' : stage α (Order.succ β) = stage α β := by
    simpa only [BPALStable, ordinalUpdate_eq_stage] using heq
  have hrel' : (stage α (Order.succ β)).rel true s s := by rw [heq']; exact hrel
  have hbad : Order.succ β ≤ β := by simpa only [hrank] using hrel'.2
  exact not_le_of_gt (Order.lt_succ β) hbad

/-- Theorem 24(4): one fixed two-agent formula realizes every ordinal rank
on S5 models. The empty ordinal is also allowed and gives an empty model. -/
theorem ranks_eq (α : Ordinal.{u}) :
    palRank (model α) formula = α ∧ bpalRank (model α) formula = α := by
  have hB : bpalRank (model α) formula = α := by
    apply le_antisymm (bpalRank_le_of_stable _ _ (stable_at α))
    apply le_of_not_gt
    intro hlt
    exact not_stable_before α _ hlt (bpalRank_stable _ _)
  exact ⟨(stabilization_rank_eq_of_s5 _ _ (model_isS5 α)).trans hB, hB⟩

section ArbitraryAgents

variable {Atom Agent : Type} (p : Atom) (a b : Agent) (hab : a ≠ b)

def formulaMany : Formula Atom Agent :=
  formula.map (fun _ => p) (fun i => if i then a else b)

noncomputable def modelMany (α : Ordinal.{u}) : Model (World α) Atom Agent := by
  classical
  exact { rel := fun i s t => if i = a then (model α).rel true s t else (model α).rel false s t
          val := fun _ s => (model α).val () s }

noncomputable def stageMany (α β : Ordinal.{u}) : Model (World α) Atom Agent where
  rel i s t := (modelMany (Atom := Atom) a α).rel i s t ∧ β ≤ rank t
  val := (modelMany (Atom := Atom) a α).val

theorem modelMany_isS5 (α : Ordinal.{u}) : IsS5 (modelMany (Atom := Atom) a α) := by
  classical
  intro i
  by_cases hi : i = a
  · simpa only [modelMany, if_pos hi] using model_isS5 α true
  · simpa only [modelMany, if_neg hi] using model_isS5 α false

include hab

theorem stageMany_rel_selected (α β : Ordinal.{u}) (s t : World α) (i : Bool) :
    (stageMany (Atom := Atom) a α β).rel (if i then a else b) s t ↔
      (stage α β).rel i s t := by
  classical
  cases i <;> simp [stageMany, modelMany, stage, Ne.symm hab]

theorem stageMany_satisfies (α β : Ordinal.{u}) (χ : Formula Unit Bool) (s : World α) :
    (stageMany a α β).Satisfies s (χ.map (fun _ => p) (fun i => if i then a else b)) ↔
      (stage α β).Satisfies s χ := by
  induction χ generalizing s with
  | atom q => rfl
  | neg χ ih => exact not_congr (ih s)
  | conj χ ψ ihχ ihψ => exact and_congr (ihχ s) (ihψ s)
  | box i χ ih =>
      simp only [Formula.map, Model.satisfies_box, stageMany_rel_selected a b hab]
      apply forall_congr'; intro t
      exact imp_congr_right (fun _ => ih t)

theorem formulaMany_iff (α β : Ordinal.{u}) (s : World α) :
    (stageMany a α β).Satisfies s (formulaMany p a b) ↔ β < rank s := by
  exact (stageMany_satisfies p a b hab α β formula s).trans (formula_iff α β s)

theorem ordinalUpdate_modelMany (α β : Ordinal.{u}) :
    ordinalUpdate (modelMany a α) (formulaMany p a b) β = stageMany a α β := by
  induction β using Ordinal.induction with
  | h β ih =>
      apply Model.ext'
      · intro i s t
        rw [ordinalUpdate_rel_iff]
        have heval : (∀ γ < β, (ordinalUpdate (modelMany a α) (formulaMany p a b) γ).Satisfies t
            (formulaMany p a b)) ↔
            (∀ γ < β, (stageMany a α γ).Satisfies t (formulaMany p a b)) := by
          apply forall_congr'; intro γ
          apply forall_congr'; intro hγ
          rw [ih γ hγ]
        rw [heval]
        change ((modelMany a α).rel i s t ∧
          (∀ γ < β, (stageMany a α γ).Satisfies t (formulaMany p a b))) ↔
          (modelMany a α).rel i s t ∧ β ≤ rank t
        simp only [formulaMany_iff p a b hab, all_lt_iff_le]
      · intro q s
        exact ordinalUpdate_val (modelMany a α) (formulaMany p a b) β q s

theorem modelMany_stable_at (α : Ordinal.{u}) :
    BPALStable (modelMany a α) (formulaMany p a b) α := by
  unfold BPALStable
  rw [ordinalUpdate_modelMany p a b hab, ordinalUpdate_modelMany p a b hab]
  apply Model.ext'
  · intro i s t
    have hn : ¬ α ≤ rank t := not_le_of_gt (index_lt t.1)
    have hn' : ¬ Order.succ α ≤ rank t := fun h => hn (le_trans (Order.le_succ α) h)
    exact iff_of_false (fun h => hn' h.2) (fun h => hn h.2)
  · intro q s; rfl

theorem modelMany_not_stable_before (α β : Ordinal.{u}) (h : β < α) :
    ¬ BPALStable (modelMany a α) (formulaMany p a b) β := by
  intro heq
  obtain ⟨x, hx⟩ := exists_index h
  let s : World α := (x, [])
  have hrank : rank s = β := hx
  have href : (modelMany (Atom := Atom) a α).rel a s s :=
    (modelMany_isS5 a α a).1 s
  have hrel : (stageMany (Atom := Atom) a α β).rel a s s := ⟨href, hrank ▸ le_rfl⟩
  have heq' : stageMany (Atom := Atom) a α (Order.succ β) = stageMany a α β := by
    simpa only [BPALStable, ordinalUpdate_modelMany p a b hab] using heq
  have hrel' : (stageMany (Atom := Atom) a α (Order.succ β)).rel a s s := by rw [heq']; exact hrel
  have hbad : Order.succ β ≤ β := by simpa only [hrank] using hrel'.2
  exact not_le_of_gt (Order.lt_succ β) hbad

/-- The construction works for any atom and any two distinct agents. Other
agents receive one of the same S5 relations and do not occur in the formula. -/
theorem ranks_eq_many (α : Ordinal.{u}) :
    palRank (modelMany a α) (formulaMany p a b) = α ∧
      bpalRank (modelMany a α) (formulaMany p a b) = α := by
  have hB : bpalRank (modelMany a α) (formulaMany p a b) = α := by
    apply le_antisymm (bpalRank_le_of_stable _ _ (modelMany_stable_at p a b hab α))
    apply le_of_not_gt
    intro hlt
    exact modelMany_not_stable_before p a b hab α _ hlt (bpalRank_stable _ _)
  have hin : HasIncoming (modelMany (Atom := Atom) a α) :=
    fun s => ⟨a, s, (modelMany_isS5 a α a).1 s⟩
  exact ⟨(stabilization_rank_eq_of_incoming _ _ hin).trans hB, hB⟩

end ArbitraryAgents

end S5OrdinalWitness
end PropertiesOfPALAndBPALOperators
