import EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalConditions
import ClassificationSigmaValidity.Diagonal

/-!
# Renaming atoms and agents

Every global eventual and common-belief condition is preserved when atoms and
agents are renamed. If both renamings have left inverses, all six conditions
are equivalent before and after renaming. This permits the concrete witnesses
to be used in any language containing their atoms and agents.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity

universe u

variable {Atom Agent Atom' Agent' : Type}

/-- Pulling back the accessibility relations can only remove available paths. -/
theorem common_reindex {World : Type u} (M : Model World Atom' Agent')
    (f : Atom → Atom') (g : Agent → Agent') (φ : Formula Atom Agent)
    {x : World} (h : Common M x (φ.map f g)) :
    Common (M.reindex f g) x φ := by
  intro y hy
  apply (M.reindex_satisfies_map f g y φ).mpr
  apply h y
  exact Relation.TransGen.mono (fun _ _ ⟨a, ha⟩ => ⟨g a, ha⟩) hy

/-- Renaming commutes with every ordinal announcement stage. -/
theorem ordinalUpdate_reindex {World : Type u} (M : Model World Atom' Agent')
    (f : Atom → Atom') (g : Agent → Agent') (φ : Formula Atom Agent)
    (α : Ordinal.{u}) :
    ordinalUpdate (M.reindex f g) φ α =
      (ordinalUpdate M (φ.map f g) α).reindex f g := by
  induction α using Ordinal.induction with
  | h α ih =>
    apply Model.ext'
    · intro a x y
      simp only [ordinalUpdate_rel_iff, Model.reindex_rel]
      constructor
      · rintro ⟨ha, h⟩
        refine ⟨ha, fun β hβ => ?_⟩
        have hv := h β hβ
        rw [ih β hβ] at hv
        exact (Model.reindex_satisfies_map _ f g y φ).mp hv
      · rintro ⟨ha, h⟩
        refine ⟨ha, fun β hβ => ?_⟩
        rw [ih β hβ]
        exact (Model.reindex_satisfies_map _ f g y φ).mpr (h β hβ)
    · intro p x
      simp only [ordinalUpdate_val, Model.reindex_val]

theorem ordinalUpdate_reindex_satisfies_map {World : Type u}
    (M : Model World Atom' Agent') (f : Atom → Atom') (g : Agent → Agent')
    (φ ψ : Formula Atom Agent) (α : Ordinal.{u}) (x : World) :
    (ordinalUpdate (M.reindex f g) φ α).Satisfies x ψ ↔
      (ordinalUpdate M (φ.map f g) α).Satisfies x (ψ.map f g) := by
  rw [ordinalUpdate_reindex]
  exact Model.reindex_satisfies_map _ f g x ψ

/-- Global eventuality is preserved even by noninjective renamings. -/
theorem eventual_map {i j : Bool} {φ : Formula Atom Agent}
    (h : Eventual.{u} i j φ) (f : Atom → Atom') (g : Agent → Agent') :
    Eventual.{u} i j (φ.map f g) := by
  intro World M hM x hx
  have hx' := (holdsBit_congr i (M.reindex_satisfies_map f g x φ)).mpr hx
  obtain ⟨n, hn, hv⟩ := h (M.reindex f g) (Model.reindex_isK45 hM f g) x hx'
  exact ⟨n, hn, (holdsBit_congr j (M.reindex_trace f g φ x n)).mp hv⟩

theorem strongEventual_map {i j : Bool} {φ : Formula Atom Agent}
    (h : StrongEventual.{u} i j φ) (f : Atom → Atom') (g : Agent → Agent') :
    StrongEventual.{u} i j (φ.map f g) := by
  intro World M hM x hx
  have hx' := (holdsBit_congr i (M.reindex_satisfies_map f g x φ)).mpr hx
  obtain ⟨N, hN, hv⟩ := h (M.reindex f g) (Model.reindex_isK45 hM f g) x hx'
  exact ⟨N, hN, fun n hn =>
    (holdsBit_congr j (M.reindex_trace f g φ x n)).mp (hv n hn)⟩

theorem stageCondition_map {i j : Bool} {k : Nat} {φ : Formula Atom Agent}
    (h : StageCondition.{u} i j k φ) (f : Atom → Atom') (g : Agent → Agent') :
    StageCondition.{u} i j k (φ.map f g) := by
  intro World M hM x hx hC
  have hx' := (holdsBit_congr i (M.reindex_satisfies_map f g x φ)).mpr hx
  have hC' := common_reindex (M.iterateUpdate (φ.map f g) k) f g φ hC
  rw [← M.reindex_iterateUpdate f g φ k] at hC'
  exact (holdsBit_congr j (M.reindex_trace f g φ x k)).mp
    (h (M.reindex f g) (Model.reindex_isK45 hM f g) x hx' hC')

theorem finiteStageCondition_map {i j : Bool} {φ : Formula Atom Agent}
    (h : FiniteStageCondition.{u} i j φ) (f : Atom → Atom') (g : Agent → Agent') :
    FiniteStageCondition.{u} i j (φ.map f g) :=
  fun k => stageCondition_map (h k) f g

theorem ordinalEventual_map {i j : Bool} {φ : Formula Atom Agent}
    (h : OrdinalEventual.{u} i j φ) (f : Atom → Atom') (g : Agent → Agent') :
    OrdinalEventual.{u} i j (φ.map f g) := by
  intro World M hM x hx
  have hx' := (holdsBit_congr i (M.reindex_satisfies_map f g x φ)).mpr hx
  obtain ⟨α, hα, hv⟩ := h (M.reindex f g) (Model.reindex_isK45 hM f g) x hx'
  exact ⟨α, hα,
    (holdsBit_congr j (ordinalUpdate_reindex_satisfies_map M f g φ φ α x)).mp hv⟩

theorem ordinalStrongEventual_map {i j : Bool} {φ : Formula Atom Agent}
    (h : OrdinalStrongEventual.{u} i j φ) (f : Atom → Atom') (g : Agent → Agent') :
    OrdinalStrongEventual.{u} i j (φ.map f g) := by
  intro World M hM x hx
  have hx' := (holdsBit_congr i (M.reindex_satisfies_map f g x φ)).mpr hx
  obtain ⟨α, hα, hv⟩ := h (M.reindex f g) (Model.reindex_isK45 hM f g) x hx'
  exact ⟨α, hα, fun β hβ =>
    (holdsBit_congr j (ordinalUpdate_reindex_satisfies_map M f g φ φ β x)).mp
      (hv β hβ)⟩

theorem ordinalStageCondition_map {i j : Bool} {φ : Formula Atom Agent}
    (h : OrdinalStageCondition.{u} i j φ) (f : Atom → Atom') (g : Agent → Agent') :
    OrdinalStageCondition.{u} i j (φ.map f g) := by
  intro World M hM x hx α hC
  have hx' := (holdsBit_congr i (M.reindex_satisfies_map f g x φ)).mpr hx
  have hC' := common_reindex (ordinalUpdate M (φ.map f g) α) f g φ hC
  rw [← ordinalUpdate_reindex M f g φ α] at hC'
  exact (holdsBit_congr j (ordinalUpdate_reindex_satisfies_map M f g φ φ α x)).mp
    (h (M.reindex f g) (Model.reindex_isK45 hM f g) x hx' α hC')

/-- Left inverse maps recover a formula syntactically. -/
theorem formula_map_leftInverse (f : Atom → Atom') (g : Agent → Agent')
    (f' : Atom' → Atom) (g' : Agent' → Agent)
    (hf : Function.LeftInverse f' f) (hg : Function.LeftInverse g' g)
    (φ : Formula Atom Agent) : (φ.map f g).map f' g' = φ := by
  induction φ with
  | atom p => simp only [Formula.map, hf p]
  | neg φ ih => simp only [Formula.map, ih]
  | conj φ ψ ihφ ihψ => simp only [Formula.map, ihφ, ihψ]
  | box a φ ih => simp only [Formula.map, hg a, ih]

section LeftInverse

variable (f : Atom → Atom') (g : Agent → Agent')
  (f' : Atom' → Atom) (g' : Agent' → Agent)
  (hf : Function.LeftInverse f' f) (hg : Function.LeftInverse g' g)
  (i j : Bool) (φ : Formula Atom Agent)

include f' g' hf hg

theorem eventual_map_iff :
    Eventual.{u} i j (φ.map f g) ↔ Eventual.{u} i j φ := by
  constructor
  · intro h
    rw [← formula_map_leftInverse f g f' g' hf hg φ]
    exact eventual_map h f' g'
  · exact fun h => eventual_map h f g

theorem strongEventual_map_iff :
    StrongEventual.{u} i j (φ.map f g) ↔ StrongEventual.{u} i j φ := by
  constructor
  · intro h
    rw [← formula_map_leftInverse f g f' g' hf hg φ]
    exact strongEventual_map h f' g'
  · exact fun h => strongEventual_map h f g

theorem finiteStageCondition_map_iff :
    FiniteStageCondition.{u} i j (φ.map f g) ↔ FiniteStageCondition.{u} i j φ := by
  constructor
  · intro h
    rw [← formula_map_leftInverse f g f' g' hf hg φ]
    exact finiteStageCondition_map h f' g'
  · exact fun h => finiteStageCondition_map h f g

theorem ordinalEventual_map_iff :
    OrdinalEventual.{u} i j (φ.map f g) ↔ OrdinalEventual.{u} i j φ := by
  constructor
  · intro h
    rw [← formula_map_leftInverse f g f' g' hf hg φ]
    exact ordinalEventual_map h f' g'
  · exact fun h => ordinalEventual_map h f g

theorem ordinalStrongEventual_map_iff :
    OrdinalStrongEventual.{u} i j (φ.map f g) ↔ OrdinalStrongEventual.{u} i j φ := by
  constructor
  · intro h
    rw [← formula_map_leftInverse f g f' g' hf hg φ]
    exact ordinalStrongEventual_map h f' g'
  · exact fun h => ordinalStrongEventual_map h f g

theorem ordinalStageCondition_map_iff :
    OrdinalStageCondition.{u} i j (φ.map f g) ↔ OrdinalStageCondition.{u} i j φ := by
  constructor
  · intro h
    rw [← formula_map_leftInverse f g f' g' hf hg φ]
    exact ordinalStageCondition_map h f' g'
  · exact fun h => ordinalStageCondition_map h f g

end LeftInverse

section Injective

variable [Nonempty Atom] [Nonempty Agent]
  (f : Atom → Atom') (g : Agent → Agent')
  (hf : Function.Injective f) (hg : Function.Injective g)
  (i j : Bool) (φ : Formula Atom Agent)

include hf hg

/-- Injective language extensions preserve and reflect all six conditions. -/
theorem renaming_condition_equivalences :
    (Eventual.{u} i j (φ.map f g) ↔ Eventual.{u} i j φ) ∧
    (StrongEventual.{u} i j (φ.map f g) ↔ StrongEventual.{u} i j φ) ∧
    (FiniteStageCondition.{u} i j (φ.map f g) ↔ FiniteStageCondition.{u} i j φ) ∧
    (OrdinalEventual.{u} i j (φ.map f g) ↔ OrdinalEventual.{u} i j φ) ∧
    (OrdinalStrongEventual.{u} i j (φ.map f g) ↔ OrdinalStrongEventual.{u} i j φ) ∧
    (OrdinalStageCondition.{u} i j (φ.map f g) ↔ OrdinalStageCondition.{u} i j φ) :=
  let f' := Function.invFun f
  let g' := Function.invFun g
  let hf' := Function.leftInverse_invFun hf
  let hg' := Function.leftInverse_invFun hg
  ⟨eventual_map_iff f g f' g' hf' hg' i j φ,
    strongEventual_map_iff f g f' g' hf' hg' i j φ,
    finiteStageCondition_map_iff f g f' g' hf' hg' i j φ,
    ordinalEventual_map_iff f g f' g' hf' hg' i j φ,
    ordinalStrongEventual_map_iff f g f' g' hf' hg' i j φ,
    ordinalStageCondition_map_iff f g f' g' hf' hg' i j φ⟩

end Injective

end EventualAndStrongEventualNotionsInPublicAnnouncements
