import EventualAndStrongEventualNotionsInPublicAnnouncements.RichOrdinalConditions
import EventualAndStrongEventualNotionsInPublicAnnouncements.Main

/-!
# Semantic transport for the common-belief language

Equivalence on every K45 model commutes with genuine finite and ordinal
announcement iteration. This transports the basic witnesses into the rich
language and the single-agent reduction back into the basic language.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

namespace Rich

/-- Semantic equivalence on all K45 models in the world universe. -/
def Equivalent (φ : BPALCFormula Atom Agent) (ψ : Formula Atom Agent) : Prop :=
  ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
    M.rSatisfies x φ ↔ M.Satisfies x ψ

variable {φ : BPALCFormula Atom Agent} {ψ : Formula Atom Agent}

 theorem equivalent_update (h : Equivalent.{u} φ ψ)
    (M : Model World Atom Agent) (hM : IsK45 M) : M.rUpdate φ = M.update ψ := by
  apply Model.ext'
  · intro a x y
    exact and_congr Iff.rfl (h M hM y)
  · intro p x
    rfl

theorem equivalent_iterate (h : Equivalent.{u} φ ψ)
    (M : Model World Atom Agent) (hM : IsK45 M) (n : Nat) :
    M.rIterateUpdate φ n = M.iterateUpdate ψ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Model.rIterateUpdate_succ, equivalent_update h _
        (Model.rIterateUpdate_isK45 hM φ n), ih, Model.iterateUpdate_succ]

theorem equivalent_trace (h : Equivalent.{u} φ ψ)
    (M : Model World Atom Agent) (hM : IsK45 M) (x : World) (n : Nat) :
    M.rTrace x φ n ↔ M.trace x ψ n := by
  unfold Model.rTrace Model.trace
  rw [equivalent_iterate h M hM n]
  exact h _ (Model.iterateUpdate_isK45 hM ψ n) x

theorem equivalent_common (h : Equivalent.{u} φ ψ)
    (M : Model World Atom Agent) (hM : IsK45 M) (x : World) :
    Common M x φ ↔ EventualAndStrongEventualNotionsInPublicAnnouncements.Common M x ψ := by
  unfold Common EventualAndStrongEventualNotionsInPublicAnnouncements.Common
  exact forall_congr' fun y => imp_congr_right fun _ => h M hM y

theorem equivalent_ordinalUpdate (h : Equivalent.{u} φ ψ)
    (M : Model World Atom Agent) (hM : IsK45 M) (α : Ordinal.{max u w}) :
    ordinalUpdate M φ α =
      EventualAndStrongEventualNotionsInPublicAnnouncements.ordinalUpdate M ψ α := by
  induction α using Ordinal.induction with
  | h α ih =>
      apply Model.ext'
      · intro a x y
        rw [ordinalUpdate_rel_iff,
          EventualAndStrongEventualNotionsInPublicAnnouncements.ordinalUpdate_rel_iff]
        apply and_congr Iff.rfl
        exact forall_congr' fun β => imp_congr_right fun hβ => by
          rw [ih β hβ]
          exact h _
            (EventualAndStrongEventualNotionsInPublicAnnouncements.ordinalUpdate_isK45 M ψ hM β) y
      · intro p x
        rw [ordinalUpdate_val,
          EventualAndStrongEventualNotionsInPublicAnnouncements.ordinalUpdate_val]

theorem equivalent_ordinalTruth (h : Equivalent.{u} φ ψ)
    (M : Model World Atom Agent) (hM : IsK45 M) (x : World)
    (α : Ordinal.{max u w}) :
    (ordinalUpdate M φ α).rSatisfies x φ ↔
      (EventualAndStrongEventualNotionsInPublicAnnouncements.ordinalUpdate M ψ α).Satisfies x ψ := by
  rw [equivalent_ordinalUpdate h M hM α]
  exact h _
    (EventualAndStrongEventualNotionsInPublicAnnouncements.ordinalUpdate_isK45 M ψ hM α) x

theorem equivalent_eventual (h : Equivalent.{u} φ ψ) (i j : Bool) :
    Eventual.{u} i j φ ↔
      EventualAndStrongEventualNotionsInPublicAnnouncements.Eventual.{u} i j ψ := by
  unfold Eventual EventualAndStrongEventualNotionsInPublicAnnouncements.Eventual
  refine forall_congr' fun W => forall_congr' fun M => imp_congr_right fun hM => ?_
  simp only [h M hM, equivalent_trace h M hM]

theorem equivalent_strongEventual (h : Equivalent.{u} φ ψ) (i j : Bool) :
    StrongEventual.{u} i j φ ↔
      EventualAndStrongEventualNotionsInPublicAnnouncements.StrongEventual.{u} i j ψ := by
  unfold StrongEventual EventualAndStrongEventualNotionsInPublicAnnouncements.StrongEventual
  refine forall_congr' fun W => forall_congr' fun M => imp_congr_right fun hM => ?_
  simp only [h M hM, equivalent_trace h M hM]

theorem equivalent_ordinalEventual (h : Equivalent.{u} φ ψ) (i j : Bool) :
    OrdinalEventual.{u} i j φ ↔
      EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalEventual.{u} i j ψ := by
  unfold OrdinalEventual EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalEventual
  refine forall_congr' fun W => forall_congr' fun M => imp_congr_right fun hM => ?_
  simp only [h M hM, equivalent_ordinalTruth h M hM]

theorem equivalent_ordinalStrongEventual (h : Equivalent.{u} φ ψ) (i j : Bool) :
    OrdinalStrongEventual.{u} i j φ ↔
      EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalStrongEventual.{u} i j ψ := by
  unfold OrdinalStrongEventual EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalStrongEventual
  refine forall_congr' fun W => forall_congr' fun M => imp_congr_right fun hM => ?_
  simp only [h M hM, equivalent_ordinalTruth h M hM]

theorem equivalent_ordinalStageCondition (h : Equivalent.{u} φ ψ) (i j : Bool) :
    OrdinalStageCondition.{u} i j φ ↔
      EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalStageCondition.{u} i j ψ := by
  unfold OrdinalStageCondition EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalStageCondition
  refine forall_congr' fun W => forall_congr' fun M => imp_congr_right fun hM => ?_
  simp only [h M hM]
  refine forall_congr' fun x => imp_congr_right fun _ => forall_congr' fun α => ?_
  rw [equivalent_ordinalUpdate h M hM α]
  have hα := EventualAndStrongEventualNotionsInPublicAnnouncements.ordinalUpdate_isK45 M ψ hM α
  rw [equivalent_common h _ hα x, h _ hα x]

theorem equivalent_finiteStageCondition (h : Equivalent.{u} φ ψ) (i j : Bool) :
    FiniteStageCondition.{u} i j φ ↔
      EventualAndStrongEventualNotionsInPublicAnnouncements.FiniteStageCondition.{u} i j ψ := by
  unfold FiniteStageCondition StageCondition
    EventualAndStrongEventualNotionsInPublicAnnouncements.FiniteStageCondition
    EventualAndStrongEventualNotionsInPublicAnnouncements.StageCondition
  refine forall_congr' fun k => forall_congr' fun W => forall_congr' fun M =>
    imp_congr_right fun hM => ?_
  simp only [h M hM, equivalent_trace h M hM, equivalent_iterate h M hM,
    equivalent_common h _ (Model.iterateUpdate_isK45 hM ψ k)]

 theorem equivalent_uniformBound (h : Equivalent.{u} φ ψ) (i j : Bool) :
    UniformBound.{u} i j φ ↔
      EventualAndStrongEventualNotionsInPublicAnnouncements.UniformBound.{u} i j ψ := by
  unfold UniformBound EventualAndStrongEventualNotionsInPublicAnnouncements.UniformBound
  refine exists_congr fun N => and_congr Iff.rfl ?_
  refine forall_congr' fun W => forall_congr' fun M => imp_congr_right fun hM => ?_
  simp only [h M hM, equivalent_trace h M hM]

 theorem equivalent_uniformExtinction (h : Equivalent.{u} φ ψ) :
    UniformExtinction.{u} φ ↔
      EventualAndStrongEventualNotionsInPublicAnnouncements.UniformExtinction.{u} ψ := by
  unfold UniformExtinction EventualAndStrongEventualNotionsInPublicAnnouncements.UniformExtinction
  refine exists_congr fun N => and_congr Iff.rfl ?_
  refine forall_congr' fun W => forall_congr' fun M => imp_congr_right fun hM => ?_
  simp only [equivalent_trace h M hM, equivalent_iterate h M hM,
    Edgeless, EventualAndStrongEventualNotionsInPublicAnnouncements.Edgeless]

/-- Every basic formula is a rich formula with identical truth and dynamics. -/
theorem ofFormula_equivalent (ψ : Formula Atom Agent) :
    Equivalent.{u} (BPALCFormula.ofFormula ψ) ψ :=
  fun M _ x => BPALC.initiallySatisfies_ofFormula M x ψ

/-- With one agent, every rich formula has a semantically equivalent basic one. -/
theorem singleAgent_equivalent [Subsingleton Agent] (a : Agent)
    (φ : BPALCFormula Atom Agent) : Equivalent.{u} φ (φ.toFormula a) :=
  fun M hM x => BPALC.initiallySatisfies_toFormula M hM a x φ

end Rich
end EventualAndStrongEventualNotionsInPublicAnnouncements
