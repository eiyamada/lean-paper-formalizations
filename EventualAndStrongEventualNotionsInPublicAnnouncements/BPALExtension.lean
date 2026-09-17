import EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalConditions
import ClassificationSigmaValidity.Expressivity

/-!
# Extension to nested believed-announcement formulas

The update below evaluates the BPAL formula itself. Its finite and ordinal
iterations coincide with those of the recursively eliminated basic formula.
Thus all six classifications transport to BPAL, as stated in Remark 1.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

def bpalUpdate (M : Model World Atom Agent) (φ : BPALFormula Atom Agent) :
    Model World Atom Agent where
  rel a x y := M.rel a x y ∧ BPAL.InitiallySatisfies M y φ
  val := M.val

theorem bpalUpdate_eq (M : Model World Atom Agent) (φ : BPALFormula Atom Agent) :
    bpalUpdate M φ = M.update φ.toFormula := by
  apply Model.ext'
  · intro a x y
    exact and_congr Iff.rfl (BPAL.initiallySatisfies_toFormula M y φ)
  · intro p x
    rfl

def bpalIterate (M : Model World Atom Agent) (φ : BPALFormula Atom Agent) :
    Nat → Model World Atom Agent
  | 0 => M
  | n + 1 => bpalUpdate (bpalIterate M φ n) φ

@[simp] theorem bpalIterate_eq (M : Model World Atom Agent)
    (φ : BPALFormula Atom Agent) (n : Nat) :
    bpalIterate M φ n = M.iterateUpdate φ.toFormula n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bpalIterate, bpalUpdate_eq, ih, Model.iterateUpdate_succ]

def bpalOrdinalUpdate (M : Model World Atom Agent) (φ : BPALFormula Atom Agent)
    (α : Ordinal.{max u w}) : Model World Atom Agent :=
  { rel := fun a x y => M.rel a x y ∧ ∀ β, β < α →
      BPAL.InitiallySatisfies (bpalOrdinalUpdate M φ β) y φ
    val := M.val }
termination_by α
decreasing_by assumption

@[simp] theorem bpalOrdinalUpdate_eq (M : Model World Atom Agent)
    (φ : BPALFormula Atom Agent) (α : Ordinal.{max u w}) :
    bpalOrdinalUpdate M φ α = ordinalUpdate M φ.toFormula α := by
  induction α using Ordinal.induction with
  | h α ih =>
    apply Model.ext'
    · intro a x y
      rw [bpalOrdinalUpdate, ordinalUpdate_rel_iff]
      apply and_congr Iff.rfl
      exact forall_congr' fun β => imp_congr_right fun hβ => by
        rw [ih β hβ, BPAL.initiallySatisfies_toFormula]
    · intro p x
      rw [bpalOrdinalUpdate, ordinalUpdate_val]

def bpalCommon (M : Model World Atom Agent) (x : World)
    (φ : BPALFormula Atom Agent) : Prop :=
  ∀ y, Relation.TransGen M.AnyStep x y → BPAL.InitiallySatisfies M y φ

@[simp] theorem bpalCommon_iff (M : Model World Atom Agent) (x : World)
    (φ : BPALFormula Atom Agent) : bpalCommon M x φ ↔ Common M x φ.toFormula := by
  simp only [bpalCommon, Common, BPAL.initiallySatisfies_toFormula]

def BPALEventual (i j : Bool) (φ : BPALFormula Atom Agent) : Prop :=
  ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (BPAL.InitiallySatisfies M x φ) → ∃ n : Nat, 1 ≤ n ∧
      HoldsBit j (BPAL.InitiallySatisfies (bpalIterate M φ n) x φ)

def BPALStrongEventual (i j : Bool) (φ : BPALFormula Atom Agent) : Prop :=
  ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (BPAL.InitiallySatisfies M x φ) → ∃ N : Nat, 1 ≤ N ∧
      ∀ n, N ≤ n → HoldsBit j (BPAL.InitiallySatisfies (bpalIterate M φ n) x φ)

def BPALFiniteStageCondition (i j : Bool) (φ : BPALFormula Atom Agent) : Prop :=
  ∀ k : Nat, ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (BPAL.InitiallySatisfies M x φ) → bpalCommon (bpalIterate M φ k) x φ →
      HoldsBit j (BPAL.InitiallySatisfies (bpalIterate M φ k) x φ)

def BPALOrdinalEventual (i j : Bool) (φ : BPALFormula Atom Agent) : Prop :=
  ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (BPAL.InitiallySatisfies M x φ) → ∃ α : Ordinal.{max u w}, 0 < α ∧
      HoldsBit j (BPAL.InitiallySatisfies (bpalOrdinalUpdate M φ α) x φ)

def BPALOrdinalStrongEventual (i j : Bool) (φ : BPALFormula Atom Agent) : Prop :=
  ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (BPAL.InitiallySatisfies M x φ) → ∃ α : Ordinal.{max u w}, 0 < α ∧
      ∀ β, α ≤ β → HoldsBit j (BPAL.InitiallySatisfies (bpalOrdinalUpdate M φ β) x φ)

def BPALOrdinalStageCondition (i j : Bool) (φ : BPALFormula Atom Agent) : Prop :=
  ∀ {W : Type u} (M : Model W Atom Agent), IsK45 M → ∀ x,
    HoldsBit i (BPAL.InitiallySatisfies M x φ) → ∀ α : Ordinal.{max u w},
      bpalCommon (bpalOrdinalUpdate M φ α) x φ →
        HoldsBit j (BPAL.InitiallySatisfies (bpalOrdinalUpdate M φ α) x φ)

theorem bpal_eventual_iff (i j : Bool) (φ : BPALFormula Atom Agent) :
    BPALEventual.{u} i j φ ↔ Eventual.{u} i j φ.toFormula := by
  simp only [BPALEventual, Eventual, bpalIterate_eq,
    BPAL.initiallySatisfies_toFormula, Model.trace]

theorem bpal_strongEventual_iff (i j : Bool) (φ : BPALFormula Atom Agent) :
    BPALStrongEventual.{u} i j φ ↔ StrongEventual.{u} i j φ.toFormula := by
  simp only [BPALStrongEventual, StrongEventual, bpalIterate_eq,
    BPAL.initiallySatisfies_toFormula, Model.trace]

theorem bpal_finiteStageCondition_iff (i j : Bool) (φ : BPALFormula Atom Agent) :
    BPALFiniteStageCondition.{u} i j φ ↔ FiniteStageCondition.{u} i j φ.toFormula := by
  simp only [BPALFiniteStageCondition, FiniteStageCondition, StageCondition,
    bpalIterate_eq, bpalCommon_iff, BPAL.initiallySatisfies_toFormula, Model.trace]

theorem bpal_ordinalEventual_iff (i j : Bool) (φ : BPALFormula Atom Agent) :
    BPALOrdinalEventual.{u} i j φ ↔ OrdinalEventual.{u} i j φ.toFormula := by
  simp only [BPALOrdinalEventual, OrdinalEventual, bpalOrdinalUpdate_eq,
    BPAL.initiallySatisfies_toFormula]

theorem bpal_ordinalStrongEventual_iff (i j : Bool) (φ : BPALFormula Atom Agent) :
    BPALOrdinalStrongEventual.{u} i j φ ↔ OrdinalStrongEventual.{u} i j φ.toFormula := by
  simp only [BPALOrdinalStrongEventual, OrdinalStrongEventual, bpalOrdinalUpdate_eq,
    BPAL.initiallySatisfies_toFormula]

theorem bpal_ordinalStageCondition_iff (i j : Bool) (φ : BPALFormula Atom Agent) :
    BPALOrdinalStageCondition.{u} i j φ ↔ OrdinalStageCondition.{u} i j φ.toFormula := by
  simp only [BPALOrdinalStageCondition, OrdinalStageCondition, bpalOrdinalUpdate_eq,
    bpalCommon_iff, BPAL.initiallySatisfies_toFormula]

end EventualAndStrongEventualNotionsInPublicAnnouncements
