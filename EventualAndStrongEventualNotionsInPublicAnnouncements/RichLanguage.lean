import EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalDynamics
import ClassificationSigmaValidity.Expressivity

/-!
# Common belief and nested believed announcements

Common belief is interpreted by positive transitive closure, including inside
announcements. With one agent on K45 frames it reduces to ordinary belief.
The recursive elimination theorem below covers arbitrary nesting of common
belief and believed announcements, not only common belief of basic formulas.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity

universe u v w

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- The basic epistemic language extended by common belief. -/
inductive CommonFormula (Atom : Type v) (Agent : Type w) where
  | atom : Atom → CommonFormula Atom Agent
  | neg : CommonFormula Atom Agent → CommonFormula Atom Agent
  | conj : CommonFormula Atom Agent → CommonFormula Atom Agent → CommonFormula Atom Agent
  | box : Agent → CommonFormula Atom Agent → CommonFormula Atom Agent
  | common : CommonFormula Atom Agent → CommonFormula Atom Agent
  deriving DecidableEq, Repr

/-- Believed public-announcement logic with common belief. -/
inductive BPALCFormula (Atom : Type v) (Agent : Type w) where
  | atom : Atom → BPALCFormula Atom Agent
  | neg : BPALCFormula Atom Agent → BPALCFormula Atom Agent
  | conj : BPALCFormula Atom Agent → BPALCFormula Atom Agent → BPALCFormula Atom Agent
  | box : Agent → BPALCFormula Atom Agent → BPALCFormula Atom Agent
  | common : BPALCFormula Atom Agent → BPALCFormula Atom Agent
  | announce : BPALCFormula Atom Agent → BPALCFormula Atom Agent → BPALCFormula Atom Agent
  deriving DecidableEq, Repr

namespace BPALC

/-- Evaluation at the currently retained arrows; announcements restrict targets
using this same recursive semantics. -/
def Satisfies (M : Model World Atom Agent) :
    (Agent → World → World → Prop) → World → BPALCFormula Atom Agent → Prop
  | _, x, .atom p => M.val p x
  | R, x, .neg φ => ¬ Satisfies M R x φ
  | R, x, .conj φ ψ => Satisfies M R x φ ∧ Satisfies M R x ψ
  | R, x, .box a φ => ∀ y, R a x y → Satisfies M R y φ
  | R, x, .common φ =>
      ∀ y, Relation.TransGen (fun s t => ∃ a, R a s t) x y → Satisfies M R y φ
  | R, x, .announce φ ψ =>
      Satisfies M (fun a y z => R a y z ∧ Satisfies M R z φ) x ψ

def InitiallySatisfies (M : Model World Atom Agent) (x : World)
    (φ : BPALCFormula Atom Agent) : Prop := Satisfies M M.rel x φ

end BPALC

namespace CommonFormula

/-- Embed the language with common belief into the dynamic language. -/
def toBPALC : CommonFormula Atom Agent → BPALCFormula Atom Agent
  | .atom p => .atom p
  | .neg φ => .neg φ.toBPALC
  | .conj φ ψ => .conj φ.toBPALC ψ.toBPALC
  | .box a φ => .box a φ.toBPALC
  | .common φ => .common φ.toBPALC

def Satisfies (M : Model World Atom Agent) (x : World)
    (φ : CommonFormula Atom Agent) : Prop :=
  BPALC.InitiallySatisfies M x φ.toBPALC

@[simp] theorem satisfies_common (M : Model World Atom Agent) (x : World)
    (φ : CommonFormula Atom Agent) :
    Satisfies M x (.common φ) ↔
      ∀ y, Relation.TransGen M.AnyStep x y → Satisfies M y φ := Iff.rfl

end CommonFormula

namespace BPALCFormula

/-- Embed a basic formula without changing its modalities. -/
def ofFormula : Formula Atom Agent → BPALCFormula Atom Agent
  | .atom p => .atom p
  | .neg φ => .neg (ofFormula φ)
  | .conj φ ψ => .conj (ofFormula φ) (ofFormula ψ)
  | .box a φ => .box a (ofFormula φ)

/-- Eliminate common belief and announcements in the single-agent setting.
Correctness requires all agents to equal the displayed agent `a`. -/
def toFormula (a : Agent) : BPALCFormula Atom Agent → Formula Atom Agent
  | .atom p => .atom p
  | .neg φ => .neg (toFormula a φ)
  | .conj φ ψ => .conj (toFormula a φ) (toFormula a ψ)
  | .box b φ => .box b (toFormula a φ)
  | .common φ => .box a (toFormula a φ)
  | .announce φ ψ => Formula.announcementReduce (toFormula a φ) (toFormula a ψ)

@[simp] theorem toFormula_ofFormula (a : Agent) (φ : Formula Atom Agent) :
    toFormula a (ofFormula φ) = φ := by
  induction φ with
  | atom p => rfl
  | neg φ ih => simp only [ofFormula, toFormula, ih]
  | conj φ ψ ihφ ihψ => simp only [ofFormula, toFormula, ihφ, ihψ]
  | box b φ ih => simp only [ofFormula, toFormula, ih]

end BPALCFormula

private theorem rich_singleAgent_positive_path [Subsingleton Agent]
    {M : Model World Atom Agent} (hM : IsK45 M) (a : Agent) {x y : World}
    (h : Relation.TransGen M.AnyStep x y) : M.rel a x y := by
  apply Relation.transGen_minimal (r' := M.rel a) ?_ ?_ h
  · intro s t z hst htz
    exact (hM a).1 hst htz
  · intro s t hst
    obtain ⟨b, hb⟩ := hst
    simpa only [Subsingleton.elim b a] using hb

/-- Common belief collapses to the sole belief modality on single-agent K45. -/
theorem singleAgent_common_iff_box [Subsingleton Agent]
    (M : Model World Atom Agent) (hM : IsK45 M) (a : Agent)
    (x : World) (φ : Formula Atom Agent) :
    Common M x φ ↔ M.Satisfies x (.box a φ) := by
  constructor
  · intro h y hy
    exact h y (Relation.TransGen.single ⟨a, hy⟩)
  · intro h y hy
    exact h y (rich_singleAgent_positive_path hM a hy)

namespace BPALC

/-- Semantic preservation of the basic-language embedding on every frame. -/
theorem satisfies_ofFormula (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    ∀ (R : Agent → World → World → Prop) (x : World),
      Satisfies M R x (BPALCFormula.ofFormula φ) ↔
        (BPAL.relationModel M R).Satisfies x φ := by
  induction φ with
  | atom p => intro R x; rfl
  | neg φ ih =>
      intro R x
      exact not_congr (ih R x)
  | conj φ ψ ihφ ihψ =>
      intro R x
      exact and_congr (ihφ R x) (ihψ R x)
  | box a φ ih =>
      intro R x
      exact forall_congr' fun y => imp_congr_right fun _ => ih R y

@[simp] theorem initiallySatisfies_ofFormula (M : Model World Atom Agent)
    (x : World) (φ : Formula Atom Agent) :
    InitiallySatisfies M x (BPALCFormula.ofFormula φ) ↔ M.Satisfies x φ := by
  rw [InitiallySatisfies, satisfies_ofFormula, BPAL.relationModel_rel_self]

/-- Elimination of arbitrary nested common belief and announcements, at any
current relation satisfying K45. The announcement case establishes K45 of its
new relation before applying the induction hypothesis. -/
theorem satisfies_toFormula [Subsingleton Agent] (M : Model World Atom Agent)
    (a : Agent) (φ : BPALCFormula Atom Agent) :
    ∀ (R : Agent → World → World → Prop), IsK45 (BPAL.relationModel M R) →
      ∀ x, Satisfies M R x φ ↔
        (BPAL.relationModel M R).Satisfies x (φ.toFormula a) := by
  induction φ with
  | atom p => intro R hR x; rfl
  | neg φ ih =>
      intro R hR x
      exact not_congr (ih R hR x)
  | conj φ ψ ihφ ihψ =>
      intro R hR x
      exact and_congr (ihφ R hR x) (ihψ R hR x)
  | box b φ ih =>
      intro R hR x
      exact forall_congr' fun y => imp_congr_right fun _ => ih R hR y
  | common φ ih =>
      intro R hR x
      change (∀ y, Relation.TransGen (BPAL.relationModel M R).AnyStep x y →
        Satisfies M R y φ) ↔
        (∀ y, R a x y → (BPAL.relationModel M R).Satisfies y (φ.toFormula a))
      constructor
      · intro h y hy
        exact (ih R hR y).mp (h y (Relation.TransGen.single ⟨a, hy⟩))
      · intro h y hy
        exact (ih R hR y).mpr (h y (rich_singleAgent_positive_path hR a hy))
  | announce φ ψ ihφ ihψ =>
      intro R hR x
      let nextRel : Agent → World → World → Prop :=
        fun b y z => R b y z ∧ Satisfies M R z φ
      have hUpdate : BPAL.relationModel M nextRel =
          (BPAL.relationModel M R).update (φ.toFormula a) := by
        apply Model.ext'
        · intro b y z
          exact and_congr Iff.rfl (ihφ R hR z)
        · intro p y
          rfl
      have hnext : IsK45 (BPAL.relationModel M nextRel) := by
        rw [hUpdate]
        exact Model.update_isK45 hR (φ.toFormula a)
      change Satisfies M nextRel x ψ ↔
        (BPAL.relationModel M R).Satisfies x
          (Formula.announcementReduce (φ.toFormula a) (ψ.toFormula a))
      rw [ihψ nextRel hnext x, hUpdate]
      exact Model.satisfies_announcementReduce _ x (φ.toFormula a) (ψ.toFormula a)

/-- Remark 1, single-agent expressive reduction including common belief. -/
theorem initiallySatisfies_toFormula [Subsingleton Agent]
    (M : Model World Atom Agent) (hM : IsK45 M) (a : Agent)
    (x : World) (φ : BPALCFormula Atom Agent) :
    InitiallySatisfies M x φ ↔ M.Satisfies x (φ.toFormula a) := by
  have hR : IsK45 (BPAL.relationModel M M.rel) := by
    simpa only [BPAL.relationModel_rel_self] using hM
  simpa only [InitiallySatisfies, BPAL.relationModel_rel_self] using
    satisfies_toFormula M a φ M.rel hR x

theorem singleAgent_equiexpressive_with_basic [Subsingleton Agent] (a : Agent) :
    (∀ φ : BPALCFormula Atom Agent, ∃ ψ : Formula Atom Agent,
      ∀ (W : Type u) (M : Model W Atom Agent), IsK45 M → ∀ x,
        InitiallySatisfies M x φ ↔ M.Satisfies x ψ) ∧
    (∀ ψ : Formula Atom Agent, ∃ φ : BPALCFormula Atom Agent,
      ∀ (W : Type u) (M : Model W Atom Agent), IsK45 M → ∀ x,
        M.Satisfies x ψ ↔ InitiallySatisfies M x φ) := by
  constructor
  · intro φ
    exact ⟨φ.toFormula a, fun _ M hM x => initiallySatisfies_toFormula M hM a x φ⟩
  · intro ψ
    exact ⟨BPALCFormula.ofFormula ψ, fun _ M _ x =>
      (initiallySatisfies_ofFormula M x ψ).symm⟩

/-- The genuine update by a formula containing common belief and announcements. -/
def update (M : Model World Atom Agent) (φ : BPALCFormula Atom Agent) :
    Model World Atom Agent where
  rel a x y := M.rel a x y ∧ InitiallySatisfies M y φ
  val := M.val

/-- Target restriction preserves K45 for arbitrary rich-language formulas. -/
theorem update_isK45 (M : Model World Atom Agent) (hM : IsK45 M)
    (φ : BPALCFormula Atom Agent) : IsK45 (update M φ) := by
  intro a
  exact ⟨fun hxy hyz => ⟨(hM a).1 hxy.1 hyz.1, hyz.2⟩,
    fun hxy hxz => ⟨(hM a).2 hxy.1 hxz.1, hxz.2⟩⟩

theorem update_eq [Subsingleton Agent] (M : Model World Atom Agent)
    (hM : IsK45 M) (a : Agent) (φ : BPALCFormula Atom Agent) :
    update M φ = M.update (φ.toFormula a) := by
  apply Model.ext'
  · intro b x y
    exact and_congr Iff.rfl (initiallySatisfies_toFormula M hM a y φ)
  · intro p x
    rfl

def iterate (M : Model World Atom Agent) (φ : BPALCFormula Atom Agent) :
    Nat → Model World Atom Agent
  | 0 => M
  | n + 1 => update (iterate M φ n) φ

theorem iterate_isK45 (M : Model World Atom Agent) (hM : IsK45 M)
    (φ : BPALCFormula Atom Agent) (n : Nat) : IsK45 (iterate M φ n) := by
  induction n with
  | zero => exact hM
  | succ n ih => exact update_isK45 _ ih φ

theorem iterate_eq [Subsingleton Agent] (M : Model World Atom Agent)
    (hM : IsK45 M) (a : Agent) (φ : BPALCFormula Atom Agent) (n : Nat) :
    iterate M φ n = M.iterateUpdate (φ.toFormula a) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate, update_eq _ (iterate_isK45 M hM φ n) a, ih,
        Model.iterateUpdate_succ]

/-- Transfinite iteration evaluates the rich announcement itself at every
earlier stage, without presupposing its single-agent reduction. -/
def ordinalIterate (M : Model World Atom Agent) (φ : BPALCFormula Atom Agent)
    (α : Ordinal.{max u w}) : Model World Atom Agent :=
  { rel := fun a x y => M.rel a x y ∧ ∀ β < α,
      InitiallySatisfies (ordinalIterate M φ β) y φ
    val := M.val }
termination_by α

theorem ordinalIterate_isK45 (M : Model World Atom Agent) (hM : IsK45 M)
    (φ : BPALCFormula Atom Agent) (α : Ordinal.{max u w}) :
    IsK45 (ordinalIterate M φ α) := by
  rw [ordinalIterate]
  intro a
  exact ⟨fun hxy hyz => ⟨(hM a).1 hxy.1 hyz.1, hyz.2⟩,
    fun hxy hxz => ⟨(hM a).2 hxy.1 hxz.1, hxz.2⟩⟩

/-- Single-agent elimination preserves the entire ordinal announcement run. -/
theorem ordinalIterate_eq [Subsingleton Agent] (M : Model World Atom Agent)
    (hM : IsK45 M) (a : Agent) (φ : BPALCFormula Atom Agent)
    (α : Ordinal.{max u w}) :
    ordinalIterate M φ α = ordinalUpdate M (φ.toFormula a) α := by
  induction α using Ordinal.induction with
  | h α ih =>
    apply Model.ext'
    · intro b x y
      rw [ordinalIterate, ordinalUpdate_rel_iff]
      apply and_congr Iff.rfl
      exact forall_congr' fun β => imp_congr_right fun hβ => by
        rw [ih β hβ]
        exact initiallySatisfies_toFormula _
          (ordinalUpdate_isK45 M (φ.toFormula a) hM β) a y φ
    · intro p x
      rw [ordinalIterate, ordinalUpdate_val]

theorem ordinalIterate_satisfies_iff [Subsingleton Agent]
    (M : Model World Atom Agent) (hM : IsK45 M) (a : Agent)
    (φ ψ : BPALCFormula Atom Agent) (α : Ordinal.{max u w}) (x : World) :
    InitiallySatisfies (ordinalIterate M φ α) x ψ ↔
      (ordinalUpdate M (φ.toFormula a) α).Satisfies x (ψ.toFormula a) := by
  rw [ordinalIterate_eq M hM a]
  exact initiallySatisfies_toFormula _
    (ordinalUpdate_isK45 M (φ.toFormula a) hM α) a x ψ

end BPALC

namespace CommonFormula

def toFormula (a : Agent) (φ : CommonFormula Atom Agent) : Formula Atom Agent :=
  φ.toBPALC.toFormula a

theorem satisfies_toFormula [Subsingleton Agent] (M : Model World Atom Agent)
    (hM : IsK45 M) (a : Agent) (x : World) (φ : CommonFormula Atom Agent) :
    Satisfies M x φ ↔ M.Satisfies x (φ.toFormula a) :=
  BPALC.initiallySatisfies_toFormula M hM a x φ.toBPALC

end CommonFormula

end EventualAndStrongEventualNotionsInPublicAnnouncements
