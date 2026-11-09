import PropertiesOfPublicAnnouncementsAsOperators.Filtration
import EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalDynamics

/-!
# Common unknowability and extinction

Theorem 28 over K. Global conditions quantify over all world types in one
universe, including finite and empty types. The fresh predecessor in the
converse is essential: a singleton without arrows is already a BPAL zero.
-/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u v w

namespace Extinction

variable {World : Type u} {Atom : Type v} {Agent : Type w}

def CommonlyUnknowable (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent) x, ¬ (M.Satisfies x φ ∧ Common M x φ)

def CommonlyUnbelievable (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent) x, ¬ Common M x φ

def InformativeWhenTrue (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent) x,
    M.Satisfies x φ → ¬ GeneratedUnchanged M x φ

def OnlyZeroFixed (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent), M.update φ = M → Edgeless M

def OrdinalExtinction (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent),
    ∃ α : Ordinal.{max u w}, Edgeless (ordinalUpdate M φ α)

def FiniteExtinction (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) [Finite W] (M : Model W Atom Agent),
    ∃ n : Nat, Edgeless (M.iterateUpdate φ n)

theorem fixed_iff_targets (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    M.update φ = M ↔ ∀ i x y, M.rel i x y → M.Satisfies y φ := by
  constructor
  · intro h i x y hxy
    have h' : (M.update φ).rel i x y := by rw [h]; exact hxy
    exact h'.2
  · intro h
    apply Model.ext'
    · intro i x y
      exact ⟨And.left, fun hxy => ⟨hxy, h i x y hxy⟩⟩
    · intro p x
      rfl

theorem edgeless_iff_update_falsum [Inhabited Atom]
    (M : Model World Atom Agent) : Edgeless M ↔ M = M.update Formula.falsum := by
  constructor
  · intro h
    exact (edgeless_update_eq M h Formula.falsum).symm
  · intro h i x y hxy
    rw [h] at hxy
    exact Model.satisfies_falsum M y hxy.2

theorem fixed_ordinal (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (h : M.update φ = M) (α : Ordinal.{max u w}) : ordinalUpdate M φ α = M := by
  have hstep : ordinalUpdate M φ (Order.succ 0) = ordinalUpdate M φ 0 := by
    rw [ordinalUpdate_succ, ordinalUpdate_zero]
    exact h
  simpa using ordinalUpdate_eq_of_ge_of_step M φ hstep (Ordinal.zero_le α)

theorem onlyZeroFixed_iff_ordinalExtinction (φ : Formula Atom Agent) :
    OnlyZeroFixed.{u} φ ↔ OrdinalExtinction.{u} φ := by
  constructor
  · intro h W M
    obtain ⟨α, hα⟩ := exists_ordinalUpdate_stableStep M φ
    refine ⟨α, h W (ordinalUpdate M φ α) ?_⟩
    simpa only [ordinalUpdate_succ] using hα
  · intro h W M hfixed
    obtain ⟨α, hα⟩ := h W M
    simpa only [fixed_ordinal M φ hfixed α] using hα

theorem onlyZeroFixed_implies_finiteExtinction (φ : Formula Atom Agent) :
    OnlyZeroFixed.{u} φ → FiniteExtinction.{u} φ := by
  intro h W _ M
  obtain ⟨n, hn⟩ := M.exists_iterateUpdate_stableStep φ
  exact ⟨n, h W (M.iterateUpdate φ n) (by simpa only [Model.iterateUpdate_succ] using hn)⟩

theorem finiteExtinction_implies_onlyZeroFixed (φ : Formula Atom Agent) :
    FiniteExtinction.{u} φ → OnlyZeroFixed.{u} φ := by
  intro h W M hfixed
  let N := MinimalFiltration.model M φ
  have hN : N.update φ = N := (fixed_iff_targets N φ).mpr
    (MinimalFiltration.targets_true M φ ((fixed_iff_targets M φ).mp hfixed))
  obtain ⟨n, hn⟩ := h (MinimalFiltration.WorldType M φ) N
  have hnfix : N.iterateUpdate φ n = N := by
    clear hn
    induction n with
    | zero => rfl
    | succ n ih => rw [Model.iterateUpdate_succ, ih, hN]
  rw [hnfix] at hn
  intro i x y hxy
  exact hn i _ _ (MinimalFiltration.original_edge M φ hxy)

theorem finiteExtinction_iff_onlyZeroFixed (φ : Formula Atom Agent) :
    FiniteExtinction.{u} φ ↔ OnlyZeroFixed.{u} φ :=
  ⟨finiteExtinction_implies_onlyZeroFixed φ, onlyZeroFixed_implies_finiteExtinction φ⟩

theorem unknowable_implies_onlyZeroFixed (φ : Formula Atom Agent) :
    CommonlyUnknowable.{u} φ → OnlyZeroFixed.{u} φ := by
  intro h W M hfix i x y hxy
  exact h W M y ⟨(fixed_iff_targets M φ).mp hfix i x y hxy,
    common_at_fixed hfix y⟩

/-- An extra predecessor has no incoming edges and cannot affect old worlds. -/
def predecessor (M : Model World Atom Agent) (root : World) (agent : Agent) :
    Model (Option World) Atom Agent where
  rel i x y := match x, y with
    | some x, some y => M.rel i x y
    | none, some y => i = agent ∧ y = root
    | _, none => False
  val p x := match x with
    | some x => M.val p x
    | none => False

theorem predecessor_truth (M : Model World Atom Agent) (root : World) (agent : Agent)
    (x : World) (φ : Formula Atom Agent) :
    (predecessor M root agent).Satisfies (some x) φ ↔ M.Satisfies x φ := by
  induction φ generalizing x with
  | atom p => rfl
  | neg φ ih => exact not_congr (ih x)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ x) (ihψ x)
  | box i φ ih =>
      constructor
      · intro h y hxy
        exact (ih y).mp (h (some y) hxy)
      · intro h y hxy
        cases y with
        | none => exact hxy.elim
        | some y => exact (ih y).mpr (h y hxy)

theorem generated_globally_true (M : Model World Atom Agent) (x : World)
    (φ : Formula Atom Agent) (hx : M.Satisfies x φ) (hc : Common M x φ) :
    ∀ y, (M.generatedSubmodel x).Satisfies y φ := by
  intro y
  apply (M.generatedSubmodel_satisfies_iff x y φ).mpr
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp y.property with heq | hp
  · simpa only [heq] using hx
  · exact hc y.val hp

theorem onlyZeroFixed_implies_unknowable [Nonempty Agent] (φ : Formula Atom Agent) :
    OnlyZeroFixed.{u} φ → CommonlyUnknowable.{u} φ := by
  classical
  intro h W M x ⟨hx, hc⟩
  let a : Agent := Classical.choice inferInstance
  let N := M.generatedSubmodel x
  let root := M.generatedPoint x
  have hN := generated_globally_true M x φ hx hc
  let P := predecessor N root a
  have hP : P.update φ = P := by
    apply (fixed_iff_targets P φ).mpr
    intro i s t hst
    cases t with
    | none => cases s <;> exact hst.elim
    | some t => exact (predecessor_truth N root a t φ).mpr (hN t)
  exact h (Option (Subtype (M.generatedSet x))) P hP a none (some root) ⟨rfl, rfl⟩

theorem onlyZeroFixed_iff_unknowable [Nonempty Agent] (φ : Formula Atom Agent) :
    OnlyZeroFixed.{u} φ ↔ CommonlyUnknowable.{u} φ :=
  ⟨onlyZeroFixed_implies_unknowable φ, unknowable_implies_onlyZeroFixed φ⟩

theorem unknowable_iff_informative (φ : Formula Atom Agent) :
    CommonlyUnknowable.{u} φ ↔ InformativeWhenTrue.{u} φ := by
  simp only [CommonlyUnknowable, InformativeWhenTrue, generatedUnchanged_iff_common]
  constructor
  · intro h W M x ht hc
    exact h W M x ⟨ht, hc⟩
  · intro h W M x ⟨ht, hc⟩
    exact h W M x ht hc

theorem unknowable_iff_common_implies_neg (φ : Formula Atom Agent) :
    CommonlyUnknowable.{u} φ ↔
      ∀ (W : Type u) (M : Model W Atom Agent) x, Common M x φ → ¬ M.Satisfies x φ := by
  unfold CommonlyUnknowable
  tauto

theorem unknowable_iff_moore (φ : Formula Atom Agent) :
    CommonlyUnknowable.{u} φ ↔
      ∀ (W : Type u) (M : Model W Atom Agent) x,
        (M.Satisfies x φ ↔ M.Satisfies x φ ∧ ¬ Common M x φ) := by
  constructor
  · intro h W M x
    exact ⟨fun hx => ⟨hx, fun hc => h W M x ⟨hx, hc⟩⟩, And.left⟩
  · intro h W M x ⟨hx, hc⟩
    exact ((h W M x).mp hx).2 hc

/-- The seven K conditions of Theorem 28, with BPAL extinction. -/
theorem theorem28_K [Nonempty Agent] (φ : Formula Atom Agent) :
    (FiniteExtinction.{u} φ ↔ OrdinalExtinction.{u} φ) ∧
    (OrdinalExtinction.{u} φ ↔ OnlyZeroFixed.{u} φ) ∧
    (OnlyZeroFixed.{u} φ ↔ CommonlyUnknowable.{u} φ) ∧
    (CommonlyUnknowable.{u} φ ↔ InformativeWhenTrue.{u} φ) ∧
    (CommonlyUnknowable.{u} φ ↔
      ∀ (W : Type u) (M : Model W Atom Agent) x, Common M x φ → ¬ M.Satisfies x φ) ∧
    (CommonlyUnknowable.{u} φ ↔
      ∀ (W : Type u) (M : Model W Atom Agent) x,
        (M.Satisfies x φ ↔ M.Satisfies x φ ∧ ¬ Common M x φ)) := by
  exact ⟨(finiteExtinction_iff_onlyZeroFixed φ).trans
      (onlyZeroFixed_iff_ordinalExtinction φ),
    (onlyZeroFixed_iff_ordinalExtinction φ).symm,
    onlyZeroFixed_iff_unknowable φ, unknowable_iff_informative φ,
    unknowable_iff_common_implies_neg φ, unknowable_iff_moore φ⟩

end Extinction

end PropertiesOfPublicAnnouncementsAsOperators
