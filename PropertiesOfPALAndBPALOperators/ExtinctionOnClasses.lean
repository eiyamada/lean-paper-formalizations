import PropertiesOfPALAndBPALOperators.Extinction
import PropertiesOfPALAndBPALOperators.Dynamics

/-!
# Frame classes, S5, and the PAL extinction conditions

The serial-frame clause concerns the logical conditions only. The S5 theorem
uses induced models of the surviving domain, because a BPAL update of an S5
model need not itself be S5.
-/

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u v w

namespace Extinction

variable {World : Type u} {Atom : Type v} {Agent : Type w}

abbrev ModelClass (Atom : Type v) (Agent : Type w) :=
  {W : Type u} → Model W Atom Agent → Prop

def S5Class : ModelClass.{u} Atom Agent := fun M => IsS5 M

def KClass : ModelClass.{u} Atom Agent := fun _ => True

def UnknowableOn (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent), C M →
    ∀ x, ¬ (M.Satisfies x φ ∧ Common M x φ)

def UnbelievableOn (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent), C M → ∀ x, ¬ Common M x φ

def InformativeOn (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent), C M →
    ∀ x, ¬ GeneratedUnchanged M x φ

def InformativeWhenTrueOn (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent), C M →
    ∀ x, M.Satisfies x φ → ¬ GeneratedUnchanged M x φ

theorem unknowableOn_iff_informativeWhenTrueOn
    (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent) :
    UnknowableOn C φ ↔ InformativeWhenTrueOn C φ := by
  simp only [UnknowableOn, InformativeWhenTrueOn, generatedUnchanged_iff_common]
  tauto

theorem unbelievableOn_iff_informativeOn
    (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent) :
    UnbelievableOn C φ ↔ InformativeOn C φ := by
  simp only [UnbelievableOn, InformativeOn, generatedUnchanged_iff_common]

theorem unknowableOn_iff_common_implies_neg
    (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent) :
    UnknowableOn C φ ↔ ∀ (W : Type u) (M : Model W Atom Agent), C M →
      ∀ x, Common M x φ → ¬ M.Satisfies x φ := by
  constructor
  · intro h W M hM x hc hx
    exact h W M hM x ⟨hx, hc⟩
  · intro h W M hM x ⟨hx, hc⟩
    exact h W M hM x hc hx

theorem unknowableOn_iff_moore
    (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent) :
    UnknowableOn C φ ↔ ∀ (W : Type u) (M : Model W Atom Agent), C M →
      ∀ x, M.Satisfies x φ ↔ M.Satisfies x φ ∧ ¬ Common M x φ := by
  constructor
  · intro h W M hM x
    exact ⟨fun hx => ⟨hx, fun hc => h W M hM x ⟨hx, hc⟩⟩, And.left⟩
  · intro h W M hM x ⟨hx, hc⟩
    exact ((h W M hM x).mp hx).2 hc

theorem common_at_successor (M : Model World Atom Agent) (φ : Formula Atom Agent)
    {x y : World} (hx : Common M x φ) {i : Agent} (hxy : M.rel i x y) :
    M.Satisfies y φ ∧ Common M y φ := by
  refine ⟨hx y (Relation.TransGen.single ⟨i, hxy⟩), ?_⟩
  intro z hyz
  exact hx z ((Relation.TransGen.single ⟨i, hxy⟩).trans hyz)

/-- On serial classes common belief has a successor witnessing common knowledge. -/
theorem serial_unknowable_iff_unbelievable [Nonempty Agent]
    (C : ModelClass.{u} Atom Agent)
    (hserial : ∀ (W : Type u) (M : Model W Atom Agent), C M →
      ∀ i, Frame.Serial (M.rel i)) (φ : Formula Atom Agent) :
    UnknowableOn C φ ↔ UnbelievableOn C φ := by
  classical
  constructor
  · intro h W M hM x hc
    let i : Agent := Classical.choice inferInstance
    obtain ⟨y, hxy⟩ := hserial W M hM i x
    exact h W M hM y (common_at_successor M φ hc hxy)
  · intro h W M hM x hx
    exact h W M hM x hx.2

def PALOnlyZeroFixedOn (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent), C M →
    (∀ x, M.Satisfies x φ) → IsEmpty W

def BPALOnlyZeroFixedOn (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent), C M → M.update φ = M → Edgeless M

def PALOrdinalExtinctionOn (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent), C M →
    ∃ α : Ordinal.{max u w}, palDomain M φ α = ∅

def BPALOrdinalExtinctionOn (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent), C M →
    ∃ α : Ordinal.{max u w}, Edgeless (ordinalUpdate M φ α)

def PALFiniteExtinctionOn (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) [Finite W] (M : Model W Atom Agent), C M →
    ∃ n : Nat, palDomain M φ n = ∅

def BPALFiniteExtinctionOn (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent) : Prop :=
  ∀ (W : Type u) [Finite W] (M : Model W Atom Agent), C M →
    ∃ n : Nat, Edgeless (M.iterateUpdate φ n)

theorem global_truth_common (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (h : ∀ x, M.Satisfies x φ) (x : World) : Common M x φ := fun y _ => h y

theorem pal_fixed_iff_unknowable (C : ModelClass.{u} Atom Agent)
    (hgen : ∀ (W : Type u) (M : Model W Atom Agent), C M →
      ∀ x, C (M.generatedSubmodel x)) (φ : Formula Atom Agent) :
    PALOnlyZeroFixedOn C φ ↔ UnknowableOn C φ := by
  constructor
  · intro h W M hM x ⟨hx, hc⟩
    have hempty := h _ (M.generatedSubmodel x) (hgen W M hM x)
      (generated_globally_true M x φ hx hc)
    exact hempty.false (M.generatedPoint x)
  · intro h W M hM ht
    exact ⟨fun x => h W M hM x ⟨ht x, global_truth_common M φ ht x⟩⟩

theorem s5_bpal_fixed_iff_unknowable [Nonempty Agent] (φ : Formula Atom Agent) :
    BPALOnlyZeroFixedOn S5Class.{u, v, w} φ ↔ UnknowableOn S5Class.{u, v, w} φ := by
  classical
  constructor
  · intro h W M hM x ⟨hx, hc⟩
    let N := M.generatedSubmodel x
    have hN : IsS5 N := Model.restrict_isS5 hM _
    have ht := generated_globally_true M x φ hx hc
    have hf : N.update φ = N := (fixed_iff_targets N φ).mpr (fun _ _ y _ => ht y)
    let i : Agent := Classical.choice inferInstance
    exact h _ N hN hf i (M.generatedPoint x) (M.generatedPoint x)
      ((hN i).1 (M.generatedPoint x))
  · intro h W M hM hf i x y hxy
    exact h W M hM y ⟨(fixed_iff_targets M φ).mp hf i x y hxy, common_at_fixed hf y⟩

/-- At a PAL fixed stage, its surviving induced model globally satisfies φ. -/
theorem stable_restriction_globally_true (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (α : Ordinal.{max u w}) (h : PALStable M φ α) :
    ∀ x, (M.restrict (palDomain M φ α)).Satisfies x φ := by
  intro x
  exact (palDomain_satisfies_iff M φ α x φ).mpr
    ((palStable_iff M φ α).mp h x.val x.property)

theorem empty_domain_edgeless (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (α : Ordinal.{max u w})
    (h : palDomain M φ α = ∅) : Edgeless (ordinalUpdate M φ α) := by
  intro i x y hxy
  have hy : y ∈ palDomain M φ α :=
    ((ordinalUpdate_rel_iff M φ α i x y).mp hxy).2
  rw [h] at hy
  exact hy

theorem incoming_edgeless_empty (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (α : Ordinal.{max u w}) (hin : HasIncoming M)
    (h : Edgeless (ordinalUpdate M φ α)) : palDomain M φ α = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨i, x, hxy⟩ := hin y
  exact h i x y ((ordinalUpdate_rel_iff M φ α i x y).mpr ⟨hxy, hy⟩)

theorem pal_ordinalExtinction_of_onlyZeroFixed
    (C : ModelClass.{u} Atom Agent)
    (hres : ∀ (W : Type u) (M : Model W Atom Agent), C M →
      ∀ S : Set W, C (M.restrict S)) (φ : Formula Atom Agent)
    (h : PALOnlyZeroFixedOn C φ) : PALOrdinalExtinctionOn C φ := by
  intro W M hM
  obtain ⟨α, hα⟩ := exists_palStable M φ
  refine ⟨α, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro x hx
  exact (h _ (M.restrict (palDomain M φ α)) (hres W M hM _)
    (stable_restriction_globally_true M φ α hα)).false ⟨x, hx⟩

end Extinction

end PropertiesOfPALAndBPALOperators
