import PropertiesOfPALAndBPALOperators.ExtinctionOnClasses

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u v w

namespace Extinction

variable {World : Type u} {Atom : Type v} {Agent : Type w}

theorem palDomain_of_global_truth (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (ht : ∀ x, M.Satisfies x φ) (α : Ordinal.{max u w}) : palDomain M φ α = Set.univ := by
  have hf : M.update φ = M := (fixed_iff_targets M φ).mpr (fun _ _ y _ => ht y)
  apply Set.eq_univ_of_forall
  intro x β hβ
  rw [fixed_ordinal M φ hf β]
  exact ht x

theorem pal_onlyZeroFixed_of_ordinalExtinction (C : ModelClass.{u} Atom Agent)
    (φ : Formula Atom Agent) (h : PALOrdinalExtinctionOn C φ) : PALOnlyZeroFixedOn C φ := by
  intro W M hM ht
  obtain ⟨α, hα⟩ := h W M hM
  rw [palDomain_of_global_truth M φ ht α] at hα
  exact ⟨fun x => Set.notMem_empty x (hα ▸ Set.mem_univ x)⟩

theorem pal_finiteExtinction_of_onlyZeroFixed
    (C : ModelClass.{u} Atom Agent)
    (hres : ∀ (W : Type u) (M : Model W Atom Agent), C M →
      ∀ S : Set W, C (M.restrict S)) (φ : Formula Atom Agent)
    (h : PALOnlyZeroFixedOn C φ) : PALFiniteExtinctionOn C φ := by
  classical
  intro W _ M hM
  letI := Fintype.ofFinite W
  let n := Fintype.card W
  have hs : PALStable M φ (n : Ordinal.{max u w}) :=
    (palRank_le_iff M φ _).mp (palRank_le_card M φ)
  refine ⟨n, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro x hx
  exact (h _ (M.restrict (palDomain M φ n)) (hres W M hM _)
    (stable_restriction_globally_true M φ n hs)).false ⟨x, hx⟩

theorem pal_finiteExtinction_implies_bpal
    (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent)
    (h : PALFiniteExtinctionOn C φ) : BPALFiniteExtinctionOn C φ := by
  intro W _ M hM
  obtain ⟨n, hn⟩ := h W M hM
  refine ⟨n, ?_⟩
  simpa only [ordinalUpdate_natCast] using empty_domain_edgeless M φ n hn

theorem pal_ordinalExtinction_implies_bpal
    (C : ModelClass.{u} Atom Agent) (φ : Formula Atom Agent)
    (h : PALOrdinalExtinctionOn C φ) : BPALOrdinalExtinctionOn C φ := by
  intro W M hM
  obtain ⟨α, hα⟩ := h W M hM
  exact ⟨α, empty_domain_edgeless M φ α hα⟩

theorem s5_bpal_ordinalExtinction_implies_pal [Nonempty Agent]
    (φ : Formula Atom Agent) (h : BPALOrdinalExtinctionOn S5Class.{u, v, w} φ) :
    PALOrdinalExtinctionOn S5Class.{u, v, w} φ := by
  intro W M hM
  obtain ⟨α, hα⟩ := h W M hM
  exact ⟨α, incoming_edgeless_empty M φ α
    (hasIncoming_of_reflexive M (fun i x => (hM i).1 x)) hα⟩

theorem s5_pal_fixed_iff_unknowable (φ : Formula Atom Agent) :
    PALOnlyZeroFixedOn S5Class.{u, v, w} φ ↔ UnknowableOn S5Class.{u, v, w} φ :=
  pal_fixed_iff_unknowable S5Class.{u, v, w}
    (fun _ M hM x => M.restrict_isS5 hM (M.generatedSet x)) φ

theorem s5_finite_bpal_implies_pal_fixed [Nonempty Agent] (φ : Formula Atom Agent)
    (h : BPALFiniteExtinctionOn S5Class.{u, v, w} φ) : PALOnlyZeroFixedOn S5Class.{u, v, w} φ := by
  classical
  intro W M hM ht
  let N := Filtration.model M φ
  have hN : IsS5 N := Filtration.model_isS5 hM φ
  have hNt : ∀ x, N.Satisfies x φ := fun x =>
    (Filtration.model_satisfies_iff hM.isK45 φ x φ (Formula.mem_subformulas_self φ)).mpr
      (ht x.out)
  have hfix : N.update φ = N := (fixed_iff_targets N φ).mpr (fun _ _ y _ => hNt y)
  obtain ⟨n, hn⟩ := h (Filtration.FilteredWorld M φ) N hN
  have hnfix : N.iterateUpdate φ n = N := by
    clear hn
    induction n with
    | zero => rfl
    | succ n ih => rw [Model.iterateUpdate_succ, ih, hfix]
  rw [hnfix] at hn
  refine ⟨fun x => ?_⟩
  let i : Agent := Classical.choice inferInstance
  let q := Quotient.mk (Filtration.setoid M φ) x
  exact hn i q q ((hN i).1 q)

/-- The extinction, fixed-point, and common-unknowability conditions over S5. -/
theorem theorem28_S5_dynamics [Nonempty Agent] (φ : Formula Atom Agent) :
    (PALFiniteExtinctionOn S5Class.{u, v, w} φ ↔ UnknowableOn S5Class.{u, v, w} φ) ∧
    (BPALFiniteExtinctionOn S5Class.{u, v, w} φ ↔ UnknowableOn S5Class.{u, v, w} φ) ∧
    (PALOrdinalExtinctionOn S5Class.{u, v, w} φ ↔ UnknowableOn S5Class.{u, v, w} φ) ∧
    (BPALOrdinalExtinctionOn S5Class.{u, v, w} φ ↔ UnknowableOn S5Class.{u, v, w} φ) ∧
    (PALOnlyZeroFixedOn S5Class.{u, v, w} φ ↔ UnknowableOn S5Class.{u, v, w} φ) ∧
    (BPALOnlyZeroFixedOn S5Class.{u, v, w} φ ↔ UnknowableOn S5Class.{u, v, w} φ) := by
  have hres : ∀ (W : Type u) (M : Model W Atom Agent), S5Class.{u, v, w} M →
      ∀ S : Set W, S5Class.{u, v, w} (M.restrict S) := fun _ M hM S => M.restrict_isS5 hM S
  have hu := s5_pal_fixed_iff_unknowable.{u, v, w} φ
  have hfB : BPALFiniteExtinctionOn S5Class.{u, v, w} φ ↔ UnknowableOn S5Class.{u, v, w} φ :=
    ⟨fun h => hu.mp (s5_finite_bpal_implies_pal_fixed φ h), fun h =>
      pal_finiteExtinction_implies_bpal S5Class.{u, v, w} φ
        (pal_finiteExtinction_of_onlyZeroFixed S5Class.{u, v, w} hres φ (hu.mpr h))⟩
  have hfP : PALFiniteExtinctionOn S5Class.{u, v, w} φ ↔ UnknowableOn S5Class.{u, v, w} φ :=
    ⟨fun h => hfB.mp (pal_finiteExtinction_implies_bpal S5Class.{u, v, w} φ h), fun h =>
      pal_finiteExtinction_of_onlyZeroFixed S5Class.{u, v, w} hres φ (hu.mpr h)⟩
  have hoP : PALOrdinalExtinctionOn S5Class.{u, v, w} φ ↔ UnknowableOn S5Class.{u, v, w} φ :=
    ⟨fun h => hu.mp (pal_onlyZeroFixed_of_ordinalExtinction S5Class.{u, v, w} φ h), fun h =>
      pal_ordinalExtinction_of_onlyZeroFixed S5Class.{u, v, w} hres φ (hu.mpr h)⟩
  have hoB : BPALOrdinalExtinctionOn S5Class.{u, v, w} φ ↔ UnknowableOn S5Class.{u, v, w} φ :=
    ⟨fun h => hoP.mp (s5_bpal_ordinalExtinction_implies_pal φ h), fun h =>
      pal_ordinalExtinction_implies_bpal S5Class.{u, v, w} φ (hoP.mpr h)⟩
  exact ⟨hfP, hfB, hoP, hoB, hu, s5_bpal_fixed_iff_unknowable φ⟩

theorem theorem28_S5_logical [Nonempty Agent] (φ : Formula Atom Agent) :
    (UnknowableOn S5Class.{u, v, w} φ ↔ InformativeWhenTrueOn S5Class.{u, v, w} φ) ∧
    (UnknowableOn S5Class.{u, v, w} φ ↔ UnbelievableOn S5Class.{u, v, w} φ) ∧
    (UnknowableOn S5Class.{u, v, w} φ ↔ InformativeOn S5Class.{u, v, w} φ) := by
  have h := serial_unknowable_iff_unbelievable S5Class.{u, v, w}
    (fun _ _ hM i => Frame.reflexive_serial (hM i).1) φ
  exact ⟨unknowableOn_iff_informativeWhenTrueOn S5Class.{u, v, w} φ, h,
    h.trans (unbelievableOn_iff_informativeOn S5Class.{u, v, w} φ)⟩

/-- The PAL version of the seven K conditions. -/
theorem theorem28_K_pal [Nonempty Agent] (φ : Formula Atom Agent) :
    (PALFiniteExtinctionOn KClass.{u, v, w} φ ↔ CommonlyUnknowable.{u} φ) ∧
    (PALOrdinalExtinctionOn KClass.{u, v, w} φ ↔ CommonlyUnknowable.{u} φ) ∧
    (PALOnlyZeroFixedOn KClass.{u, v, w} φ ↔ CommonlyUnknowable.{u} φ) := by
  have hc : UnknowableOn KClass.{u, v, w} φ ↔ CommonlyUnknowable.{u} φ := by
    simp only [UnknowableOn, KClass, CommonlyUnknowable, forall_const]
  have hu := (pal_fixed_iff_unknowable KClass.{u, v, w} (fun _ _ _ _ => trivial) φ).trans hc
  have ho : PALOrdinalExtinctionOn KClass.{u, v, w} φ ↔ CommonlyUnknowable.{u} φ :=
    ⟨fun h => hu.mp (pal_onlyZeroFixed_of_ordinalExtinction KClass.{u, v, w} φ h), fun h =>
      pal_ordinalExtinction_of_onlyZeroFixed KClass.{u, v, w} (fun _ _ _ _ => trivial) φ (hu.mpr h)⟩
  have hf : PALFiniteExtinctionOn KClass.{u, v, w} φ ↔ CommonlyUnknowable.{u} φ := by
    constructor
    · intro h
      apply (onlyZeroFixed_iff_unknowable φ).mp
      apply finiteExtinction_implies_onlyZeroFixed
      have hb := pal_finiteExtinction_implies_bpal KClass.{u, v, w} φ h
      exact fun W inst M => hb W M trivial
    · intro h
      exact pal_finiteExtinction_of_onlyZeroFixed KClass.{u, v, w} (fun _ _ _ _ => trivial) φ (hu.mpr h)
  exact ⟨hf, ho, hu⟩

end Extinction

end PropertiesOfPALAndBPALOperators
