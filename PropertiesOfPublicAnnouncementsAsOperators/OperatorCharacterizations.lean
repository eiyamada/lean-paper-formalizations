import PropertiesOfPublicAnnouncementsAsOperators.AnnouncementMonotonicity
import PropertiesOfPublicAnnouncementsAsOperators.Propositional
import PropertiesOfPublicAnnouncementsAsOperators.PALFixedPoints
import PropertiesOfPublicAnnouncementsAsOperators.Extinction

/-! # Operator comparisons and propositional commutation

The comparisons use actual model equality and actual PAL surviving domains.
Fresh atoms test arbitrary induced domains; a fresh predecessor makes BPAL
operator equality detect the truth at a world that originally had no incoming
arrow.
-/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

theorem palUpdate_univ_mem (M : Model World Atom Agent) (φ : Formula Atom Agent) (x : World) :
    x ∈ palUpdate M φ.toPAL Set.univ ↔ M.Satisfies x φ := by
  change (True ∧ PAL.Satisfies M Set.univ x φ.toPAL) ↔ _
  have hbase : PAL.domainModel M Set.univ = M := PAL.domainModel_true M
  rw [PAL.satisfies_toPAL, hbase]
  exact and_iff_right trivial

theorem palUpdate_twice_mem (M : Model World Atom Agent) (φ ψ : Formula Atom Agent) (x : World) :
    x ∈ palUpdate M φ.toPAL (palUpdate M ψ.toPAL Set.univ) ↔
      M.Satisfies x ψ ∧ (M.update ψ).Satisfies x φ := by
  change (True ∧ PAL.Satisfies M Set.univ x ψ.toPAL) ∧
    PAL.Satisfies M (palUpdate M ψ.toPAL Set.univ) x φ.toPAL ↔ _
  have hbase : PAL.domainModel M Set.univ = M := PAL.domainModel_true M
  rw [PAL.satisfies_toPAL, PAL.satisfies_toPAL, domainModel_palUpdate, hbase]
  exact and_congr (and_iff_right trivial) Iff.rfl

theorem predecessor_update_truth (M : Model World Atom Agent) (root : World) (a : Agent)
    (ψ φ : Formula Atom Agent) (x : World) :
    ((Extinction.predecessor M root a).update ψ).Satisfies (some x) φ ↔
      (M.update ψ).Satisfies x φ := by
  rw [Model.satisfies_announcementReduce, Model.satisfies_announcementReduce]
  exact Extinction.predecessor_truth M root a x _

def PALComparisonUp (φ : Formula Atom Agent) : Prop :=
  ∀ {W : Type u} (M : Model W Atom Agent) (ψ : Formula Atom Agent),
    palUpdate M (Formula.conj φ ψ).toPAL Set.univ ⊆
      palUpdate M φ.toPAL (palUpdate M ψ.toPAL Set.univ)

def PALComparisonDown (φ : Formula Atom Agent) : Prop :=
  ∀ {W : Type u} (M : Model W Atom Agent) (ψ : Formula Atom Agent),
    palUpdate M φ.toPAL (palUpdate M ψ.toPAL Set.univ) ⊆
      palUpdate M (Formula.conj φ ψ).toPAL Set.univ

def BPALComparisonUp (φ : Formula Atom Agent) : Prop :=
  ∀ {W : Type u} (M : Model W Atom Agent) (ψ : Formula Atom Agent),
    ArrowSubmodel (M.update (.conj φ ψ)) ((M.update ψ).update φ)

def BPALComparisonDown (φ : Formula Atom Agent) : Prop :=
  ∀ {W : Type u} (M : Model W Atom Agent) (ψ : Formula Atom Agent),
    ArrowSubmodel ((M.update ψ).update φ) (M.update (.conj φ ψ))

theorem palComparisonUp_iff_preserved (φ : Formula Atom Agent) :
    PALComparisonUp.{u} φ ↔ AnnouncementPreserved.{u} φ := by
  constructor
  · intro h W M ψ x hφ hψ
    exact (palUpdate_twice_mem M φ ψ x).mp
      (h M ψ ((palUpdate_univ_mem M (.conj φ ψ) x).mpr ⟨hφ, hψ⟩)) |>.2
  · intro h W M ψ x hx
    obtain ⟨hφ, hψ⟩ := (palUpdate_univ_mem M (.conj φ ψ) x).mp hx
    exact (palUpdate_twice_mem M φ ψ x).mpr ⟨hψ, h M ψ x hφ hψ⟩

theorem bpalComparisonUp_iff_preserved [Nonempty Agent] (φ : Formula Atom Agent) :
    BPALComparisonUp.{u} φ ↔ AnnouncementPreserved.{u} φ := by
  classical
  constructor
  · intro h W M ψ x hφ hψ
    let a := Classical.arbitrary Agent
    let P := Extinction.predecessor M x a
    have harrow : (P.update (.conj φ ψ)).rel a none (some x) :=
      ⟨⟨rfl, rfl⟩, (Extinction.predecessor_truth M x a x φ).mpr hφ,
        (Extinction.predecessor_truth M x a x ψ).mpr hψ⟩
    exact (predecessor_update_truth M x a ψ φ x).mp
      ((h P ψ).rel_le a none (some x) harrow).2
  · intro h W M ψ
    exact ⟨rfl, fun i x y hy => ⟨⟨hy.1, hy.2.2⟩, h M ψ y hy.2.1 hy.2.2⟩⟩

theorem palComparisonDown_iff_neg_up (φ : Formula Atom Agent) :
    PALComparisonDown.{u} φ ↔ PALComparisonUp.{u} (.neg φ) := by
  classical
  constructor
  · intro h W M ψ x hx
    obtain ⟨hnφ, hψ⟩ := (palUpdate_univ_mem M (.conj (.neg φ) ψ) x).mp hx
    apply (palUpdate_twice_mem M (.neg φ) ψ x).mpr
    refine ⟨hψ, fun ht => ?_⟩
    exact hnφ ((palUpdate_univ_mem M (.conj φ ψ) x).mp
      (h M ψ ((palUpdate_twice_mem M φ ψ x).mpr ⟨hψ, ht⟩))).1
  · intro h W M ψ x hx
    obtain ⟨hψ, ht⟩ := (palUpdate_twice_mem M φ ψ x).mp hx
    apply (palUpdate_univ_mem M (.conj φ ψ) x).mpr
    refine ⟨?_, hψ⟩
    by_contra hnφ
    have hn := (palUpdate_twice_mem M (.neg φ) ψ x).mp
      (h M ψ ((palUpdate_univ_mem M (.conj (.neg φ) ψ) x).mpr ⟨hnφ, hψ⟩))
    exact hn.2 ht

theorem bpalComparisonDown_iff_neg_up (φ : Formula Atom Agent) :
    BPALComparisonDown.{u} φ ↔ BPALComparisonUp.{u} (.neg φ) := by
  classical
  constructor
  · intro h W M ψ
    refine ⟨rfl, ?_⟩
    intro i x y hy
    refine ⟨⟨hy.1, hy.2.2⟩, fun ht => ?_⟩
    exact hy.2.1 ((h M ψ).rel_le i x y ⟨⟨hy.1, hy.2.2⟩, ht⟩).2.1
  · intro h W M ψ
    refine ⟨rfl, ?_⟩
    intro i x y hy
    refine ⟨hy.1.1, ?_, hy.1.2⟩
    by_contra hn
    exact ((h M ψ).rel_le i x y ⟨hy.1.1, hn, hy.1.2⟩).2 hy.2

theorem palComparisonUp_iff_deletionMonotone [Infinite Atom] (φ : Formula Atom Agent) :
    PALComparisonUp.{u} φ ↔ DeletionMonotone.{u} φ :=
  (palComparisonUp_iff_preserved φ).trans
    ((announcementPreserved_iff_submodelPreserved φ).trans
      (deletionMonotone_iff_submodelPreserved φ).symm)

theorem bpalComparisonUp_iff_deletionMonotone [Infinite Atom] [Nonempty Agent]
    (φ : Formula Atom Agent) : BPALComparisonUp.{u} φ ↔ DeletionMonotone.{u} φ :=
  (bpalComparisonUp_iff_preserved φ).trans
    ((announcementPreserved_iff_submodelPreserved φ).trans
      (deletionMonotone_iff_submodelPreserved φ).symm)

theorem palComparisonDown_iff_deletionAntimonotone [Infinite Atom] (φ : Formula Atom Agent) :
    PALComparisonDown.{u} φ ↔ DeletionAntimonotone.{u} φ :=
  (palComparisonDown_iff_neg_up φ).trans
    ((palComparisonUp_iff_deletionMonotone (.neg φ)).trans (deletionMonotone_neg_iff φ))

theorem bpalComparisonDown_iff_deletionAntimonotone [Infinite Atom] [Nonempty Agent]
    (φ : Formula Atom Agent) : BPALComparisonDown.{u} φ ↔ DeletionAntimonotone.{u} φ :=
  (bpalComparisonDown_iff_neg_up φ).trans
    ((bpalComparisonUp_iff_deletionMonotone (.neg φ)).trans (deletionMonotone_neg_iff φ))

/-- Corollary 20(1) iff (3), in PAL. -/
theorem propositional_iff_pal_composition [Infinite Atom] [Inhabited Atom]
    (φ : Formula Atom Agent) : PropositionalEquivalent.{u} φ ↔
      ∀ {W : Type u} (M : Model W Atom Agent) (ψ : Formula Atom Agent),
        palUpdate M φ.toPAL (palUpdate M ψ.toPAL Set.univ) =
          palUpdate M (Formula.conj φ ψ).toPAL Set.univ := by
  rw [propositionalEquivalent_iff_both_deletion, ← palComparisonUp_iff_deletionMonotone,
    ← palComparisonDown_iff_deletionAntimonotone]
  constructor
  · rintro ⟨hu, hd⟩ W M ψ
    exact Set.Subset.antisymm (hd M ψ) (hu M ψ)
  · intro h
    exact ⟨fun M ψ => (h M ψ).symm.subset, fun M ψ => (h M ψ).subset⟩

/-- Corollary 20(1) iff (3), in BPAL. -/
theorem propositional_iff_bpal_composition [Infinite Atom] [Inhabited Atom] [Nonempty Agent]
    (φ : Formula Atom Agent) : PropositionalEquivalent.{u} φ ↔
      ∀ {W : Type u} (M : Model W Atom Agent) (ψ : Formula Atom Agent),
        (M.update ψ).update φ = M.update (.conj φ ψ) := by
  rw [propositionalEquivalent_iff_both_deletion, ← bpalComparisonUp_iff_deletionMonotone,
    ← bpalComparisonDown_iff_deletionAntimonotone]
  constructor
  · rintro ⟨hu, hd⟩ W M ψ
    exact ArrowSubmodel.antisymm (hd M ψ) (hu M ψ)
  · intro h
    constructor
    · intro W M ψ
      rw [h M ψ]
      exact ArrowSubmodel.refl _
    · intro W M ψ
      rw [h M ψ]
      exact ArrowSubmodel.refl _

def AtomAnnouncementInvariant (φ : Formula Atom Agent) : Prop :=
  ∀ {W : Type u} (M : Model W Atom Agent) (p : Atom) (x : W), M.val p x →
    (M.Satisfies x φ ↔ (M.update (.atom p)).Satisfies x φ)

theorem atomInvariant_implies_propositional [Infinite Atom] [Inhabited Atom]
    (φ : Formula Atom Agent) (h : AtomAnnouncementInvariant.{u} φ) :
    PropositionalEquivalent.{u} φ := by
  classical
  have hinvariant {W : Type u} (M : Model W Atom Agent) (S : Set W) (x : S) :
      M.Satisfies x.val φ ↔ (M.restrict S).Satisfies x φ := by
    obtain ⟨p, hp⟩ := φ.atoms.exists_notMem
    let R := revalue M p S
    have hpx : R.val p x.val := by
      change (if p = p then S x.val else M.val p x.val)
      rw [if_pos rfl]
      exact x.property
    have he := h R p x.val hpx
    rw [revalue_update_atom] at he
    exact (revalue_satisfies M p S φ hp x.val).symm.trans
      (he.trans ((targetCut_satisfies_restrict R S x φ).trans
        (revalue_restrict_satisfies M p S S φ hp x)))
  apply (propositionalEquivalent_iff_both_deletion φ).mpr
  refine ⟨(deletionMonotone_iff_submodelPreserved φ).mpr (fun M S x => (hinvariant M S x).mp), ?_⟩
  apply (deletionMonotone_neg_iff φ).mp
  apply (deletionMonotone_iff_submodelPreserved (.neg φ)).mpr
  intro W M S x hn ht
  exact hn ((hinvariant M S x).mpr ht)

theorem propositional_implies_atomInvariant (φ : Formula Atom Agent)
    (h : PropositionalEquivalent.{u} φ) : AtomAnnouncementInvariant.{u} φ := by
  obtain ⟨ψ, hψ, he⟩ := h
  intro W M p x _
  exact (he M x).trans ((hψ.update_satisfies_iff M (.atom p) x).symm.trans
    (he (M.update (.atom p)) x).symm)

theorem pal_atom_commutation_iff_invariant (φ : Formula Atom Agent) :
    (∀ {W : Type u} (M : Model W Atom Agent) (p : Atom),
      palUpdate M (.atom p) (palUpdate M φ.toPAL Set.univ) =
        palUpdate M φ.toPAL (palUpdate M (.atom p) Set.univ)) ↔
      AtomAnnouncementInvariant.{u} φ := by
  constructor
  · intro h W M p x hp
    have he := Iff.of_eq (congrArg (fun S : Set W => x ∈ S) (h M p))
    dsimp only at he
    rw [show (PALFormula.atom p) = (Formula.atom p).toPAL from rfl,
      palUpdate_twice_mem, palUpdate_twice_mem] at he
    change (M.Satisfies x φ ∧ M.val p x) ↔
      (M.val p x ∧ (M.update (.atom p)).Satisfies x φ) at he
    exact (and_iff_left hp).symm.trans (he.trans (and_iff_right hp))
  · intro h W M p
    ext x
    rw [show (PALFormula.atom p) = (Formula.atom p).toPAL from rfl,
      palUpdate_twice_mem, palUpdate_twice_mem]
    change (M.Satisfies x φ ∧ M.val p x) ↔
      (M.val p x ∧ (M.update (.atom p)).Satisfies x φ)
    exact ⟨fun ht => ⟨ht.2, (h M p x ht.2).mp ht.1⟩,
      fun ht => ⟨(h M p x ht.1).mpr ht.2, ht.1⟩⟩

theorem bpal_atom_commutation_iff_invariant [Nonempty Agent] (φ : Formula Atom Agent) :
    (∀ {W : Type u} (M : Model W Atom Agent) (p : Atom),
      (M.update φ).update (.atom p) = (M.update (.atom p)).update φ) ↔
      AtomAnnouncementInvariant.{u} φ := by
  classical
  constructor
  · intro h W M p x hp
    let a := Classical.arbitrary Agent
    let P := Extinction.predecessor M x a
    have hpx : P.val p (some x) := hp
    have he := h P p
    constructor
    · intro hφ
      have ht : ((P.update φ).update (.atom p)).rel a none (some x) :=
        ⟨⟨⟨rfl, rfl⟩, (Extinction.predecessor_truth M x a x φ).mpr hφ⟩, hpx⟩
      rw [he] at ht
      exact (predecessor_update_truth M x a (.atom p) φ x).mp ht.2
    · intro ht
      have he' : ((P.update (.atom p)).update φ).rel a none (some x) :=
        ⟨⟨⟨rfl, rfl⟩, hpx⟩, (predecessor_update_truth M x a (.atom p) φ x).mpr ht⟩
      rw [← he] at he'
      exact (Extinction.predecessor_truth M x a x φ).mp he'.1.2
  · intro h W M p
    apply Model.ext'
    · intro i x y
      change ((M.rel i x y ∧ M.Satisfies y φ) ∧ M.val p y) ↔
        ((M.rel i x y ∧ M.val p y) ∧ (M.update (.atom p)).Satisfies y φ)
      exact ⟨fun ht => ⟨⟨ht.1.1, ht.2⟩, (h M p y ht.2).mp ht.1.2⟩,
        fun ht => ⟨⟨ht.1.1, (h M p y ht.1.2).mpr ht.2⟩, ht.1.2⟩⟩
    · intro q x
      rfl

/-- Corollary 20(1) iff (4), PAL. -/
theorem propositional_iff_pal_atom_commutation [Infinite Atom] [Inhabited Atom]
    (φ : Formula Atom Agent) : PropositionalEquivalent.{u} φ ↔
      ∀ {W : Type u} (M : Model W Atom Agent) (p : Atom),
        palUpdate M (.atom p) (palUpdate M φ.toPAL Set.univ) =
          palUpdate M φ.toPAL (palUpdate M (.atom p) Set.univ) :=
  ⟨fun h => (pal_atom_commutation_iff_invariant φ).mpr (propositional_implies_atomInvariant φ h),
    fun h => atomInvariant_implies_propositional φ ((pal_atom_commutation_iff_invariant φ).mp h)⟩

/-- Corollary 20(1) iff (4), BPAL. -/
theorem propositional_iff_bpal_atom_commutation [Infinite Atom] [Inhabited Atom] [Nonempty Agent]
    (φ : Formula Atom Agent) : PropositionalEquivalent.{u} φ ↔
      ∀ {W : Type u} (M : Model W Atom Agent) (p : Atom),
        (M.update φ).update (.atom p) = (M.update (.atom p)).update φ :=
  ⟨fun h => (bpal_atom_commutation_iff_invariant φ).mpr (propositional_implies_atomInvariant φ h),
    fun h => atomInvariant_implies_propositional φ ((bpal_atom_commutation_iff_invariant φ).mp h)⟩

def PALMonotone (φ : Formula Atom Agent) : Prop :=
  ∀ α β, Entails.{u} α β → ∀ {W : Type u} (M : Model W Atom Agent) x,
    (M.Satisfies x α → (M.update α).Satisfies x φ) →
      (M.Satisfies x β → (M.update β).Satisfies x φ)

def BPALMonotone (φ : Formula Atom Agent) : Prop :=
  ∀ α β, Entails.{u} α β → ∀ {W : Type u} (M : Model W Atom Agent) x,
    (M.update α).Satisfies x φ → (M.update β).Satisfies x φ

/-- The final PAL assertion of Theorem 19. -/
theorem palMonotone_iff_valid [Inhabited Atom] (φ : Formula Atom Agent) :
    PALMonotone.{u} φ ↔ ∀ {W : Type u} (M : Model W Atom Agent) x, M.Satisfies x φ := by
  constructor
  · intro h W M x
    have ht := h Formula.falsum Formula.verum (fun M x hf => (Model.satisfies_falsum M x hf).elim)
      M x (fun hf => (Model.satisfies_falsum M x hf).elim) (Model.satisfies_verum M x)
    simpa only [model_update_verum] using ht
  · intro h α β hab W M x hα hβ
    exact h (M.update β) x

/-- The final BPAL assertion of Theorem 19; there is no executability guard. -/
theorem bpalMonotone_iff_negative (φ : Formula Atom Agent) :
    BPALMonotone.{u} φ ↔ BPALNegative.{u} φ := Iff.rfl

end PropertiesOfPublicAnnouncementsAsOperators
