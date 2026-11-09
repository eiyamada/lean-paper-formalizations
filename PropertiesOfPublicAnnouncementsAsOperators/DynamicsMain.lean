import PropertiesOfPublicAnnouncementsAsOperators.FiniteStabilization
import PropertiesOfPublicAnnouncementsAsOperators.Incoming
import PropertiesOfPublicAnnouncementsAsOperators.PALFixedPoints

/-! # Theorems 25 and 26, assembled with their global quantifiers -/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

theorem domainModel_inter (M : Model World Atom Agent) (S T : Set World) :
    PAL.domainModel (PAL.domainModel M S) T = PAL.domainModel M (S ∩ T : Set World) := by
  apply Model.ext'
  · intro i x y
    change (T y ∧ S y ∧ M.rel i x y) ↔ (S y ∧ T y) ∧ M.rel i x y
    tauto
  · intro p x
    rfl

@[simp] theorem palRestart_zero (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (S : Set World) : palRestart M φ S 0 = S := by
  simp only [palRestart, palDomain_zero, Set.inter_univ]

/-- `palRestart` iterates the actual PAL operator on an arbitrary current
domain, not only on the domains occurring in the original run. -/
theorem palRestart_succ (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (S : Set World) (α : Ordinal.{max u w}) :
    palRestart M φ S (Order.succ α) = palUpdate M φ.toPAL (palRestart M φ S α) := by
  unfold palRestart
  rw [palDomain_succ]
  ext x
  change (S x ∧ x ∈ palDomain (PAL.domainModel M S) φ α ∧
    (EventualAndStrongEventualNotionsInPublicAnnouncements.ordinalUpdate
      (PAL.domainModel M S) φ α).Satisfies x φ) ↔
    (S x ∧ x ∈ palDomain (PAL.domainModel M S) φ α) ∧
      PAL.Satisfies M (S ∩ palDomain (PAL.domainModel M S) φ α : Set World) x φ.toPAL
  rw [PAL.satisfies_toPAL, ← palDomain_domainModel, domainModel_inter]
  exact and_assoc.symm

theorem palRestart_limit (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (S : Set World) {α : Ordinal.{max u w}} (hα : Order.IsSuccLimit α) :
    palRestart M φ S α = ⋂ β < α, palRestart M φ S β := by
  unfold palRestart
  rw [palDomain_limit _ _ hα]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  exact ⟨fun h β hβ => ⟨h.1, h.2 β hβ⟩,
    fun h => ⟨(h 0 hα.bot_lt).1, fun β hβ => (h β hβ).2⟩⟩

/-- Theorem 25, PAL: finite stabilization, a uniform positive bound,
stability of the relativization formulas, and idempotence of a finite power. -/
theorem theorem25_pal [Inhabited Atom] (φ : Formula Atom Agent) :
    ((∀ {W : Type u} (M : Model W Atom Agent), palRank M φ < Ordinal.omega0) ↔
      ∃ N : Nat, 1 ≤ N ∧ ∀ {W : Type u} (M : Model W Atom Agent),
        palRank M φ ≤ (N : Ordinal.{max u w})) ∧
    ((∀ {W : Type u} (M : Model W Atom Agent), palRank M φ < Ordinal.omega0) ↔
      ∃ N : Nat, 1 ≤ N ∧ ∀ {W : Type u} (M : Model W Atom Agent) x,
        M.Satisfies x (theta φ N) ↔ M.Satisfies x (theta φ (N + 1))) ∧
    ((∀ {W : Type u} (M : Model W Atom Agent), palRank M φ < Ordinal.omega0) ↔
      ∃ N : Nat, 1 ≤ N ∧ ∀ {W : Type u} (M : Model W Atom Agent),
        palRestart M φ (palDomain M φ (N : Ordinal.{max u w})) (N : Ordinal.{max u w}) =
          palDomain M φ (N : Ordinal.{max u w})) := by
  have h12 := pal_finite_stabilization_iff_uniform.{u} φ
  refine ⟨h12, h12.trans ?_, h12.trans ?_⟩
  · constructor
    · rintro ⟨N, hN, h⟩
      exact ⟨N, hN, fun M => (pal_stable_iff_theta_equivalent M φ N).mp (h M)⟩
    · rintro ⟨N, hN, h⟩
      exact ⟨N, hN, fun M => (pal_stable_iff_theta_equivalent M φ N).mpr (h M)⟩
  · constructor
    · rintro ⟨N, hN, h⟩
      exact ⟨N, hN, fun M => (pal_finite_stable_iff_idempotent M φ N hN).mp (h M)⟩
    · rintro ⟨N, hN, h⟩
      exact ⟨N, hN, fun M => (pal_finite_stable_iff_idempotent M φ N hN).mpr (h M)⟩

/-- Theorem 25, BPAL, using the same finite relativization formulas. -/
theorem theorem25_bpal [Inhabited Atom] [Nonempty Agent] (φ : Formula Atom Agent) :
    ((∀ {W : Type u} (M : Model W Atom Agent), bpalRank M φ < Ordinal.omega0) ↔
      ∃ N : Nat, 1 ≤ N ∧ ∀ {W : Type u} (M : Model W Atom Agent),
        bpalRank M φ ≤ (N : Ordinal.{max u w})) ∧
    ((∀ {W : Type u} (M : Model W Atom Agent), bpalRank M φ < Ordinal.omega0) ↔
      ∃ N : Nat, 1 ≤ N ∧ ∀ {W : Type u} (M : Model W Atom Agent) x,
        M.Satisfies x (theta φ N) ↔ M.Satisfies x (theta φ (N + 1))) ∧
    ((∀ {W : Type u} (M : Model W Atom Agent), bpalRank M φ < Ordinal.omega0) ↔
      ∃ N : Nat, 1 ≤ N ∧ ∀ {W : Type u} (M : Model W Atom Agent),
        (M.iterateUpdate φ N).iterateUpdate φ N = M.iterateUpdate φ N) := by
  have h12 := bpal_finite_stabilization_iff_uniform.{u} φ
  refine ⟨h12, h12.trans ?_, h12.trans ?_⟩
  · constructor
    · rintro ⟨N, hN, h⟩
      have hP : ∀ {W : Type u} (M : Model W Atom Agent),
          palRank M φ ≤ (N : Ordinal.{max u w}) :=
        (global_palRank_le_iff_bpalRank_le φ (N : Ordinal.{max u w})).mpr h
      exact ⟨N, hN, fun M => (pal_stable_iff_theta_equivalent M φ N).mp (hP M)⟩
    · rintro ⟨N, hN, h⟩
      refine ⟨N, hN, ?_⟩
      apply (global_palRank_le_iff_bpalRank_le φ (N : Ordinal.{max u w})).mp
      exact fun M => (pal_stable_iff_theta_equivalent M φ N).mpr (h M)
  · constructor
    · rintro ⟨N, hN, h⟩
      exact ⟨N, hN, fun M => (bpal_finite_stable_iff_idempotent M φ N hN).mp (h M)⟩
    · rintro ⟨N, hN, h⟩
      exact ⟨N, hN, fun M => (bpal_finite_stable_iff_idempotent M φ N hN).mpr (h M)⟩

/-- Theorem 26, PAL, with global quantifiers on all three conditions. -/
theorem theorem26_pal (φ : Formula Atom Agent) :
    ((∀ {W : Type u} (M : Model W Atom Agent), palRank M φ ≤ Ordinal.omega0) ↔
      ∀ {W : Type u} (M : Model W Atom Agent),
        palRestart M φ (palDomain M φ Ordinal.omega0) Ordinal.omega0 =
          palDomain M φ Ordinal.omega0) ∧
    ((∀ {W : Type u} (M : Model W Atom Agent), palRank M φ ≤ Ordinal.omega0) ↔
      ∀ {W : Type u} (M : Model W Atom Agent),
        palRestart M φ (palDomain M φ Ordinal.omega0) 1 =
          palRestart M φ (palDomain M φ 1) Ordinal.omega0) := by
  exact ⟨⟨fun h {W} M => (pal_omega_stable_iff_idempotent M φ).mp (h M),
    fun h {W} M => (pal_omega_stable_iff_idempotent M φ).mpr (h M)⟩,
    ⟨fun h {W} M => (pal_omega_stable_iff_commutes M φ).mp (h M),
      fun h {W} M => (pal_omega_stable_iff_commutes M φ).mpr (h M)⟩⟩

open EventualAndStrongEventualNotionsInPublicAnnouncements in
/-- Theorem 26, BPAL, with global quantifiers on all three conditions. -/
theorem theorem26_bpal (φ : Formula Atom Agent) :
    ((∀ {W : Type u} (M : Model W Atom Agent), bpalRank M φ ≤ Ordinal.omega0) ↔
      ∀ {W : Type u} (M : Model W Atom Agent),
        ordinalUpdate (ordinalUpdate M φ Ordinal.omega0) φ Ordinal.omega0 =
          ordinalUpdate M φ Ordinal.omega0) ∧
    ((∀ {W : Type u} (M : Model W Atom Agent), bpalRank M φ ≤ Ordinal.omega0) ↔
      ∀ {W : Type u} (M : Model W Atom Agent),
        (ordinalUpdate M φ Ordinal.omega0).update φ =
          ordinalUpdate (M.update φ) φ Ordinal.omega0) := by
  exact ⟨⟨fun h {W} M => (bpal_omega_stable_iff_idempotent M φ).mp (h M),
    fun h {W} M => (bpal_omega_stable_iff_idempotent M φ).mpr (h M)⟩,
    ⟨fun h {W} M => (bpal_omega_stable_iff_commutes M φ).mp (h M),
      fun h {W} M => (bpal_omega_stable_iff_commutes M φ).mpr (h M)⟩⟩

theorem theorem26_pal_iff_bpal [Nonempty Agent] (φ : Formula Atom Agent) :
    (∀ {W : Type u} (M : Model W Atom Agent), palRank M φ ≤ Ordinal.omega0) ↔
      (∀ {W : Type u} (M : Model W Atom Agent), bpalRank M φ ≤ Ordinal.omega0) :=
  global_palRank_le_iff_bpalRank_le φ Ordinal.omega0

end PropertiesOfPublicAnnouncementsAsOperators
