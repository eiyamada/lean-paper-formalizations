import PropertiesOfPublicAnnouncementsAsOperators.Stabilization

/-! # Uniform finite stabilization and finite relativization -/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u v w z

variable {Atom : Type v} {Agent : Type w}

/-- Disjoint union of an arbitrary family of Kripke models. -/
def sumModel {I : Type z} {W : I → Type u}
    (models : ∀ i, Model (W i) Atom Agent) : Model (Sigma W) Atom Agent where
  rel a x y := ∃ h : x.1 = y.1, (models x.1).rel a x.2 (h.symm ▸ y.2)
  val p x := (models x.1).val p x.2

theorem sumModel_satisfies {I : Type z} {W : I → Type u}
    (models : ∀ i, Model (W i) Atom Agent) (i : I) (x : W i) (φ : Formula Atom Agent) :
    (sumModel models).Satisfies ⟨i, x⟩ φ ↔ (models i).Satisfies x φ := by
  induction φ generalizing i x with
  | atom p => rfl
  | neg φ ih => exact not_congr (ih i x)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ i x) (ihψ i x)
  | box a φ ih =>
      constructor
      · intro h y hxy
        exact (ih i y).mp (h ⟨i, y⟩ ⟨rfl, hxy⟩)
      · intro h y hy
        rcases y with ⟨j, y⟩
        rcases hy with ⟨hij, hxy⟩
        cases hij
        exact (ih i y).mpr (h y hxy)

theorem sumModel_update {I : Type z} {W : I → Type u}
    (models : ∀ i, Model (W i) Atom Agent) (φ : Formula Atom Agent) :
    (sumModel models).update φ = sumModel (fun i => (models i).update φ) := by
  apply Model.ext'
  · intro a ⟨i, x⟩ ⟨j, y⟩
    constructor
    · rintro ⟨⟨hij, hxy⟩, hφ⟩
      cases hij
      exact ⟨rfl, hxy, (sumModel_satisfies models i y φ).mp hφ⟩
    · rintro ⟨hij, hxy, hφ⟩
      cases hij
      exact ⟨⟨rfl, hxy⟩, (sumModel_satisfies models i y φ).mpr hφ⟩
  · intro p x
    rfl

theorem sumModel_iterate {I : Type z} {W : I → Type u}
    (models : ∀ i, Model (W i) Atom Agent) (φ : Formula Atom Agent) (n : Nat) :
    (sumModel models).iterateUpdate φ n = sumModel (fun i => (models i).iterateUpdate φ n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Model.iterateUpdate_succ, ih, sumModel_update]

theorem sumModel_injective {I : Type z} {W : I → Type u}
    {models models' : ∀ i, Model (W i) Atom Agent}
    (h : sumModel models = sumModel models') (i : I) : models i = models' i := by
  apply Model.ext'
  · intro a x y
    have heq := congrArg (fun M => M.rel a ⟨i, x⟩ ⟨i, y⟩) h
    simpa [sumModel] using (Iff.of_eq heq)
  · intro p x
    exact Iff.of_eq (congrArg (fun M => M.val p ⟨i, x⟩) h)

theorem bpalStable_nat_iff {World : Type u} (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (n : Nat) :
    BPALStable M φ (n : Ordinal.{max u w}) ↔
      M.iterateUpdate φ (n + 1) = M.iterateUpdate φ n := by
  simp only [BPALStable, ← Ordinal.natCast_succ, ordinalUpdate_natCast]

theorem palDomain_nat_iff {World : Type u} (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (n : Nat) (x : World) :
    x ∈ palDomain M φ (n : Ordinal.{max u w}) ↔ M.Survives φ n x := by
  constructor
  · intro h m hm
    simpa using h (m : Ordinal.{max u w}) (by exact_mod_cast hm)
  · intro h β hβ
    obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp
      (lt_trans hβ (Ordinal.nat_lt_omega0 n))
    exact (ordinalUpdate_natCast M φ m) ▸ h m (by exact_mod_cast hβ)

theorem palDomain_sumModel {I : Type z} {W : I → Type u}
    (models : ∀ i, Model (W i) Atom Agent) (φ : Formula Atom Agent)
    (n : Nat) (i : I) (x : W i) :
    (⟨i, x⟩ : Sigma W) ∈ palDomain (sumModel models) φ (n : Ordinal.{max u w z}) ↔
      x ∈ palDomain (models i) φ (n : Ordinal.{max u w}) := by
  rw [palDomain_nat_iff, palDomain_nat_iff]
  unfold Model.Survives
  apply forall_congr'
  intro m
  apply forall_congr'
  intro _hm
  rw [sumModel_iterate, sumModel_satisfies]

/-- Disjoint union turns unbounded finite stabilization times into a model
that fails to stabilize at every finite stage. No compactness assumption is used. -/
theorem bpal_finite_uniform (φ : Formula Atom Agent)
    (hfinite : ∀ {World : Type u} (M : Model World Atom Agent),
      ∃ n : Nat, BPALStable M φ (n : Ordinal.{max u w})) :
    ∃ N : Nat, ∀ {World : Type u} (M : Model World Atom Agent),
      BPALStable M φ (N : Ordinal.{max u w}) := by
  classical
  by_contra! hnone
  choose W models hmodels using hnone
  obtain ⟨N, hN⟩ := hfinite (sumModel models)
  apply hmodels N
  rw [bpalStable_nat_iff] at hN ⊢
  rw [sumModel_iterate, sumModel_iterate] at hN
  exact sumModel_injective hN N

theorem pal_finite_uniform (φ : Formula Atom Agent)
    (hfinite : ∀ {World : Type u} (M : Model World Atom Agent),
      ∃ n : Nat, PALStable M φ (n : Ordinal.{max u w})) :
    ∃ N : Nat, ∀ {World : Type u} (M : Model World Atom Agent),
      PALStable M φ (N : Ordinal.{max u w}) := by
  classical
  by_contra! hnone
  choose W models hmodels using hnone
  obtain ⟨N, hN⟩ := hfinite (sumModel models)
  apply hmodels N
  apply Set.ext
  intro x
  change x ∈ palDomain (models N) φ ((N + 1 : Nat) : Ordinal.{max u w}) ↔
    x ∈ palDomain (models N) φ (N : Ordinal.{max u w})
  rw [← palDomain_sumModel models φ (N + 1) N x,
    ← palDomain_sumModel models φ N N x]
  exact Iff.of_eq (congrArg (fun S : Set (Sigma W) => (⟨N, x⟩ : Sigma W) ∈ S) hN)

theorem palRank_lt_omega_iff {World : Type u} (M : Model World Atom Agent)
    (φ : Formula Atom Agent) :
    palRank M φ < Ordinal.omega0 ↔ ∃ n : Nat, PALStable M φ (n : Ordinal.{max u w}) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp h
    exact ⟨n, hn ▸ palRank_stable M φ⟩
  · rintro ⟨n, hn⟩
    exact lt_of_le_of_lt (palRank_le_of_stable M φ hn) (Ordinal.nat_lt_omega0 n)

theorem bpalRank_lt_omega_iff {World : Type u} (M : Model World Atom Agent)
    (φ : Formula Atom Agent) :
    bpalRank M φ < Ordinal.omega0 ↔ ∃ n : Nat, BPALStable M φ (n : Ordinal.{max u w}) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp h
    exact ⟨n, hn ▸ bpalRank_stable M φ⟩
  · rintro ⟨n, hn⟩
    exact lt_of_le_of_lt (bpalRank_le_of_stable M φ hn) (Ordinal.nat_lt_omega0 n)

/-- Theorem 25(1) iff (2), PAL. -/
theorem pal_finite_stabilization_iff_uniform (φ : Formula Atom Agent) :
    (∀ {World : Type u} (M : Model World Atom Agent), palRank M φ < Ordinal.omega0) ↔
      ∃ N : Nat, 1 ≤ N ∧ ∀ {World : Type u} (M : Model World Atom Agent),
        palRank M φ ≤ (N : Ordinal.{max u w}) := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := pal_finite_uniform φ (fun M => (palRank_lt_omega_iff M φ).mp (h M))
    refine ⟨N + 1, by omega, fun M => ?_⟩
    exact le_trans (palRank_le_of_stable M φ (hN M)) (Order.le_succ _)
  · rintro ⟨N, _, hN⟩ World M
    exact lt_of_le_of_lt (hN M) (Ordinal.nat_lt_omega0 N)

/-- Theorem 25(1) iff (2), BPAL. -/
theorem bpal_finite_stabilization_iff_uniform (φ : Formula Atom Agent) :
    (∀ {World : Type u} (M : Model World Atom Agent), bpalRank M φ < Ordinal.omega0) ↔
      ∃ N : Nat, 1 ≤ N ∧ ∀ {World : Type u} (M : Model World Atom Agent),
        bpalRank M φ ≤ (N : Ordinal.{max u w}) := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := bpal_finite_uniform φ (fun M => (bpalRank_lt_omega_iff M φ).mp (h M))
    refine ⟨N + 1, by omega, fun M => ?_⟩
    exact le_trans (bpalRank_le_of_stable M φ (hN M)) (Order.le_succ _)
  · rintro ⟨N, _, hN⟩ World M
    exact lt_of_le_of_lt (hN M) (Ordinal.nat_lt_omega0 N)

/-- The paper's finite relativization formulas. `announcementReduce α ψ`
is exactly `ψ^α`, with modal quantifiers restricted by `α`. -/
def theta [Inhabited Atom] (φ : Formula Atom Agent) : Nat → Formula Atom Agent
  | 0 => Formula.verum
  | n + 1 => .conj (theta φ n) (Formula.announcementReduce (theta φ n) φ)

theorem theta_truth [Inhabited Atom] {World : Type u} (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (n : Nat) (x : World) :
    M.Satisfies x (theta φ n) ↔ x ∈ palDomain M φ (n : Ordinal.{max u w}) := by
  induction n generalizing x with
  | zero => simp [theta]
  | succ n ih =>
      have hu : M.update (theta φ n) = ordinalUpdate M φ (n : Ordinal.{max u w}) := by
        apply Model.ext'
        · intro i x y
          rw [Model.update_rel, ordinalUpdate_rel_iff, ih]
          rfl
        · intro p x
          exact (ordinalUpdate_val M φ n p x).symm
      rw [theta, Model.satisfies_and, ← Model.satisfies_announcementReduce,
        hu, ih, Ordinal.natCast_succ, palDomain_succ]
      rfl

/-- Theorem 25(2) iff (3), with the bound fixed, in PAL. -/
theorem pal_stable_iff_theta_equivalent [Inhabited Atom] {World : Type u}
    (M : Model World Atom Agent) (φ : Formula Atom Agent) (N : Nat) :
    palRank M φ ≤ (N : Ordinal.{max u w}) ↔
      ∀ x, M.Satisfies x (theta φ N) ↔ M.Satisfies x (theta φ (N + 1)) := by
  rw [palRank_le_iff]
  constructor
  · intro h x
    rw [theta_truth, theta_truth]
    exact Iff.of_eq (congrArg (fun S : Set World => x ∈ S) h.symm)
  · intro h
    apply Set.ext
    intro x
    exact ((theta_truth M φ (N + 1) x).symm.trans ((h x).symm)).trans
      (theta_truth M φ N x)

end PropertiesOfPublicAnnouncementsAsOperators
