import PropertiesOfPublicAnnouncementsAsOperators.Dynamics

/-! # Image-finite stabilization at omega -/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u v w

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- Every state has finitely many successors for each individual agent. -/
def ImageFinite (M : Model World Atom Agent) : Prop :=
  ∀ i x, {y | M.rel i x y}.Finite

theorem palDomain_omega_iff (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (x : World) :
    x ∈ palDomain M φ Ordinal.omega0 ↔ ∀ n : Nat, (M.iterateUpdate φ n).Satisfies x φ := by
  constructor
  · intro h n
    simpa using h (n : Ordinal.{max u w}) (Ordinal.nat_lt_omega0 n)
  · intro h β hβ
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hβ
    simpa using h n

theorem omega_rel_iff (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (i : Agent) (x y : World) :
    (ordinalUpdate M φ Ordinal.omega0).rel i x y ↔
      ∀ n : Nat, (M.iterateUpdate φ n).rel i x y := by
  rw [ordinalUpdate_limit_rel_iff M φ Ordinal.isSuccLimit_omega0]
  constructor
  · intro h n
    simpa using h (n : Ordinal.{max u w}) (Ordinal.nat_lt_omega0 n)
  · intro h β hβ
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hβ
    simpa using h n

/-- Each individual arrow has already reached its omega value at a finite stage. -/
theorem eventually_omega_rel (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (i : Agent) (x y : World) :
    ∃ N : Nat, ∀ n, N ≤ n →
      ((M.iterateUpdate φ n).rel i x y ↔ (ordinalUpdate M φ Ordinal.omega0).rel i x y) := by
  classical
  by_cases hω : (ordinalUpdate M φ Ordinal.omega0).rel i x y
  · exact ⟨0, fun n _ => ⟨fun _ => hω, fun _ => (omega_rel_iff M φ i x y).mp hω n⟩⟩
  · have hn : ¬∀ n : Nat, (M.iterateUpdate φ n).rel i x y :=
      fun h => hω ((omega_rel_iff M φ i x y).mpr h)
    obtain ⟨N, hN⟩ := not_forall.mp hn
    refine ⟨N, fun n hNn => ?_⟩
    exact iff_of_false (fun h => hN (M.iterateUpdate_rel_antitone φ hNn h)) hω

/-- Finitely many eventual assertions have a common finite threshold. -/
theorem finite_uniform_threshold {X : Type*} {s : Set X} (hs : s.Finite)
    (P : X → Nat → Prop) (h : ∀ x ∈ s, ∃ N, ∀ n, N ≤ n → P x n) :
    ∃ N, ∀ x ∈ s, ∀ n, N ≤ n → P x n := by
  classical
  letI : Fintype s := hs.fintype
  have hx (x : s) : ∃ N, ∀ n, N ≤ n → P x.val n := h x.val x.property
  choose bound hbound using hx
  refine ⟨Finset.univ.sup bound, fun x hx n hn => ?_⟩
  exact hbound ⟨x, hx⟩ n (le_trans (Finset.le_sup (f := bound)
    (Finset.mem_univ (⟨x, hx⟩ : s))) hn)

/-- Every finite-depth static formula eventually has its omega truth value
on an image-finite model. The proof does not require finitely many agents. -/
theorem eventually_omega_satisfies (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (hM : ImageFinite M) (ψ : Formula Atom Agent) (x : World) :
    ∃ N : Nat, ∀ n, N ≤ n →
      ((M.iterateUpdate φ n).Satisfies x ψ ↔
        (ordinalUpdate M φ Ordinal.omega0).Satisfies x ψ) := by
  induction ψ generalizing x with
  | atom p =>
      exact ⟨0, fun n _ => by simp⟩
  | neg ψ ih =>
      obtain ⟨N, hN⟩ := ih x
      exact ⟨N, fun n hn => not_congr (hN n hn)⟩
  | conj ψ χ ihψ ihχ =>
      obtain ⟨N, hN⟩ := ihψ x
      obtain ⟨K, hK⟩ := ihχ x
      refine ⟨max N K, fun n hn => ?_⟩
      exact and_congr (hN n (le_trans (le_max_left _ _) hn))
        (hK n (le_trans (le_max_right _ _) hn))
  | box i ψ ih =>
      have hlocal (y : World) (_hy : y ∈ {y | M.rel i x y}) :
          ∃ N, ∀ n, N ≤ n →
            (((M.iterateUpdate φ n).rel i x y ↔
                (ordinalUpdate M φ Ordinal.omega0).rel i x y) ∧
              ((M.iterateUpdate φ n).Satisfies y ψ ↔
                (ordinalUpdate M φ Ordinal.omega0).Satisfies y ψ)) := by
        obtain ⟨N, hN⟩ := eventually_omega_rel M φ i x y
        obtain ⟨K, hK⟩ := ih y
        exact ⟨max N K, fun n hn =>
          ⟨hN n (le_trans (le_max_left _ _) hn), hK n (le_trans (le_max_right _ _) hn)⟩⟩
      obtain ⟨N, hN⟩ := finite_uniform_threshold (hM i x) _ hlocal
      refine ⟨N, fun n hn => ?_⟩
      constructor
      · intro h y hxy
        have hy : M.rel i x y := ((ordinalUpdate_rel_iff M φ _ i x y).mp hxy).1
        have hlocal := hN y hy n hn
        exact hlocal.2.mp (h y (hlocal.1.mpr hxy))
      · intro h y hxy
        have hy : M.rel i x y := (M.iterateUpdate_rel_iff φ n i x y).mp hxy |>.1
        have hlocal := hN y hy n hn
        exact hlocal.2.mpr (h y (hlocal.1.mp hxy))

/-- Theorem 24(3): image-finite models are PAL-stable at omega. -/
theorem palStable_omega_of_imageFinite (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (hM : ImageFinite M) : PALStable M φ Ordinal.omega0 := by
  apply (palStable_iff M φ _).mpr
  intro x hx
  obtain ⟨N, hN⟩ := eventually_omega_satisfies M φ hM φ x
  exact (hN N le_rfl).mp ((palDomain_omega_iff M φ x).mp hx N)

theorem imageFinite_stabilization (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (hM : ImageFinite M) :
    palRank M φ ≤ Ordinal.omega0 ∧ bpalRank M φ ≤ Ordinal.omega0 := by
  have hP := palRank_le_of_stable M φ (palStable_omega_of_imageFinite M φ hM)
  exact ⟨hP, le_trans (stabilization_rank_comparison M φ).1 hP⟩

end PropertiesOfPublicAnnouncementsAsOperators
