import PropertiesOfPublicAnnouncementsAsOperators.Dynamics
import EventualAndStrongEventualNotionsInPublicAnnouncements.SingleAgent

/-! # The single-agent bound in the footnote to Theorem 24 -/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- Each single-agent cluster reaches common belief by the number of possible
valuations of the announcement's atoms. Worlds themselves need not be finite. -/
theorem singleAgent_common_bounded [Nonempty Agent] [Subsingleton Agent] [DecidableEq Atom]
    (M : Model World Atom Agent) (hM : IsK45 M) (φ : Formula Atom Agent) (root : World) :
    ∃ n : Nat, n ≤ 2 ^ φ.atoms.card ∧ Common (M.iterateUpdate φ n) root φ := by
  classical
  let a : Agent := Classical.choice inferInstance
  let P := {p : Atom // p ∈ φ.atoms}
  let valType : World → Set P := fun x => {p | M.val p.val x}
  let s : Nat → Set (Set P) := fun n =>
    valType '' {y | (M.iterateUpdate φ n).rel a root y}
  have hs : Antitone s := by
    intro n m hnm t ht
    obtain ⟨y, hy, rfl⟩ := ht
    exact ⟨y, M.iterateUpdate_rel_antitone φ hnm hy, rfl⟩
  obtain ⟨n, hn, heq⟩ := antitoneSet_stableStep_le_card s hs
  refine ⟨n, ?_, ?_⟩
  · simpa [P] using hn
  · intro y hy
    have hrooty := singleAgent_positive_path (M.iterateUpdate_isK45 hM φ n) a hy
    have hty : valType y ∈ s n := ⟨y, hrooty, rfl⟩
    rw [← heq] at hty
    obtain ⟨z, hz, hval⟩ := hty
    have hztruth : (M.iterateUpdate φ n).Satisfies z φ := hz.2
    have hy0 : M.rel a root y := (M.iterateUpdate_rel_iff φ n a root y).mp hrooty |>.1
    have hz0 : M.rel a root z :=
      (M.iterateUpdate_rel_iff φ (n + 1) a root z).mp hz |>.1
    have hiff := satisfies_iff_of_atoms_and_successors (M.iterateUpdate φ n) φ z y
      (fun p hp => by
        simp only [Model.iterateUpdate_val]
        exact Set.ext_iff.mp hval ⟨p, hp⟩)
      (singleAgent_iterate_successors_eq hM φ hz0 hy0 n)
    exact hiff.mp hztruth

theorem singleAgent_bpalRank_le [Nonempty Agent] [Subsingleton Agent] [DecidableEq Atom]
    (M : Model World Atom Agent) (hM : IsK45 M) (φ : Formula Atom Agent) :
    bpalRank M φ ≤ ((2 ^ φ.atoms.card : Nat) : Ordinal.{max u w}) := by
  apply bpalRank_le_of_stable
  unfold BPALStable
  rw [ordinalUpdate_succ, ordinalUpdate_natCast]
  apply Model.ext'
  · intro i x y
    constructor
    · exact And.left
    · intro hxy
      refine ⟨hxy, ?_⟩
      obtain ⟨n, hn, hC⟩ := singleAgent_common_bounded M hM φ x
      have hxy' := M.iterateUpdate_rel_antitone φ hn hxy
      have hφn := hC y (Relation.TransGen.single ⟨i, hxy'⟩)
      have hCy : Common (M.iterateUpdate φ n) y φ := by
        intro z hyz
        exact hC z ((Relation.TransGen.single ⟨i, hxy'⟩).trans hyz)
      have hCy' : Common (ordinalUpdate M φ (n : Ordinal.{max u w})) y φ := by
        simpa only [ordinalUpdate_natCast] using hCy
      have ht := common_ordinal_stage_permanent M φ hCy'
        (show (n : Ordinal.{max u w}) ≤ ((2 ^ φ.atoms.card : Nat) : Ordinal.{max u w})
          by exact_mod_cast hn) φ
      simp only [ordinalUpdate_natCast] at ht
      exact ht.mpr hφn
  · intro p x
    rfl

/-- In S5 the two ranks agree and are bounded by `2^k`, where `k` counts the
proposition letters occurring in the announced formula. -/
theorem singleAgent_s5_rank_bound [Nonempty Agent] [Subsingleton Agent] [DecidableEq Atom]
    (M : Model World Atom Agent) (hM : IsS5 M) (φ : Formula Atom Agent) :
    palRank M φ = bpalRank M φ ∧
      palRank M φ ≤ ((2 ^ φ.atoms.card : Nat) : Ordinal.{max u w}) := by
  have heq := stabilization_rank_eq_of_s5 M φ hM
  refine ⟨heq, ?_⟩
  rw [heq]
  exact singleAgent_bpalRank_le M hM.isK45 φ

end PropertiesOfPublicAnnouncementsAsOperators
