import EventualAndStrongEventualNotionsInPublicAnnouncements.CommonBelief
import ClassificationSigmaValidity.SingleAgentKD45

/-!
# Single-agent finite stabilization

The finite carrier used in the proof consists of valuations of the finitely many
atoms in the announced formula. The model's world type may be infinite.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements

open ClassificationSigmaValidity

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- Equal relevant valuations and equal successor sets give equal truth values.
No finiteness or frame assumption is required for this local observation. -/
theorem satisfies_iff_of_atoms_and_successors [DecidableEq Atom]
    (M : Model World Atom Agent) (φ : Formula Atom Agent) (x y : World)
    (hv : ∀ p ∈ φ.atoms, M.val p x ↔ M.val p y)
    (hr : ∀ a z, M.rel a x z ↔ M.rel a y z) :
    M.Satisfies x φ ↔ M.Satisfies y φ := by
  induction φ with
  | atom p => exact hv p (by simp [Formula.atoms])
  | neg ψ ih => exact not_congr (ih hv)
  | conj ψ χ ihψ ihχ =>
      exact and_congr
        (ihψ (fun p hp => hv p (Finset.mem_union_left _ hp)))
        (ihχ (fun p hp => hv p (Finset.mem_union_right _ hp)))
  | box a ψ ih =>
      change (∀ z, M.rel a x z → M.Satisfies z ψ) ↔
        (∀ z, M.rel a y z → M.Satisfies z ψ)
      exact forall_congr' fun z => imp_congr (hr a z) Iff.rfl

/-- Original successors in a single-agent K45 cluster retain identical successor
sets throughout the iteration, even after their incoming arrows disappear. -/
theorem singleAgent_iterate_successors_eq [Subsingleton Agent]
    {M : Model World Atom Agent} (hM : IsK45 M) (φ : Formula Atom Agent)
    {a : Agent} {root x y : World} (hx : M.rel a root x)
    (hy : M.rel a root y) (n : Nat) (b : Agent) (z : World) :
    (M.iterateUpdate φ n).rel b x z ↔
      (M.iterateUpdate φ n).rel b y z := by
  have hba : b = a := Subsingleton.elim _ _
  subst b
  rw [M.iterateUpdate_rel_iff, M.iterateUpdate_rel_iff]
  exact and_congr
    ((Frame.successor_eq_of_transitive_euclidean (R := M.rel a) (x := root) (y := x) (hM a).1 (hM a).2 hx z).symm.trans
      (Frame.successor_eq_of_transitive_euclidean (R := M.rel a) (x := root) (y := y) (hM a).1 (hM a).2 hy z)) Iff.rfl

/-- A positive path in a single-agent transitive model is a direct edge. -/
theorem singleAgent_positive_path [Subsingleton Agent]
    {M : Model World Atom Agent} (hM : IsK45 M) (a : Agent)
    {x y : World} (h : Relation.TransGen M.AnyStep x y) : M.rel a x y := by
  induction h with
  | single h =>
      obtain ⟨b, hb⟩ := h
      simpa only [Subsingleton.elim b a] using hb
  | @tail y z hy hyz ih =>
      obtain ⟨b, hb⟩ := hyz
      have hb' : M.rel a y z := by simpa only [Subsingleton.elim b a] using hb
      exact (hM a).1 ih hb'

/-- Lemma 6: every single-agent K45 pointed model reaches common belief after a
finite number of announcements. The initial model may have infinitely many worlds. -/
theorem singleAgent_exists_common [Nonempty Agent] [Subsingleton Agent]
    (M : Model World Atom Agent) (hM : IsK45 M)
    (φ : Formula Atom Agent) (root : World) :
    ∃ n : Nat, Common (M.iterateUpdate φ n) root φ := by
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
  obtain ⟨n, hn⟩ := FiniteDynamics.antitoneSet_exists_stableStep s hs
  refine ⟨n, ?_⟩
  intro y hy
  have hrooty := singleAgent_positive_path (M.iterateUpdate_isK45 hM φ n) a hy
  have hty : valType y ∈ s n := ⟨y, hrooty, rfl⟩
  rw [← hn] at hty
  obtain ⟨z, hz, hval⟩ := hty
  have hztruth : (M.iterateUpdate φ n).Satisfies z φ := hz.2
  have hx0 : M.rel a root y := (M.iterateUpdate_rel_iff φ n a root y).mp hrooty |>.1
  have hz0 : M.rel a root z :=
    (M.iterateUpdate_rel_iff φ (n + 1) a root z).mp hz |>.1
  have hiff := satisfies_iff_of_atoms_and_successors (M.iterateUpdate φ n) φ z y
    (fun p hp => by
      simp only [Model.iterateUpdate_val]
      exact Set.ext_iff.mp hval ⟨p, hp⟩)
    (singleAgent_iterate_successors_eq hM φ hz0 hx0 n)
  exact hiff.mp hztruth

/-- The witnessing common-belief stage can be chosen strictly positive. -/
theorem singleAgent_exists_positive_common [Nonempty Agent] [Subsingleton Agent]
    (M : Model World Atom Agent) (hM : IsK45 M)
    (φ : Formula Atom Agent) (root : World) :
    ∃ n : Nat, 1 ≤ n ∧ Common (M.iterateUpdate φ n) root φ := by
  obtain ⟨n, hn⟩ := singleAgent_exists_common (M.update φ) (M.update_isK45 hM φ) φ root
  refine ⟨1 + n, by omega, ?_⟩
  rw [M.iterateUpdate_add φ 1 n]
  exact hn

/-- The whole submodel generated initially by the point has a finite stable
step, including worlds that later cease to be reachable from the point. -/
theorem singleAgent_generated_exists_stableStep [Nonempty Agent] [Subsingleton Agent]
    (M : Model World Atom Agent) (hM : IsK45 M)
    (φ : Formula Atom Agent) (root : World) :
    ∃ n : Nat, 1 ≤ n ∧
      (M.generatedSubmodel root).iterateUpdate φ (n + 1) =
        (M.generatedSubmodel root).iterateUpdate φ n := by
  obtain ⟨n, hn, hC⟩ := singleAgent_exists_positive_common M hM φ root
  have hagree : (M.iterateUpdate φ n).LocallyAgrees
      ((M.iterateUpdate φ n).update φ) (M.generatedSet root) := by
    constructor
    · intro p y hy
      rfl
    · intro a y hy z hz
      constructor
      · intro hyz
        refine ⟨hyz, ?_⟩
        have hrootz : (M.iterateUpdate φ n).rel a root z := by
          rcases M.reachable_eq_or_rel hM hy with rfl | ⟨b, hb⟩
          · exact hyz
          · have hba : b = a := Subsingleton.elim _ _
            subst b
            obtain ⟨hyz0, hsurv⟩ := (M.iterateUpdate_rel_iff φ n a y z).mp hyz
            exact (M.iterateUpdate_rel_iff φ n a root z).mpr ⟨(hM a).1 hb hyz0, hsurv⟩
        exact hC z (Relation.TransGen.single ⟨a, hrootz⟩)
      · exact And.left
  have hrest := Model.restrict_eq_of_locallyAgrees hagree
  have hU : M.ForwardClosed (M.generatedSet root) := M.generatedSet_forwardClosed root
  refine ⟨n, hn, ?_⟩
  change (M.restrict (M.generatedSet root)).iterateUpdate φ (n + 1) =
    (M.restrict (M.generatedSet root)).iterateUpdate φ n
  rw [← M.restrict_iterateUpdate_eq _ hU φ (n + 1),
    ← M.restrict_iterateUpdate_eq _ hU φ n]
  exact hrest.symm

/-- Lemma 6, finite collapse: the finite S condition already implies strong
finite eventuality in the single-agent case. -/
theorem singleAgent_finiteStageCondition_implies_strongEventual
    [Nonempty Agent] [Subsingleton Agent]
    (i j : Bool) (φ : Formula Atom Agent)
    (hS : FiniteStageCondition.{u} i j φ) : StrongEventual.{u} i j φ := by
  intro W M hM x hx
  obtain ⟨N, hN, hC⟩ := singleAgent_exists_positive_common M hM φ x
  have htarget := hS N M hM x hx hC
  refine ⟨N, hN, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hiff := common_finite_permanent hC k φ
  rw [← M.iterateUpdate_add φ N k] at hiff
  cases j <;> simp only [HoldsBit, Pattern.HoldsBit, Bool.false_eq_true, ↓reduceIte] at *
  · exact fun h => htarget (hiff.mp h)
  · exact hiff.mpr htarget

end EventualAndStrongEventualNotionsInPublicAnnouncements
