import ClassificationSigmaValidity.Semantics
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Finite dynamics of iterated believed announcements

Every iterated update has the original valuation and an accessibility relation
obtained by retaining arrows whose targets survived all earlier announcements.
Thus the dynamics are controlled by a decreasing sequence of sets of worlds.
On a finite world type that sequence, the models, and all truth traces eventually
stabilize.

The drop-set lemmas near the end of the file isolate the strict-descent argument
used by the paper's nonexistence proofs: whenever the truth of any formula changes
between consecutive iterates, at least one world is removed from the survivor set.
-/

namespace ClassificationSigmaValidity

universe u v w

namespace FiniteDynamics

/-- A decreasing sequence of subsets of a finite type is eventually constant. -/
theorem antitoneSet_eventually_constant {α : Type*} [Finite α]
    (s : Nat -> Set α) (hs : Antitone s) :
    ∃ n, ∀ m, n <= m -> s m = s n := by
  classical
  letI := Fintype.ofFinite α
  let f : Nat -> Finset α := fun n => Finset.univ.filter fun x => x ∈ s n
  have hrange : (Set.range f).Finite := Set.toFinite _
  obtain ⟨a, ⟨n, rfl⟩, hmin⟩ :=
    Set.exists_min_image (Set.range f) Finset.card hrange (Set.range_nonempty f)
  refine ⟨n, fun m hnm => ?_⟩
  have hsubset : f m ⊆ f n := by
    intro x hx
    have hx' : x ∈ s m := by simpa [f] using hx
    have : x ∈ s n := hs hnm hx'
    simpa [f] using this
  have hcard : (f n).card <= (f m).card := hmin (f m) ⟨m, rfl⟩
  have heq : f m = f n := Finset.eq_of_subset_of_card_le hsubset hcard
  ext x
  have hx := congrArg (fun t : Finset α => x ∈ t) heq
  simpa [f] using hx

/-- A decreasing sequence of subsets of a finite type has a stable step. -/
theorem antitoneSet_exists_stableStep {α : Type*} [Finite α]
    (s : Nat -> Set α) (hs : Antitone s) :
    ∃ n, s (n + 1) = s n := by
  obtain ⟨n, hn⟩ := antitoneSet_eventually_constant s hs
  exact ⟨n, hn (n + 1) (Nat.le_succ n)⟩

/-- There cannot be a strict decrease at every step of a decreasing sequence of
subsets of a finite type. -/
theorem antitoneSet_not_strictly_decreasing {α : Type*} [Finite α]
    (s : Nat -> Set α) (hs : Antitone s) :
    ¬(∀ n, s (n + 1) ⊂ s n) := by
  rintro hstrict
  obtain ⟨n, heq⟩ := antitoneSet_exists_stableStep s hs
  exact (Set.ssubset_iff_subset_ne.mp (hstrict n)).2 heq

end FiniteDynamics

namespace Model

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- Worlds that satisfy the announced formula at every time before `n`. -/
def survivorSet (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (n : Nat) : Set World :=
  {x | M.Survives phi n x}

@[simp] theorem mem_survivorSet (M : Model World Atom Agent)
    (phi : Formula Atom Agent) (n : Nat) (x : World) :
    x ∈ M.survivorSet phi n <-> M.Survives phi n x := Iff.rfl

@[simp] theorem survivorSet_zero (M : Model World Atom Agent)
    (phi : Formula Atom Agent) : M.survivorSet phi 0 = Set.univ := by
  ext x
  simp [survivorSet]

/-- The next survivor set is obtained by intersecting the current survivor set
with the current truth set of the announced formula. -/
theorem survivorSet_succ (M : Model World Atom Agent)
    (phi : Formula Atom Agent) (n : Nat) :
    M.survivorSet phi (n + 1) =
      M.survivorSet phi n ∩ (M.iterateUpdate phi n).truthSet phi := by
  ext x
  simp [survivorSet, truthSet, survives_succ_iff]

/-- Survivor sets decrease with time. -/
theorem survivorSet_antitone (M : Model World Atom Agent)
    (phi : Formula Atom Agent) : Antitone (M.survivorSet phi) := by
  intro m n hmn x hx
  exact M.survives_antitone phi hmn hx

theorem survivorSet_succ_subset (M : Model World Atom Agent)
    (phi : Formula Atom Agent) (n : Nat) :
    M.survivorSet phi (n + 1) ⊆ M.survivorSet phi n :=
  M.survivorSet_antitone phi (Nat.le_succ n)

/-- Worlds that are discarded precisely at update number `n + 1`. -/
def dropSet (M : Model World Atom Agent) (phi : Formula Atom Agent)
    (n : Nat) : Set World :=
  M.survivorSet phi n \ M.survivorSet phi (n + 1)

/-- A world is dropped at stage `n` exactly when it survived all earlier stages
and the announced formula is false there at time `n`. -/
theorem mem_dropSet_iff (M : Model World Atom Agent)
    (phi : Formula Atom Agent) (n : Nat) (x : World) :
    x ∈ M.dropSet phi n <->
      M.Survives phi n x ∧
        ¬(M.iterateUpdate phi n).Satisfies x phi := by
  rw [dropSet, Set.mem_diff, mem_survivorSet, mem_survivorSet,
    survives_succ_iff]
  tauto

/-- A world cannot be dropped at two distinct stages. -/
theorem dropSet_disjoint_of_lt (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {m n : Nat} (hmn : m < n) :
    Disjoint (M.dropSet phi m) (M.dropSet phi n) := by
  rw [Set.disjoint_left]
  intro x hxm hxn
  rcases hxm with ⟨_, hxmNext⟩
  rcases hxn with ⟨hxnNow, _⟩
  exact hxmNext (M.survivorSet_antitone phi (Nat.succ_le_of_lt hmn) hxnNow)

/-- The survivor-set form of the iterated accessibility-relation equation. -/
theorem iterateUpdate_rel_iff_survivorSet (M : Model World Atom Agent)
    (phi : Formula Atom Agent) (n : Nat) (i : Agent) (x y : World) :
    (M.iterateUpdate phi n).rel i x y <->
      M.rel i x y ∧ y ∈ M.survivorSet phi n := by
  simpa only [mem_survivorSet] using M.iterateUpdate_rel_iff phi n i x y

/-- Every arrow present at a later iterate was already present at every earlier
iterate. -/
theorem iterateUpdate_rel_antitone (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {m n : Nat} (hmn : m <= n)
    {i : Agent} {x y : World} :
    (M.iterateUpdate phi n).rel i x y ->
      (M.iterateUpdate phi m).rel i x y := by
  rw [M.iterateUpdate_rel_iff_survivorSet phi n i x y,
    M.iterateUpdate_rel_iff_survivorSet phi m i x y]
  rintro ⟨hxy, hy⟩
  exact ⟨hxy, M.survivorSet_antitone phi hmn hy⟩

/-- Equal survivor sets determine equal iterated models. -/
theorem iterateUpdate_eq_of_survivorSet_eq (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {m n : Nat}
    (h : M.survivorSet phi m = M.survivorSet phi n) :
    M.iterateUpdate phi m = M.iterateUpdate phi n := by
  apply Model.ext'
  · intro i x y
    have hy : M.Survives phi m y <-> M.Survives phi n y := by
      change y ∈ M.survivorSet phi m <-> y ∈ M.survivorSet phi n
      rw [h]
    rw [iterateUpdate_rel_iff, iterateUpdate_rel_iff, hy]
  · intro p x
    rw [iterateUpdate_val, iterateUpdate_val]

/-- A stable survivor-set step gives a stable model step. -/
theorem iterateUpdate_eq_of_survivorSet_step (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {n : Nat}
    (h : M.survivorSet phi (n + 1) = M.survivorSet phi n) :
    M.iterateUpdate phi (n + 1) = M.iterateUpdate phi n :=
  M.iterateUpdate_eq_of_survivorSet_eq phi h

/-- Once two consecutive iterated models agree, every later iterate agrees with
them. -/
theorem iterateUpdate_eq_of_ge_of_step (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {n m : Nat}
    (hstep : M.iterateUpdate phi (n + 1) = M.iterateUpdate phi n)
    (hnm : n <= m) :
    M.iterateUpdate phi m = M.iterateUpdate phi n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact M.iterateUpdate_eq_of_step phi hstep k

/-- At a stable step, applying one more announcement is a fixed point. -/
theorem update_iterateUpdate_eq_self_of_step (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {n : Nat}
    (hstep : M.iterateUpdate phi (n + 1) = M.iterateUpdate phi n) :
    (M.iterateUpdate phi n).update phi = M.iterateUpdate phi n := by
  simpa only [iterateUpdate_succ] using hstep

/-- Satisfaction of every formula is constant after a stable model step. -/
theorem satisfies_iff_of_ge_of_step (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {n m : Nat}
    (hstep : M.iterateUpdate phi (n + 1) = M.iterateUpdate phi n)
    (hnm : n <= m) (x : World) (psi : Formula Atom Agent) :
    (M.iterateUpdate phi m).Satisfies x psi <->
      (M.iterateUpdate phi n).Satisfies x psi :=
  Model.satisfies_congr (M.iterateUpdate_eq_of_ge_of_step phi hstep hnm) x psi

/-- Truth sets of every formula are constant after a stable model step. -/
theorem truthSet_eq_of_ge_of_step (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {n m : Nat}
    (hstep : M.iterateUpdate phi (n + 1) = M.iterateUpdate phi n)
    (hnm : n <= m) (psi : Formula Atom Agent) :
    (M.iterateUpdate phi m).truthSet psi =
      (M.iterateUpdate phi n).truthSet psi := by
  ext x
  exact M.satisfies_iff_of_ge_of_step phi hstep hnm x psi

/-- In particular, the truth trace of the announced formula is constant after a
stable model step. -/
theorem trace_iff_of_ge_of_step (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {n m : Nat}
    (hstep : M.iterateUpdate phi (n + 1) = M.iterateUpdate phi n)
    (hnm : n <= m) (x : World) :
    M.trace x phi m <-> M.trace x phi n := by
  exact M.satisfies_iff_of_ge_of_step phi hstep hnm x phi

/-- A stable survivor-set step makes all later survivor sets equal as well. -/
theorem survivorSet_eq_of_ge_of_step (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {n m : Nat}
    (hstep : M.survivorSet phi (n + 1) = M.survivorSet phi n)
    (hnm : n <= m) :
    M.survivorSet phi m = M.survivorSet phi n := by
  apply Set.Subset.antisymm
  · exact M.survivorSet_antitone phi hnm
  · intro x hx
    have hxNext : x ∈ M.survivorSet phi (n + 1) := by
      rw [hstep]
      exact hx
    have hxTruth : (M.iterateUpdate phi n).Satisfies x phi :=
      (M.survives_succ_iff phi n x).mp hxNext |>.2
    change M.Survives phi m x
    intro j hjm
    by_cases hjn : j < n
    · exact hx j hjn
    · have hnj : n <= j := Nat.le_of_not_gt hjn
      have hmodelStep := M.iterateUpdate_eq_of_survivorSet_step phi hstep
      exact (M.satisfies_iff_of_ge_of_step phi hmodelStep hnj x phi).mpr hxTruth

/-- A truth-value change across one update forces a strict survivor-set
decrease, irrespective of which formula's truth changed. -/
theorem survivorSet_strict_of_satisfaction_change (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {n : Nat} (x : World)
    (psi : Formula Atom Agent)
    (hchange : ¬((M.iterateUpdate phi n).Satisfies x psi <->
      (M.iterateUpdate phi (n + 1)).Satisfies x psi)) :
    M.survivorSet phi (n + 1) ⊂ M.survivorSet phi n := by
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨M.survivorSet_succ_subset phi n, ?_⟩
  intro heq
  apply hchange
  have hmodel := M.iterateUpdate_eq_of_survivorSet_eq phi heq
  exact (Model.satisfies_congr hmodel x psi).symm

/-- A truth-value change produces a world dropped at that update. -/
theorem dropSet_nonempty_of_satisfaction_change (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {n : Nat} (x : World)
    (psi : Formula Atom Agent)
    (hchange : ¬((M.iterateUpdate phi n).Satisfies x psi <->
      (M.iterateUpdate phi (n + 1)).Satisfies x psi)) :
    (M.dropSet phi n).Nonempty := by
  obtain ⟨y, hyn, hynext⟩ :=
    Set.exists_of_ssubset
      (M.survivorSet_strict_of_satisfaction_change phi x psi hchange)
  exact ⟨y, hyn, hynext⟩

/-- Explicit witness form of the descent caused by a truth-value change. -/
theorem exists_dropped_of_satisfaction_change (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {n : Nat} (x : World)
    (psi : Formula Atom Agent)
    (hchange : ¬((M.iterateUpdate phi n).Satisfies x psi <->
      (M.iterateUpdate phi (n + 1)).Satisfies x psi)) :
    ∃ y, M.Survives phi n y ∧
      ¬(M.iterateUpdate phi n).Satisfies y phi := by
  obtain ⟨y, hy⟩ := M.dropSet_nonempty_of_satisfaction_change phi x psi hchange
  exact ⟨y, (M.mem_dropSet_iff phi n y).mp hy⟩

theorem exists_dropped_of_true_false (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {n : Nat} (x : World)
    (psi : Formula Atom Agent)
    (htrue : (M.iterateUpdate phi n).Satisfies x psi)
    (hfalse : ¬(M.iterateUpdate phi (n + 1)).Satisfies x psi) :
    ∃ y, M.Survives phi n y ∧
      ¬(M.iterateUpdate phi n).Satisfies y phi := by
  apply M.exists_dropped_of_satisfaction_change phi x psi
  intro hiff
  exact hfalse (hiff.mp htrue)

theorem exists_dropped_of_false_true (M : Model World Atom Agent)
    (phi : Formula Atom Agent) {n : Nat} (x : World)
    (psi : Formula Atom Agent)
    (hfalse : ¬(M.iterateUpdate phi n).Satisfies x psi)
    (htrue : (M.iterateUpdate phi (n + 1)).Satisfies x psi) :
    ∃ y, M.Survives phi n y ∧
      ¬(M.iterateUpdate phi n).Satisfies y phi := by
  apply M.exists_dropped_of_satisfaction_change phi x psi
  intro hiff
  exact hfalse (hiff.mpr htrue)

section Finite

variable [Finite World]

/-- Survivor sets eventually stabilize on a finite world type. -/
theorem exists_survivorSet_eventually_constant (M : Model World Atom Agent)
    (phi : Formula Atom Agent) :
    ∃ n, ∀ m, n <= m ->
      M.survivorSet phi m = M.survivorSet phi n :=
  FiniteDynamics.antitoneSet_eventually_constant
    (M.survivorSet phi) (M.survivorSet_antitone phi)

/-- Survivor sets have a stable step on a finite world type. -/
theorem exists_survivorSet_stableStep (M : Model World Atom Agent)
    (phi : Formula Atom Agent) :
    ∃ n, M.survivorSet phi (n + 1) = M.survivorSet phi n :=
  FiniteDynamics.antitoneSet_exists_stableStep
    (M.survivorSet phi) (M.survivorSet_antitone phi)

/-- Iterated models eventually stabilize on a finite world type. -/
theorem exists_iterateUpdate_eventually_constant (M : Model World Atom Agent)
    (phi : Formula Atom Agent) :
    ∃ n, ∀ m, n <= m ->
      M.iterateUpdate phi m = M.iterateUpdate phi n := by
  obtain ⟨n, hn⟩ := M.exists_survivorSet_eventually_constant phi
  exact ⟨n, fun m hnm => M.iterateUpdate_eq_of_survivorSet_eq phi (hn m hnm)⟩

/-- Iterated models have a stable step on a finite world type. -/
theorem exists_iterateUpdate_stableStep (M : Model World Atom Agent)
    (phi : Formula Atom Agent) :
    ∃ n, M.iterateUpdate phi (n + 1) = M.iterateUpdate phi n := by
  obtain ⟨n, hn⟩ := M.exists_survivorSet_stableStep phi
  exact ⟨n, M.iterateUpdate_eq_of_survivorSet_step phi hn⟩

/-- Satisfaction of every formula at every world is eventually constant,
uniformly from one stabilization time. -/
theorem exists_satisfies_eventually_constant (M : Model World Atom Agent)
    (phi : Formula Atom Agent) :
    ∃ n, ∀ m, n <= m -> ∀ (x : World) (psi : Formula Atom Agent),
      (M.iterateUpdate phi m).Satisfies x psi <->
        (M.iterateUpdate phi n).Satisfies x psi := by
  obtain ⟨n, hn⟩ := M.exists_iterateUpdate_eventually_constant phi
  refine ⟨n, fun m hnm x psi => ?_⟩
  exact Model.satisfies_congr (hn m hnm) x psi

/-- Every truth trace generated by a finite model eventually stabilizes. -/
theorem exists_trace_eventually_constant (M : Model World Atom Agent)
    (phi : Formula Atom Agent) :
    ∃ n, ∀ m, n <= m -> ∀ x : World,
      M.trace x phi m <-> M.trace x phi n := by
  obtain ⟨n, hn⟩ := M.exists_satisfies_eventually_constant phi
  exact ⟨n, fun m hnm x => hn m hnm x phi⟩

end Finite

end Model

end ClassificationSigmaValidity
