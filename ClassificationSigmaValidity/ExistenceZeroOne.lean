import ClassificationSigmaValidity.TypeFormulas
import ClassificationSigmaValidity.FrameClass
import ClassificationSigmaValidity.PatternLemmas
import Mathlib.Data.List.FinRange

/-!
# Separating the finite `0 1^k` validity classes

This file formalizes the paper's parametric K45 witness showing that, for every
`k >= 1`, some formula is non-trivially `0 1^k`-valid but not
`0 1^(k+1)`-valid.

The displayed definition of `B_k` in the TeX source contains `chi_(a_0) OR
E_(Y_0)` in its second clause.  The subsequent prose, all three transition
figures, and the claimed theorem require `chi_(a_0) AND E_(Y_0)`.  The former
formula is already false as a witness on a one-world K45 frame.  We therefore
formalize the mathematically intended conjunction below, without modifying the
TeX source.
-/

namespace ClassificationSigmaValidity

universe u v w

namespace ExistenceZeroOne

open Pattern Sigma TypeFormulas

set_option maxHeartbeats 1000000 in
section

/-- Names of the mutually exclusive state types used by the `k`th witness. -/
inductive Tag (k : Nat) where
  | root
  | base
  | step (index : Fin (k + 2))
  deriving DecidableEq, Repr

namespace Tag

variable {k : Nat}

/-- A concrete injection of every finite witness type into the paper's
countable proposition-letter type `Nat`. -/
def toNat : Tag k -> Nat
  | .root => 0
  | .base => 1
  | .step j => j.val + 2

theorem toNat_injective : Function.Injective (toNat : Tag k -> Nat) := by
  intro s t h
  cases s with
  | root => cases t <;> simp_all [toNat]
  | base => cases t <;> simp_all [toNat]
  | step j =>
      cases t with
      | root => simp [toNat] at h
      | base => simp [toNat] at h
      | step l =>
          have hjl : j.val = l.val := by simpa [toNat] using h
          exact congrArg Tag.step (Fin.ext hjl)

/-- The distinguished type `a_0`. -/
def a0 (k : Nat) : Tag k := .step ⟨0, by omega⟩

/-- Every type, in the order `r,b,a_0,...,a_(k+1)`. -/
def all (k : Nat) : List (Tag k) :=
  .root :: .base :: (List.finRange (k + 2)).map .step

@[simp] theorem root_mem_all : Tag.root ∈ all k := by
  simp [all]

@[simp] theorem base_mem_all : Tag.base ∈ all k := by
  simp [all]

@[simp] theorem step_mem_all (j : Fin (k + 2)) : Tag.step j ∈ all k := by
  simp [all, List.mem_finRange]

theorem mem_all (t : Tag k) : t ∈ all k := by
  cases t <;> simp

/-- `X_j = {b,a_j,...,a_(k+1)}`; for `j = k+2` this is `{b}`. -/
def X (k j : Nat) : List (Tag k) :=
  .base :: ((List.finRange (k + 2)).filter fun n => j <= n.val).map .step

/-- `Y_0`, which is the entire type universe. -/
def Y (k : Nat) : List (Tag k) := all k

@[simp] theorem root_not_mem_X (j : Nat) : Tag.root ∉ X k j := by
  simp [X]

@[simp] theorem base_mem_X (j : Nat) : Tag.base ∈ X k j := by
  simp [X]

@[simp] theorem step_mem_X_iff (j : Nat) (n : Fin (k + 2)) :
    Tag.step n ∈ X k j <-> j <= n.val := by
  simp [X, List.mem_finRange]

@[simp] theorem a0_mem_Y : a0 k ∈ Y k := by
  simp [a0, Y]

@[simp] theorem root_mem_Y : Tag.root ∈ Y k := by
  simp [Y]

@[simp] theorem base_mem_Y : Tag.base ∈ Y k := by
  simp [Y]

@[simp] theorem step_mem_Y (j : Fin (k + 2)) : Tag.step j ∈ Y k := by
  simp [Y]

@[simp] theorem step_not_mem_X_succ (j : Nat) (hj : j < k + 2) :
    Tag.step ⟨j, hj⟩ ∉ X k (j + 1) := by
  simp [step_mem_X_iff]

@[simp] theorem step_mem_X_self (j : Nat) (hj : j < k + 2) :
    Tag.step ⟨j, hj⟩ ∈ X k j := by
  simp

theorem mem_X_succ_of_mem_X_of_ne {j : Nat} (hj : j < k + 2) {t : Tag k}
    (ht : t ∈ X k j) (hne : t ≠ Tag.step ⟨j, hj⟩) :
    t ∈ X k (j + 1) := by
  rcases t with _ | _ | n
  · simp at ht
  · simp
  · rw [step_mem_X_iff] at ht ⊢
    have hnj : n.val ≠ j := by
      intro h
      apply hne
      apply congrArg Tag.step
      exact Fin.ext h
    omega

theorem mem_X_succ_iff {j : Nat} (hj : j < k + 2) {t : Tag k} :
    t ∈ X k (j + 1) <-> t ∈ X k j /\ t ≠ Tag.step ⟨j, hj⟩ := by
  constructor
  · intro ht
    have htPrev : t ∈ X k j := by
      rcases t with _ | _ | n
      · simp at ht
      · simp
      · rw [step_mem_X_iff] at ht ⊢
        omega
    refine ⟨htPrev, ?_⟩
    intro hEq
    subst t
    simp at ht
    omega
  · rintro ⟨ht, hne⟩
    exact mem_X_succ_of_mem_X_of_ne hj ht hne

theorem mem_X_one_iff {t : Tag k} :
    t ∈ X k 1 <-> t ∈ Y k /\ t ≠ Tag.root /\ t ≠ a0 k := by
  constructor
  · intro ht
    refine ⟨mem_all t, ?_, ?_⟩
    · intro h
      subst t
      simp at ht
    · intro h
      subst t
      simp [a0] at ht
  · rintro ⟨_, hroot, ha0⟩
    rcases t with _ | _ | n
    · exact (hroot rfl).elim
    · simp
    · rw [step_mem_X_iff]
      have hn0 : n.val ≠ 0 := by
        intro hn
        apply ha0
        apply congrArg Tag.step
        apply Fin.ext
        simpa using hn
      omega

@[simp] theorem mem_X_terminal_iff {t : Tag k} :
    t ∈ X k (k + 2) <-> t = Tag.base := by
  rcases t with _ | _ | n
  · simp
  · simp
  · rw [step_mem_X_iff]
    constructor
    · intro h
      omega
    · intro h
      cases h

end Tag

variable {Atom : Type v} {Agent : Type w} {k : Nat}

section Formula

variable [Inhabited Atom]

/-- `chi_t`, relative to the complete universe of witness types. -/
def chi (atomOf : Tag k -> Atom) (t : Tag k) : Formula Atom Agent :=
  exactType atomOf (Tag.all k) t

/-- `E_X` for the chosen agent. -/
def E (agent : Agent) (atomOf : Tag k -> Atom) (types : List (Tag k)) :
    Formula Atom Agent :=
  successorTypes agent atomOf (Tag.all k) types

def rootClause (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom) :
    Formula Atom Agent :=
  .conj (chi atomOf .root)
    (Formula.or (E agent atomOf (Tag.Y k))
      (E agent atomOf (Tag.X k (k + 1))))

/-- The intended (conjunctive) `a_0` clause. -/
def a0Clause (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom) :
    Formula Atom Agent :=
  .conj (chi atomOf (Tag.a0 k)) (E agent atomOf (Tag.Y k))

def stepClause (agent : Agent) (atomOf : Tag k -> Atom)
    (j : Fin (k + 2)) : Formula Atom Agent :=
  .conj (chi atomOf (.step j)) (E agent atomOf (Tag.X k j.val))

def positiveIndices (k : Nat) : List (Fin (k + 2)) :=
  (List.finRange (k + 2)).filter fun j => j.val != 0

def stepClauses (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom) :
    List (Formula Atom Agent) :=
  (positiveIndices k).map (stepClause agent atomOf)

/-- The corrected `B_k` from the paper. -/
def bad (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom) :
    Formula Atom Agent :=
  Formula.or (rootClause k agent atomOf)
    (Formula.or (a0Clause k agent atomOf)
      (Formula.disjList (stepClauses k agent atomOf)))

/-- The witness `phi_k = not B_k`. -/
def witness (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom) :
    Formula Atom Agent :=
  .neg (bad k agent atomOf)

end Formula

namespace Model

variable {World : Type u} [Inhabited Atom]

@[simp] theorem satisfies_chi (M : Model World Atom Agent) (x : World)
    (atomOf : Tag k -> Atom) (t : Tag k) :
    M.Satisfies x (chi atomOf t) <->
      M.val (atomOf t) x /\
        forall s, s ∈ Tag.all k -> s != t -> Not (M.val (atomOf s) x) := by
  simp [chi]

theorem chi_unique (M : Model World Atom Agent) (x : World)
    (atomOf : Tag k -> Atom) {s t : Tag k} (hst : s ≠ t)
    (hs : M.Satisfies x (chi atomOf s)) :
    Not (M.Satisfies x (chi atomOf t)) := by
  intro ht
  exact TypeFormulas.exactType_mutuallyExclusive M x atomOf (Tag.all k)
    (Tag.mem_all s) (by simpa using hst) ⟨hs, ht⟩

@[simp] theorem satisfies_E (M : Model World Atom Agent) (x : World)
    (agent : Agent) (atomOf : Tag k -> Atom) (types : List (Tag k)) :
    M.Satisfies x (E agent atomOf types) <->
      (forall y, M.rel agent x y ->
        exists t, t ∈ types /\ M.Satisfies y (chi atomOf t)) /\
      (forall t, t ∈ types ->
        exists y, M.rel agent x y /\ M.Satisfies y (chi atomOf t)) := by
  simp [E, chi]

@[simp] theorem satisfies_bad (M : Model World Atom Agent) (x : World)
    (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom) :
    M.Satisfies x (bad k agent atomOf) <->
      (M.Satisfies x (chi atomOf .root) /\
        (M.Satisfies x (E agent atomOf (Tag.Y k)) \/
          M.Satisfies x (E agent atomOf (Tag.X k (k + 1))))) \/
      ((M.Satisfies x (chi atomOf (Tag.a0 k)) /\
          M.Satisfies x (E agent atomOf (Tag.Y k))) \/
        exists j : Fin (k + 2), j.val ≠ 0 /\
          M.Satisfies x (chi atomOf (.step j)) /\
          M.Satisfies x (E agent atomOf (Tag.X k j.val))) := by
  simp only [bad, Model.satisfies_or, rootClause, Model.satisfies_and,
    a0Clause, Model.satisfies_disjList, stepClauses, List.mem_map,
    positiveIndices, List.mem_filter, List.mem_finRange, true_and, stepClause]
  aesop

theorem satisfies_chi_update_iff (M : Model World Atom Agent) (x : World)
    (ann : Formula Atom Agent) (atomOf : Tag k -> Atom) (t : Tag k) :
    (M.update ann).Satisfies x (chi atomOf t) <->
      M.Satisfies x (chi atomOf t) := by
  simp [chi]

theorem satisfies_chi_iterateUpdate_iff (M : Model World Atom Agent) (x : World)
    (ann : Formula Atom Agent) (n : Nat) (atomOf : Tag k -> Atom) (t : Tag k) :
    (M.iterateUpdate ann n).Satisfies x (chi atomOf t) <->
      M.Satisfies x (chi atomOf t) := by
  simp [chi]

/-- Exact types are unique, stated as a positive equality principle. -/
theorem tag_eq_of_chi (M : Model World Atom Agent) (x : World)
    (atomOf : Tag k -> Atom) {s t : Tag k}
    (hs : M.Satisfies x (chi atomOf s))
    (ht : M.Satisfies x (chi atomOf t)) : s = t := by
  by_contra hne
  exact chi_unique M x atomOf hne hs ht

/-- `E_X` has the same truth value at two worlds connected by the relevant
K45 accessibility relation. -/
theorem E_agreement {M : Model World Atom Agent} (hM : IsK45 M)
    {x y : World} {agent : Agent} (hxy : M.rel agent x y)
    (atomOf : Tag k -> Atom) (types : List (Tag k)) :
    M.Satisfies x (E agent atomOf types) <->
      M.Satisfies y (E agent atomOf types) := by
  rw [satisfies_E, satisfies_E]
  have hsucc := Frame.successor_eq_of_transitive_euclidean
    (R := M.rel agent) (x := x) (y := y)
    (hM agent).1 (hM agent).2 hxy
  constructor
  · rintro ⟨hall, hevery⟩
    constructor
    · intro z hyz
      exact hall z ((hsucc z).mpr hyz)
    · intro t ht
      rcases hevery t ht with ⟨z, hxz, hzt⟩
      exact ⟨z, (hsucc z).mp hxz, hzt⟩
  · rintro ⟨hall, hevery⟩
    constructor
    · intro z hxz
      exact hall z ((hsucc z).mp hxz)
    · intro t ht
      rcases hevery t ht with ⟨z, hyz, hzt⟩
      exact ⟨z, (hsucc z).mpr hyz, hzt⟩

/-- A witnessed type in one exact successor-type set separates it from any
set omitting that type. -/
theorem E_not_of_mem_not_mem (M : Model World Atom Agent) (x : World)
    (agent : Agent) (atomOf : Tag k -> Atom) {A B : List (Tag k)}
    {t : Tag k} (htA : t ∈ A) (htB : t ∉ B)
    (hEA : M.Satisfies x (E agent atomOf A)) :
    Not (M.Satisfies x (E agent atomOf B)) := by
  intro hEB
  rcases (satisfies_E M x agent atomOf A).mp hEA |>.2 t htA with
    ⟨y, hxy, hyt⟩
  rcases (satisfies_E M x agent atomOf B).mp hEB |>.1 y hxy with
    ⟨s, hsB, hys⟩
  have hts : t ≠ s := fun h => htB (h ▸ hsB)
  exact chi_unique M y atomOf hts hyt hys

theorem EY_not_EX (M : Model World Atom Agent) (x : World)
    (agent : Agent) (atomOf : Tag k -> Atom) (j : Nat)
    (hEY : M.Satisfies x (E agent atomOf (Tag.Y k))) :
    Not (M.Satisfies x (E agent atomOf (Tag.X k j))) :=
  E_not_of_mem_not_mem M x agent atomOf Tag.root_mem_Y
    (Tag.root_not_mem_X j) hEY

theorem EX_not_EY (M : Model World Atom Agent) (x : World)
    (agent : Agent) (atomOf : Tag k -> Atom) (j : Nat)
    (hEX : M.Satisfies x (E agent atomOf (Tag.X k j))) :
    Not (M.Satisfies x (E agent atomOf (Tag.Y k))) := by
  intro hEY
  exact EY_not_EX M x agent atomOf j hEY hEX

theorem EX_not_EX_of_lt (M : Model World Atom Agent) (x : World)
    (agent : Agent) (atomOf : Tag k -> Atom) {j m : Nat}
    (hj : j < k + 2) (hjm : j < m)
    (hEX : M.Satisfies x (E agent atomOf (Tag.X k j))) :
    Not (M.Satisfies x (E agent atomOf (Tag.X k m))) := by
  apply E_not_of_mem_not_mem M x agent atomOf
    (Tag.step_mem_X_self j hj) _ hEX
  simp
  omega

/-- On a `Y_0` successor cell, exactly the `r` and `a_0` types satisfy `B_k`. -/
theorem bad_under_EY_iff (M : Model World Atom Agent) (x : World)
    (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom) (t : Tag k)
    (hEY : M.Satisfies x (E agent atomOf (Tag.Y k)))
    (ht : M.Satisfies x (chi atomOf t)) :
    M.Satisfies x (bad k agent atomOf) <->
      t = Tag.root \/ t = Tag.a0 k := by
  constructor
  · intro hbad
    rcases (satisfies_bad M x k agent atomOf).mp hbad with
      hroot | ha0 | ⟨j, hj0, hjchi, hjE⟩
    · exact Or.inl (tag_eq_of_chi M x atomOf ht hroot.1)
    · exact Or.inr (tag_eq_of_chi M x atomOf ht ha0.1)
    · exact (EY_not_EX M x agent atomOf j.val hEY hjE).elim
  · rintro (rfl | rfl)
    · apply (satisfies_bad M x k agent atomOf).mpr
      exact Or.inl ⟨ht, Or.inl hEY⟩
    · apply (satisfies_bad M x k agent atomOf).mpr
      exact Or.inr (Or.inl ⟨ht, hEY⟩)

/-- On an `X_j` successor cell (`1 <= j < k+2`), exactly `a_j` satisfies
`B_k`. -/
theorem bad_under_EX_iff (M : Model World Atom Agent) (x : World)
    (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom)
    (j : Nat) (hjPos : 1 <= j) (hj : j < k + 2) (t : Tag k)
    (htMem : t ∈ Tag.X k j)
    (hEX : M.Satisfies x (E agent atomOf (Tag.X k j)))
    (ht : M.Satisfies x (chi atomOf t)) :
    M.Satisfies x (bad k agent atomOf) <->
      t = Tag.step ⟨j, hj⟩ := by
  constructor
  · intro hbad
    rcases (satisfies_bad M x k agent atomOf).mp hbad with
      hroot | ha0 | ⟨n, hn0, hnchi, hnE⟩
    · have htr := tag_eq_of_chi M x atomOf ht hroot.1
      subst t
      simp at htMem
    · have hta := tag_eq_of_chi M x atomOf ht ha0.1
      subst t
      simp [Tag.a0] at htMem
      omega
    · have htn : t = Tag.step n := tag_eq_of_chi M x atomOf ht hnchi
      have hjn : j <= n.val := by
        subst t
        exact (Tag.step_mem_X_iff j n).mp htMem
      have hnj : n.val <= j := by
        by_contra hnot
        have hjlt : j < n.val := by omega
        exact EX_not_EX_of_lt M x agent atomOf hj hjlt hEX hnE
      have hval : n.val = j := by omega
      calc
        t = Tag.step n := htn
        _ = Tag.step ⟨j, hj⟩ := congrArg Tag.step (Fin.ext hval)
  · intro hEq
    subst t
    apply (satisfies_bad M x k agent atomOf).mpr
    apply Or.inr
    apply Or.inr
    exact ⟨⟨j, hj⟩, Nat.ne_of_gt hjPos, ht, hEX⟩

end Model

section Dynamics

variable {World : Type u} [Inhabited Atom]

/-- The first update of a `Y_0` cell removes exactly the `r` and `a_0`
successor types. -/
theorem update_EY {M : Model World Atom Agent} (hM : IsK45 M)
    (x : World) (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom)
    (hEY : M.Satisfies x (E agent atomOf (Tag.Y k))) :
    (M.update (witness k agent atomOf)).Satisfies x
      (E agent atomOf (Tag.X k 1)) := by
  apply (Model.satisfies_E _ _ _ _ _).mpr
  constructor
  · intro y hy
    rcases (Model.satisfies_E M x agent atomOf (Tag.Y k)).mp hEY |>.1 y hy.1 with
      ⟨t, htY, hyt⟩
    have hEYy : M.Satisfies y (E agent atomOf (Tag.Y k)) :=
      (Model.E_agreement hM hy.1 atomOf (Tag.Y k)).mp hEY
    have hnotBad : Not (M.Satisfies y (bad k agent atomOf)) := by
      simpa [witness] using hy.2
    have hnotSpecial : Not (t = Tag.root \/ t = Tag.a0 k) := by
      intro ht
      exact hnotBad ((Model.bad_under_EY_iff M y k agent atomOf t hEYy hyt).mpr ht)
    refine ⟨t, (Tag.mem_X_one_iff).mpr ⟨htY, ?_, ?_⟩, ?_⟩
    · exact fun h => hnotSpecial (Or.inl h)
    · exact fun h => hnotSpecial (Or.inr h)
    · exact (Model.satisfies_chi_update_iff M y _ atomOf t).mpr hyt
  · intro t htX
    have htY : t ∈ Tag.Y k := (Tag.mem_X_one_iff.mp htX).1
    rcases (Model.satisfies_E M x agent atomOf (Tag.Y k)).mp hEY |>.2 t htY with
      ⟨y, hxy, hyt⟩
    have hEYy : M.Satisfies y (E agent atomOf (Tag.Y k)) :=
      (Model.E_agreement hM hxy atomOf (Tag.Y k)).mp hEY
    have hnotSpecial : Not (t = Tag.root \/ t = Tag.a0 k) := by
      rcases Tag.mem_X_one_iff.mp htX with ⟨_, hroot, ha0⟩
      exact fun h => h.elim hroot ha0
    have hphi : M.Satisfies y (witness k agent atomOf) := by
      change Not (M.Satisfies y (bad k agent atomOf))
      intro hbad
      exact hnotSpecial
        ((Model.bad_under_EY_iff M y k agent atomOf t hEYy hyt).mp hbad)
    exact ⟨y, ⟨hxy, hphi⟩,
      (Model.satisfies_chi_update_iff M y _ atomOf t).mpr hyt⟩

/-- An `X_j` update removes exactly `a_j`, producing `X_(j+1)`. -/
theorem update_EX {M : Model World Atom Agent} (hM : IsK45 M)
    (x : World) (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom)
    (j : Nat) (hjPos : 1 <= j) (hj : j < k + 2)
    (hEX : M.Satisfies x (E agent atomOf (Tag.X k j))) :
    (M.update (witness k agent atomOf)).Satisfies x
      (E agent atomOf (Tag.X k (j + 1))) := by
  apply (Model.satisfies_E _ _ _ _ _).mpr
  constructor
  · intro y hy
    rcases (Model.satisfies_E M x agent atomOf (Tag.X k j)).mp hEX |>.1 y hy.1 with
      ⟨t, htX, hyt⟩
    have hEXy : M.Satisfies y (E agent atomOf (Tag.X k j)) :=
      (Model.E_agreement hM hy.1 atomOf (Tag.X k j)).mp hEX
    have hnotBad : Not (M.Satisfies y (bad k agent atomOf)) := by
      simpa [witness] using hy.2
    have hne : t ≠ Tag.step ⟨j, hj⟩ := by
      intro ht
      exact hnotBad ((Model.bad_under_EX_iff M y k agent atomOf j hjPos hj
        t htX hEXy hyt).mpr ht)
    refine ⟨t, (Tag.mem_X_succ_iff hj).mpr ⟨htX, hne⟩, ?_⟩
    exact (Model.satisfies_chi_update_iff M y _ atomOf t).mpr hyt
  · intro t htNext
    rcases Tag.mem_X_succ_iff hj |>.mp htNext with ⟨htX, hne⟩
    rcases (Model.satisfies_E M x agent atomOf (Tag.X k j)).mp hEX |>.2 t htX with
      ⟨y, hxy, hyt⟩
    have hEXy : M.Satisfies y (E agent atomOf (Tag.X k j)) :=
      (Model.E_agreement hM hxy atomOf (Tag.X k j)).mp hEX
    have hphi : M.Satisfies y (witness k agent atomOf) := by
      change Not (M.Satisfies y (bad k agent atomOf))
      intro hbad
      exact hne ((Model.bad_under_EX_iff M y k agent atomOf j hjPos hj
        t htX hEXy hyt).mp hbad)
    exact ⟨y, ⟨hxy, hphi⟩,
      (Model.satisfies_chi_update_iff M y _ atomOf t).mpr hyt⟩

theorem bad_false_under_terminal (M : Model World Atom Agent) (x : World)
    (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom) (t : Tag k)
    (htMem : t ∈ Tag.X k (k + 2))
    (ht : M.Satisfies x (chi atomOf t)) :
    Not (M.Satisfies x (bad k agent atomOf)) := by
  have htBase : t = Tag.base := Tag.mem_X_terminal_iff.mp htMem
  intro hbad
  rcases (Model.satisfies_bad M x k agent atomOf).mp hbad with
    hroot | ha0 | ⟨j, hj0, hjchi, hjE⟩
  · have := Model.tag_eq_of_chi M x atomOf ht hroot.1
    simp [htBase] at this
  · have := Model.tag_eq_of_chi M x atomOf ht ha0.1
    simp [htBase, Tag.a0] at this
  · have := Model.tag_eq_of_chi M x atomOf ht hjchi
    simp [htBase] at this

/-- Once only the base type remains, the relevant successor cell is fixed. -/
theorem update_E_terminal {M : Model World Atom Agent}
    (x : World) (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom)
    (hEX : M.Satisfies x (E agent atomOf (Tag.X k (k + 2)))) :
    (M.update (witness k agent atomOf)).Satisfies x
      (E agent atomOf (Tag.X k (k + 2))) := by
  apply (Model.satisfies_E _ _ _ _ _).mpr
  constructor
  · intro y hy
    rcases (Model.satisfies_E M x agent atomOf (Tag.X k (k + 2))).mp hEX |>.1
      y hy.1 with ⟨t, htX, hyt⟩
    exact ⟨t, htX, (Model.satisfies_chi_update_iff M y _ atomOf t).mpr hyt⟩
  · intro t htX
    rcases (Model.satisfies_E M x agent atomOf (Tag.X k (k + 2))).mp hEX |>.2
      t htX with ⟨y, hxy, hyt⟩
    have hphi : M.Satisfies y (witness k agent atomOf) := by
      change Not (M.Satisfies y (bad k agent atomOf))
      exact bad_false_under_terminal M y k agent atomOf t htX hyt
    exact ⟨y, ⟨hxy, hphi⟩,
      (Model.satisfies_chi_update_iff M y _ atomOf t).mpr hyt⟩

/-- Iterating after a `Y_0` cell produces `X_(n+1)` after `n+1` updates. -/
theorem iterate_E_from_Y {M : Model World Atom Agent} (hM : IsK45 M)
    (x : World) (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom)
    (hEY : M.Satisfies x (E agent atomOf (Tag.Y k)))
    (n : Nat) (hn : n <= k + 1) :
    (M.iterateUpdate (witness k agent atomOf) (n + 1)).Satisfies x
      (E agent atomOf (Tag.X k (n + 1))) := by
  induction n with
  | zero =>
      simpa [Model.iterateUpdate] using update_EY hM x k agent atomOf hEY
  | succ n ih =>
      have hnPrev : n <= k + 1 := by omega
      have hPrev := ih hnPrev
      have hStageK45 : IsK45
          (M.iterateUpdate (witness k agent atomOf) (n + 1)) :=
        M.iterateUpdate_isK45 hM _ _
      have hNext := update_EX hStageK45 x k agent atomOf (n + 1)
        (by omega) (by omega) hPrev
      simpa [Model.iterateUpdate, Nat.add_assoc] using hNext

/-- Starting from `X_j`, the successor type set advances one step per update
until it reaches the terminal `X_(k+2)`, and then remains there. -/
theorem iterate_E_from_X_capped {M : Model World Atom Agent} (hM : IsK45 M)
    (x : World) (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom)
    (j : Nat) (hjPos : 1 <= j) (hj : j < k + 2)
    (hEX : M.Satisfies x (E agent atomOf (Tag.X k j)))
    (n : Nat) :
    (M.iterateUpdate (witness k agent atomOf) n).Satisfies x
      (E agent atomOf (Tag.X k (min (j + n) (k + 2)))) := by
  induction n with
  | zero =>
      rw [Nat.add_zero, Nat.min_eq_left (Nat.le_of_lt hj)]
      exact hEX
  | succ n ih =>
      have hStageK45 : IsK45
          (M.iterateUpdate (witness k agent atomOf) n) :=
        M.iterateUpdate_isK45 hM _ _
      by_cases hBefore : j + n < k + 2
      · have hCap : min (j + n) (k + 2) = j + n := Nat.min_eq_left (by omega)
        rw [hCap] at ih
        have hNext := update_EX hStageK45 x k agent atomOf (j + n)
          (by omega) hBefore ih
        have hCapNext : min (j + Nat.succ n) (k + 2) = j + n + 1 := by
          apply Nat.min_eq_left
          omega
        rw [Model.iterateUpdate_succ, hCapNext]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hNext
      · have hCap : min (j + n) (k + 2) = k + 2 := Nat.min_eq_right (by omega)
        rw [hCap] at ih
        have hNext := update_E_terminal x k agent atomOf ih
        have hCapNext : min (j + Nat.succ n) (k + 2) = k + 2 :=
          Nat.min_eq_right (by omega)
        rw [Model.iterateUpdate_succ, hCapNext]
        exact hNext

theorem root_not_bad_before_last (M : Model World Atom Agent) (x : World)
    (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom)
    (j : Nat) (hjLast : j < k + 1)
    (hroot : M.Satisfies x (chi atomOf Tag.root))
    (hEX : M.Satisfies x (E agent atomOf (Tag.X k j))) :
    Not (M.Satisfies x (bad k agent atomOf)) := by
  intro hbad
  rcases (Model.satisfies_bad M x k agent atomOf).mp hbad with
    hrootClause | ha0 | ⟨n, hn0, hnchi, hnE⟩
  · rcases hrootClause with ⟨_, hEY | hELast⟩
    · exact Model.EX_not_EY M x agent atomOf j hEX hEY
    · exact Model.EX_not_EX_of_lt M x agent atomOf (by omega) hjLast hEX hELast
  · have hEq := Model.tag_eq_of_chi M x atomOf hroot ha0.1
    simp [Tag.a0] at hEq
  · have hEq := Model.tag_eq_of_chi M x atomOf hroot hnchi
    simp at hEq

theorem root_bad_at_last (M : Model World Atom Agent) (x : World)
    (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom)
    (hroot : M.Satisfies x (chi atomOf Tag.root))
    (hEX : M.Satisfies x (E agent atomOf (Tag.X k (k + 1)))) :
    M.Satisfies x (bad k agent atomOf) := by
  apply (Model.satisfies_bad M x k agent atomOf).mpr
  exact Or.inl ⟨hroot, Or.inr hEX⟩

theorem root_not_bad_terminal (M : Model World Atom Agent) (x : World)
    (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom)
    (hroot : M.Satisfies x (chi atomOf Tag.root))
    (hEX : M.Satisfies x (E agent atomOf (Tag.X k (k + 2)))) :
    Not (M.Satisfies x (bad k agent atomOf)) := by
  intro hbad
  rcases (Model.satisfies_bad M x k agent atomOf).mp hbad with
    hrootClause | ha0 | ⟨n, hn0, hnchi, hnE⟩
  · rcases hrootClause with ⟨_, hEY | hELast⟩
    · exact Model.EX_not_EY M x agent atomOf (k + 2) hEX hEY
    · exact Model.EX_not_EX_of_lt M x agent atomOf (by omega) (by omega)
        hELast hEX
  · have hEq := Model.tag_eq_of_chi M x atomOf hroot ha0.1
    simp [Tag.a0] at hEq
  · have hEq := Model.tag_eq_of_chi M x atomOf hroot hnchi
    simp at hEq

theorem a0_not_bad_under_EX (M : Model World Atom Agent) (x : World)
    (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom) (j : Nat)
    (ha0 : M.Satisfies x (chi atomOf (Tag.a0 k)))
    (hEX : M.Satisfies x (E agent atomOf (Tag.X k j))) :
    Not (M.Satisfies x (bad k agent atomOf)) := by
  intro hbad
  rcases (Model.satisfies_bad M x k agent atomOf).mp hbad with
    hroot | ha0Clause | ⟨n, hn0, hnchi, hnE⟩
  · have hEq := Model.tag_eq_of_chi M x atomOf ha0 hroot.1
    simp [Tag.a0] at hEq
  · exact Model.EX_not_EY M x agent atomOf j hEX ha0Clause.2
  · have hEq := Model.tag_eq_of_chi M x atomOf ha0 hnchi
    have hFin : (⟨0, by omega⟩ : Fin (k + 2)) = n :=
      Tag.step.inj (by simpa [Tag.a0] using hEq)
    have hnVal : n.val = 0 := (congrArg Fin.val hFin).symm
    exact hn0 hnVal

theorem step_not_bad_under_later_EX (M : Model World Atom Agent) (x : World)
    (k : Nat) (agent : Agent) (atomOf : Tag k -> Atom)
    (m : Fin (k + 2)) (hmPos : m.val ≠ 0) (j : Nat) (hmj : m.val < j)
    (hm : M.Satisfies x (chi atomOf (.step m)))
    (hEX : M.Satisfies x (E agent atomOf (Tag.X k j))) :
    Not (M.Satisfies x (bad k agent atomOf)) := by
  intro hbad
  rcases (Model.satisfies_bad M x k agent atomOf).mp hbad with
    hroot | ha0 | ⟨n, hn0, hnchi, hnE⟩
  · have hEq := Model.tag_eq_of_chi M x atomOf hm hroot.1
    simp at hEq
  · have hEq := Model.tag_eq_of_chi M x atomOf hm ha0.1
    have hFin : m = (⟨0, by omega⟩ : Fin (k + 2)) :=
      Tag.step.inj (by simpa [Tag.a0] using hEq)
    have hm0 : m.val = 0 := congrArg Fin.val hFin
    exact hmPos hm0
  · have hEq : m = n := by
      have := Model.tag_eq_of_chi M x atomOf hm hnchi
      simpa using this
    subst n
    exact Model.EX_not_EX_of_lt M x agent atomOf m.isLt hmj hnE hEX

end Dynamics

section Validity

variable [Inhabited Atom]

theorem realizes_zeroOnes_of (tr : Nat -> Prop) (k : Nat) (hk : 1 <= k)
    (hzero : Not (tr 0))
    (hones : forall n, 1 <= n -> n <= k -> tr n) :
    (Pattern.zeroOnes k hk).RealizesTrace tr := by
  intro n hn
  cases n with
  | zero => simpa [Pattern.zeroOnes, Pattern.HoldsBit] using hzero
  | succ n =>
      have hnK : n + 1 <= k := by simpa [Pattern.zeroOnes] using hn
      have hh := hones (n + 1) (by omega) hnK
      simpa [Pattern.zeroOnes, Pattern.HoldsBit, List.getElem_cons_succ,
        List.getElem_replicate] using hh

/-- The corrected paper witness is `0 1^k`-valid on every K45 frame. -/
theorem witness_valid_zeroOnes (k : Nat) (hk : 1 <= k)
    (agent : Agent) (atomOf : Tag k -> Atom) :
    Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (witness k agent atomOf) (Pattern.zeroOnes k hk) := by
  intro World M hM x hx
  have hnotPhi : Not (M.Satisfies x (witness k agent atomOf)) := by
    simpa [Pattern.zeroOnes, Pattern.first, Model.trace] using hx
  have hbad : M.Satisfies x (bad k agent atomOf) := by
    apply Classical.not_not.mp
    simpa [witness] using hnotPhi
  apply realizes_zeroOnes_of (M.trace x (witness k agent atomOf)) k hk
  · simpa [Model.trace] using hnotPhi
  · intro n hnPos hnK
    rcases (Model.satisfies_bad M x k agent atomOf).mp hbad with
      hroot | ha0 | ⟨j, hj0, hjchi, hjE⟩
    · rcases hroot with ⟨hroot, hEY | hELast⟩
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnPos
        have hmK : m <= k + 1 := by omega
        have hEX := iterate_E_from_Y hM x k agent atomOf hEY m hmK
        have hrootStage :=
          (Model.satisfies_chi_iterateUpdate_iff M x (witness k agent atomOf)
            (m + 1) atomOf Tag.root).mpr hroot
        have hnot := root_not_bad_before_last
          (M.iterateUpdate (witness k agent atomOf) (m + 1)) x k agent atomOf
          (m + 1) (by omega) hrootStage hEX
        change (M.iterateUpdate (witness k agent atomOf) (1 + m)).Satisfies x
          (witness k agent atomOf)
        rw [Nat.add_comm]
        exact hnot
      · have hEX := iterate_E_from_X_capped hM x k agent atomOf (k + 1)
          (by omega) (by omega) hELast n
        have hCap : min (k + 1 + n) (k + 2) = k + 2 :=
          Nat.min_eq_right (by omega)
        rw [hCap] at hEX
        have hrootStage :=
          (Model.satisfies_chi_iterateUpdate_iff M x (witness k agent atomOf)
            n atomOf Tag.root).mpr hroot
        change Not ((M.iterateUpdate (witness k agent atomOf) n).Satisfies x
          (bad k agent atomOf))
        exact root_not_bad_terminal _ x k agent atomOf hrootStage hEX
    · rcases ha0 with ⟨ha0, hEY⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnPos
      have hmK : m <= k + 1 := by omega
      have hEX := iterate_E_from_Y hM x k agent atomOf hEY m hmK
      have ha0Stage :=
        (Model.satisfies_chi_iterateUpdate_iff M x (witness k agent atomOf)
          (m + 1) atomOf (Tag.a0 k)).mpr ha0
      have hnot := a0_not_bad_under_EX
        (M.iterateUpdate (witness k agent atomOf) (m + 1)) x k agent atomOf
        (m + 1) ha0Stage hEX
      change (M.iterateUpdate (witness k agent atomOf) (1 + m)).Satisfies x
        (witness k agent atomOf)
      rw [Nat.add_comm]
      exact hnot
    · have hjPos : 1 <= j.val := by omega
      have hEX := iterate_E_from_X_capped hM x k agent atomOf j.val
        hjPos j.isLt hjE n
      have hjLater : j.val < min (j.val + n) (k + 2) := by
        rw [lt_min_iff]
        exact ⟨by omega, j.isLt⟩
      have hjStage :=
        (Model.satisfies_chi_iterateUpdate_iff M x (witness k agent atomOf)
          n atomOf (.step j)).mpr hjchi
      change Not ((M.iterateUpdate (witness k agent atomOf) n).Satisfies x
        (bad k agent atomOf))
      exact step_not_bad_under_later_EX _ x k agent atomOf j hj0 _ hjLater
        hjStage hEX

end Validity

section Countermodel

variable [Inhabited Atom]

/-- The finite universal S5 model drawn in the paper.  Each world carries its
own exact type, and every world sees every other world. -/
def canonicalModel (k : Nat) (atomOf : Tag k -> Atom) :
    Model (ULift.{u} (Tag k)) Atom Agent where
  rel _ _ _ := True
  val p x := p = atomOf x.down

omit [Inhabited Atom] in
@[simp] theorem canonical_rel (k : Nat) (atomOf : Tag k -> Atom)
    (i : Agent) (x y : ULift.{u} (Tag k)) :
    (canonicalModel (Agent := Agent) k atomOf).rel i x y := by
  trivial

omit [Inhabited Atom] in
theorem canonical_isS5 (k : Nat) (atomOf : Tag k -> Atom) :
    IsS5 (canonicalModel (Agent := Agent) k atomOf) := by
  intro i
  exact ⟨fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

theorem canonical_satisfies_chi (k : Nat) (atomOf : Tag k -> Atom)
    (hatom : Function.Injective atomOf) (t : Tag k) :
    (canonicalModel (Agent := Agent) k atomOf).Satisfies
      (⟨t⟩ : ULift.{u} (Tag k)) (chi atomOf t) := by
  apply (Model.satisfies_chi _ _ atomOf t).mpr
  constructor
  · simp [canonicalModel]
  · intro s hs hst hsval
    have hEq : atomOf s = atomOf t := by simpa [canonicalModel] using hsval
    have : s ≠ t := by simpa using hst
    exact this (hatom hEq)

theorem canonical_satisfies_E (k : Nat) (agent : Agent)
    (atomOf : Tag k -> Atom) (hatom : Function.Injective atomOf)
    (types : List (Tag k)) (hcover : forall t : Tag k, t ∈ types) :
    (canonicalModel (Agent := Agent) k atomOf).Satisfies
      (⟨Tag.root⟩ : ULift.{u} (Tag k)) (E agent atomOf types) := by
  apply (Model.satisfies_E _ _ _ _ _).mpr
  constructor
  · intro y hy
    exact ⟨y.down, hcover y.down,
      canonical_satisfies_chi k atomOf hatom y.down⟩
  · intro t ht
    exact ⟨⟨t⟩, by trivial,
      canonical_satisfies_chi k atomOf hatom t⟩

theorem canonical_root_bad (k : Nat) (agent : Agent)
    (atomOf : Tag k -> Atom) (hatom : Function.Injective atomOf) :
    (canonicalModel (Agent := Agent) k atomOf).Satisfies
      (⟨Tag.root⟩ : ULift.{u} (Tag k)) (bad k agent atomOf) := by
  apply (Model.satisfies_bad _ _ k agent atomOf).mpr
  apply Or.inl
  exact ⟨canonical_satisfies_chi k atomOf hatom Tag.root,
    Or.inl (canonical_satisfies_E k agent atomOf hatom (Tag.Y k)
      Tag.mem_all)⟩

/-- In the canonical S5 model the root follows `0 1^k 0`, so this is the
explicit counterexample to `0 1^(k+1)`-validity. -/
theorem canonical_root_trace (k : Nat) (agent : Agent)
    (atomOf : Tag k -> Atom) (hatom : Function.Injective atomOf) :
    let M : Model (ULift.{u} (Tag k)) Atom Agent := canonicalModel k atomOf
    Not (M.trace ⟨Tag.root⟩ (witness k agent atomOf) 0) /\
      (forall n, 1 <= n -> n <= k ->
        M.trace ⟨Tag.root⟩ (witness k agent atomOf) n) /\
      Not (M.trace ⟨Tag.root⟩ (witness k agent atomOf) (k + 1)) := by
  dsimp
  let M : Model (ULift.{u} (Tag k)) Atom Agent := canonicalModel k atomOf
  have hM : IsK45 M := (canonical_isS5 (Agent := Agent) k atomOf).isK45
  have hroot : M.Satisfies ⟨Tag.root⟩ (chi atomOf Tag.root) :=
    canonical_satisfies_chi k atomOf hatom Tag.root
  have hEY : M.Satisfies ⟨Tag.root⟩ (E agent atomOf (Tag.Y k)) :=
    canonical_satisfies_E k agent atomOf hatom (Tag.Y k) Tag.mem_all
  refine ⟨?_, ?_, ?_⟩
  · change Not (M.Satisfies ⟨Tag.root⟩ (witness k agent atomOf))
    intro hphi
    exact hphi (canonical_root_bad k agent atomOf hatom)
  · intro n hnPos hnK
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnPos
    have hmK : m <= k + 1 := by omega
    have hEX := iterate_E_from_Y hM ⟨Tag.root⟩ k agent atomOf hEY m hmK
    have hrootStage :=
      (Model.satisfies_chi_iterateUpdate_iff M ⟨Tag.root⟩
        (witness k agent atomOf) (m + 1) atomOf Tag.root).mpr hroot
    have hnot := root_not_bad_before_last
      (M.iterateUpdate (witness k agent atomOf) (m + 1)) ⟨Tag.root⟩
      k agent atomOf (m + 1) (by omega) hrootStage hEX
    change (M.iterateUpdate (witness k agent atomOf) (1 + m)).Satisfies
      ⟨Tag.root⟩ (witness k agent atomOf)
    rw [Nat.add_comm]
    exact hnot
  · have hEX := iterate_E_from_Y hM ⟨Tag.root⟩ k agent atomOf hEY k (by omega)
    have hrootStage :=
      (Model.satisfies_chi_iterateUpdate_iff M ⟨Tag.root⟩
        (witness k agent atomOf) (k + 1) atomOf Tag.root).mpr hroot
    change Not ((M.iterateUpdate (witness k agent atomOf) (k + 1)).Satisfies
      ⟨Tag.root⟩ (witness k agent atomOf))
    change Not (Not ((M.iterateUpdate (witness k agent atomOf) (k + 1)).Satisfies
      ⟨Tag.root⟩ (bad k agent atomOf)))
    exact Classical.not_not.mpr (root_bad_at_last _ _ k agent atomOf hrootStage hEX)

theorem witness_satisfiable_zeroOnes_s5 (k : Nat) (hk : 1 <= k)
    (agent : Agent) (atomOf : Tag k -> Atom) (hatom : Function.Injective atomOf) :
    Sigma.Satisfiable (Classes.S5 : FrameClass.{u} Atom Agent)
      (witness k agent atomOf) (Pattern.zeroOnes k hk) := by
  let M : Model (ULift.{u} (Tag k)) Atom Agent := canonicalModel k atomOf
  refine ⟨ULift.{u} (Tag k), M, canonical_isS5 (Agent := Agent) k atomOf,
    ⟨Tag.root⟩, ?_⟩
  rcases canonical_root_trace k agent atomOf hatom with
    ⟨hzero, hones, hlast⟩
  exact realizes_zeroOnes_of (M.trace ⟨Tag.root⟩ (witness k agent atomOf))
    k hk hzero hones

theorem witness_satisfiable_zeroOnes_k45 (k : Nat) (hk : 1 <= k)
    (agent : Agent) (atomOf : Tag k -> Atom) (hatom : Function.Injective atomOf) :
    Sigma.Satisfiable (Classes.K45 : FrameClass.{u} Atom Agent)
      (witness k agent atomOf) (Pattern.zeroOnes k hk) :=
  Sigma.satisfiable_mono_class
    (fun {World} (M : Model World Atom Agent) (hM : Classes.S5 M) =>
      Classes.s5_subset_k45 hM)
    (witness_satisfiable_zeroOnes_s5 k hk agent atomOf hatom)

theorem witness_nontriviallyValid_zeroOnes_k45 (k : Nat) (hk : 1 <= k)
    (agent : Agent) (atomOf : Tag k -> Atom) (hatom : Function.Injective atomOf) :
    Sigma.NontriviallyValid (Classes.K45 : FrameClass.{u} Atom Agent)
      (witness k agent atomOf) (Pattern.zeroOnes k hk) :=
  ⟨witness_valid_zeroOnes k hk agent atomOf,
    witness_satisfiable_zeroOnes_k45 k hk agent atomOf hatom⟩

theorem witness_not_valid_zeroOnes_succ_k45 (k : Nat) (hk : 1 <= k)
    (agent : Agent) (atomOf : Tag k -> Atom) (hatom : Function.Injective atomOf) :
    Not (Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (witness k agent atomOf) (Pattern.zeroOnes (k + 1) (by omega))) := by
  intro hvalid
  let M : Model (ULift.{u} (Tag k)) Atom Agent := canonicalModel k atomOf
  have hM : IsK45 M := (canonical_isS5 (Agent := Agent) k atomOf).isK45
  rcases canonical_root_trace k agent atomOf hatom with
    ⟨hzero, hones, hlast⟩
  have hreal := hvalid M hM ⟨Tag.root⟩ (by
    simpa [Pattern.zeroOnes, Pattern.first] using hzero)
  have hAt := hreal (k + 1) (by simp)
  have htrue : M.trace ⟨Tag.root⟩ (witness k agent atomOf) (k + 1) := by
    simpa [Pattern.zeroOnes, Pattern.HoldsBit, List.getElem_cons_succ,
      List.getElem_replicate] using hAt
  exact hlast htrue

end Countermodel

end

end ExistenceZeroOne

end ClassificationSigmaValidity
