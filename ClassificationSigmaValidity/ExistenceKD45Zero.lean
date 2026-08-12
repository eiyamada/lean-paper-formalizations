import ClassificationSigmaValidity.TypeFormulas
import ClassificationSigmaValidity.Patterns
import ClassificationSigmaValidity.FrameClass
import ClassificationSigmaValidity.FiniteDynamics
import Mathlib.Data.List.Range

/-!
# The KD45 witness family for finite zero patterns

This module formalizes the parametric formula used in the paper's lemma
`lem:0k_but_not_0kplus1_multi_kd45`.  It explicitly assumes two distinct
agents.  The type tags are naturals `0,...,k-1`; `0` is the root type and
positive tags are the successive `b`-successor types.
-/

namespace ClassificationSigmaValidity

universe u u' v w

namespace KD45Zero

open Pattern Sigma

variable {Atom : Type v} {Agent : Type w}

/-- The list `[0,...,k-1]` of all exact types used by the construction. -/
def typeUniverse (k : Nat) : List Nat := List.range k

/-- The list `[1,...,k-1]` of positive types. -/
def positiveTypes (k : Nat) : List Nat := List.range' 1 (k - 1)

/-- The earlier positive types `[1,...,j-1]`. -/
def earlierTypes (j : Nat) : List Nat := List.range' 1 (j - 1)

/-- `A` from the paper: exactly the atom for type `0` holds. -/
def A [Inhabited Atom] (atomOf : Nat -> Atom) (k : Nat) :
    Formula Atom Agent :=
  TypeFormulas.exactType atomOf (typeUniverse k) 0

/-- `C_j` from the paper: exactly the atom for type `j` holds. -/
def C [Inhabited Atom] (atomOf : Nat -> Atom) (k j : Nat) :
    Formula Atom Agent :=
  TypeFormulas.exactType atomOf (typeUniverse k) j

/-- The conjunction `∧_{j=1}^{k-1} ◇_b C_j`. -/
def everyPositiveType [Inhabited Atom] (b : Agent)
    (atomOf : Nat -> Atom) (k : Nat) : Formula Atom Agent :=
  TypeFormulas.everyTypeOccurs b atomOf (typeUniverse k) (positiveTypes k)

/-- `B_0` from the paper. -/
def B0 [Inhabited Atom] (a b : Agent) (atomOf : Nat -> Atom) (k : Nat) :
    Formula Atom Agent :=
  .conj (A atomOf k)
    (.conj (Formula.dia a Formula.verum)
      (.conj (everyPositiveType b atomOf k)
        (.box a (.conj (A atomOf k) (everyPositiveType b atomOf k)))))

/-- The conjunction `∧_{m=1}^{j-1} □_b ¬C_m`. -/
def noEarlierType [Inhabited Atom] (b : Agent)
    (atomOf : Nat -> Atom) (k j : Nat) : Formula Atom Agent :=
  Formula.conjList ((earlierTypes j).map fun m => .box b (.neg (C atomOf k m)))

/-- `B_j` for a positive index `j`. -/
def Bj [Inhabited Atom] (a b : Agent) (atomOf : Nat -> Atom)
    (k j : Nat) : Formula Atom Agent :=
  .conj (Formula.or (A atomOf k) (C atomOf k j))
    (.conj (.box a Formula.falsum)
      (.conj (noEarlierType b atomOf k j) (Formula.dia b (C atomOf k j))))

/-- The disjunction `B_0 ∨ ... ∨ B_{k-1}`. -/
def bad [Inhabited Atom] (a b : Agent) (atomOf : Nat -> Atom) (k : Nat) :
    Formula Atom Agent :=
  Formula.disjList (B0 a b atomOf k ::
    (positiveTypes k).map (Bj a b atomOf k))

/-- The paper's announcement formula `φ_k = ¬(B_0∨...∨B_{k-1})`. -/
def witness [Inhabited Atom] (a b : Agent) (atomOf : Nat -> Atom) (k : Nat) :
    Formula Atom Agent :=
  .neg (bad a b atomOf k)

section Semantics

variable {World : Type u}

@[simp] theorem mem_typeUniverse {k j : Nat} :
    j ∈ typeUniverse k ↔ j < k := by
  simp [typeUniverse]

@[simp] theorem mem_positiveTypes {k j : Nat} :
    j ∈ positiveTypes k ↔ 1 <= j ∧ j < k := by
  simp [positiveTypes]
  omega

@[simp] theorem mem_earlierTypes {j m : Nat} :
    m ∈ earlierTypes j ↔ 1 <= m ∧ m < j := by
  simp [earlierTypes]
  omega

@[simp] theorem satisfies_A [Inhabited Atom]
    (M : Model World Atom Agent) (x : World) (atomOf : Nat -> Atom) (k : Nat) :
    M.Satisfies x (A atomOf k) ↔
      M.val (atomOf 0) x ∧
        ∀ r, r < k -> r ≠ 0 -> ¬M.val (atomOf r) x := by
  simp [A]

@[simp] theorem satisfies_C [Inhabited Atom]
    (M : Model World Atom Agent) (x : World) (atomOf : Nat -> Atom)
    (k j : Nat) :
    M.Satisfies x (C atomOf k j) ↔
      M.val (atomOf j) x ∧
        ∀ r, r < k -> r ≠ j -> ¬M.val (atomOf r) x := by
  simp [C]

theorem C_mutuallyExclusive [Inhabited Atom]
    (M : Model World Atom Agent) (x : World) (atomOf : Nat -> Atom)
    {k j m : Nat} (hj : j < k) (hjm : j ≠ m) :
    ¬(M.Satisfies x (C atomOf k j) ∧ M.Satisfies x (C atomOf k m)) := by
  intro hboth
  have hjpos := (satisfies_C M x atomOf k j).mp hboth.1 |>.1
  have hjneg := (satisfies_C M x atomOf k m).mp hboth.2 |>.2 j hj hjm
  exact hjneg hjpos

theorem A_not_C [Inhabited Atom]
    (M : Model World Atom Agent) (x : World) (atomOf : Nat -> Atom)
    {k j : Nat} (hk : 0 < k) (hj : j ≠ 0) :
    ¬(M.Satisfies x (A atomOf k) ∧ M.Satisfies x (C atomOf k j)) := by
  intro hboth
  have hzero := (satisfies_A M x atomOf k).mp hboth.1 |>.1
  have hnotZero := (satisfies_C M x atomOf k j).mp hboth.2 |>.2 0 hk (by omega)
  exact hnotZero hzero

@[simp] theorem satisfies_everyPositiveType [Inhabited Atom]
    (M : Model World Atom Agent) (x : World) (b : Agent)
    (atomOf : Nat -> Atom) (k : Nat) :
    M.Satisfies x (everyPositiveType b atomOf k) ↔
      ∀ j, 1 <= j -> j < k ->
        ∃ y, M.rel b x y ∧ M.Satisfies y (C atomOf k j) := by
  simp [everyPositiveType]

@[simp] theorem satisfies_noEarlierType [Inhabited Atom]
    (M : Model World Atom Agent) (x : World) (b : Agent)
    (atomOf : Nat -> Atom) (k j : Nat) :
    M.Satisfies x (noEarlierType b atomOf k j) ↔
      ∀ m, 1 <= m -> m < j ->
        ∀ y, M.rel b x y -> ¬M.Satisfies y (C atomOf k m) := by
  rw [noEarlierType, Model.satisfies_conjList]
  constructor
  · intro h m hm1 hmj y hxy hCm
    have hmem : m ∈ earlierTypes j := by simp [hm1, hmj]
    have hformula : (Formula.box b (Formula.neg (C atomOf k m))) ∈
        (earlierTypes j).map fun r => Formula.box b (Formula.neg (C atomOf k r)) := by
      exact List.mem_map.mpr ⟨m, hmem, rfl⟩
    have hbox := h (.box b (.neg (C atomOf k m))) hformula
    exact hbox y hxy hCm
  · intro h boxFormula hmem
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hmem
    exact fun y hxy => h m (mem_earlierTypes.mp hm).1
      (mem_earlierTypes.mp hm).2 y hxy

@[simp] theorem satisfies_B0 [Inhabited Atom]
    (M : Model World Atom Agent) (x : World) (a b : Agent)
    (atomOf : Nat -> Atom) (k : Nat) :
    M.Satisfies x (B0 a b atomOf k) ↔
      M.Satisfies x (A atomOf k) ∧
      M.Satisfies x (Formula.dia a Formula.verum) ∧
      M.Satisfies x (everyPositiveType b atomOf k) ∧
      M.Satisfies x (.box a (.conj (A atomOf k)
        (everyPositiveType b atomOf k))) := by
  rfl

@[simp] theorem satisfies_Bj [Inhabited Atom]
    (M : Model World Atom Agent) (x : World) (a b : Agent)
    (atomOf : Nat -> Atom) (k j : Nat) :
    M.Satisfies x (Bj a b atomOf k j) ↔
      (M.Satisfies x (A atomOf k) ∨ M.Satisfies x (C atomOf k j)) ∧
      M.Satisfies x (.box a Formula.falsum) ∧
      M.Satisfies x (noEarlierType b atomOf k j) ∧
      M.Satisfies x (Formula.dia b (C atomOf k j)) := by
  simp [Bj]

@[simp] theorem satisfies_bad [Inhabited Atom]
    (M : Model World Atom Agent) (x : World) (a b : Agent)
    (atomOf : Nat -> Atom) (k : Nat) :
    M.Satisfies x (bad a b atomOf k) ↔
      M.Satisfies x (B0 a b atomOf k) ∨
        ∃ j, 1 <= j ∧ j < k ∧ M.Satisfies x (Bj a b atomOf k j) := by
  rw [bad, Model.satisfies_disjList]
  constructor
  · rintro ⟨formula, hmem, hsat⟩
    simp only [List.mem_cons, List.mem_map] at hmem
    rcases hmem with rfl | ⟨j, hj, rfl⟩
    · exact Or.inl hsat
    · exact Or.inr ⟨j, (mem_positiveTypes.mp hj).1,
        (mem_positiveTypes.mp hj).2, hsat⟩
  · rintro (hB0 | ⟨j, hj1, hjk, hBj⟩)
    · exact ⟨B0 a b atomOf k, by simp, hB0⟩
    · exact ⟨Bj a b atomOf k j, by
        simp only [List.mem_cons, List.mem_map]
        exact Or.inr ⟨j, mem_positiveTypes.mpr ⟨hj1, hjk⟩, rfl⟩, hBj⟩

@[simp] theorem satisfies_witness [Inhabited Atom]
    (M : Model World Atom Agent) (x : World) (a b : Agent)
    (atomOf : Nat -> Atom) (k : Nat) :
    M.Satisfies x (witness a b atomOf k) ↔
      ¬M.Satisfies x (bad a b atomOf k) := by
  rfl

end Semantics

section Validity

/-- The `a`-successors of a `B₀` point satisfy `B₀` as well.  This is the
modal-agreement step used to delete every `a`-arrow after the first update. -/
theorem B0_at_successor {World : Type u} [Inhabited Atom]
    (M : Model World Atom Agent) (hM : IsKD45 M)
    (a b : Agent) (atomOf : Nat -> Atom) (k : Nat)
    {x y : World} (hx : M.Satisfies x (B0 a b atomOf k))
    (hxy : M.rel a x y) : M.Satisfies y (B0 a b atomOf k) := by
  rw [satisfies_B0] at hx ⊢
  have hprofile : M.Satisfies y
      (.conj (A atomOf k) (everyPositiveType b atomOf k)) := hx.2.2.2 y hxy
  refine ⟨hprofile.1, ?_, hprofile.2, ?_⟩
  · obtain ⟨z, hyz⟩ := (hM a).1 y
    exact (M.satisfies_dia y a Formula.verum).mpr ⟨z, hyz, by simp⟩
  · intro z hyz
    exact hx.2.2.2 z ((hM a).2.1 hxy hyz)

/-- Every `a`-arrow out of an initially `B₀` point disappears at the first
announcement. -/
theorem no_a_successor_after_one {World : Type u} [Inhabited Atom]
    (M : Model World Atom Agent) (hM : IsKD45 M)
    (a b : Agent) (atomOf : Nat -> Atom) (k : Nat)
    {x : World} (hx : M.Satisfies x (B0 a b atomOf k)) :
    ∀ y, ¬(M.iterateUpdate (witness a b atomOf k) 1).rel a x y := by
  intro y hxy
  have hB0 := B0_at_successor M hM a b atomOf k hx hxy.1
  exact hxy.2 ((satisfies_bad M y a b atomOf k).mpr (Or.inl hB0))

/-- Once gone, those `a`-arrows remain gone at every positive time. -/
theorem no_a_successor_after {World : Type u} [Inhabited Atom]
    (M : Model World Atom Agent) (hM : IsKD45 M)
    (a b : Agent) (atomOf : Nat -> Atom) (k n : Nat)
    {x : World} (hx : M.Satisfies x (B0 a b atomOf k)) (hn : 1 <= n) :
    ∀ y, ¬(M.iterateUpdate (witness a b atomOf k) n).rel a x y := by
  intro y hxy
  have hone : (M.iterateUpdate (witness a b atomOf k) 1).rel a x y :=
    M.iterateUpdate_rel_antitone (witness a b atomOf k) hn hxy
  exact no_a_successor_after_one M hM a b atomOf k hx y hone

/-- Valuations, and hence exact-type formulas, are invariant under updates. -/
theorem iterateUpdate_satisfies_C_iff {World : Type u} [Inhabited Atom]
    (M : Model World Atom Agent) (a b : Agent) (atomOf : Nat -> Atom)
    (k j n : Nat) (x : World) :
    (M.iterateUpdate (witness a b atomOf k) n).Satisfies x (C atomOf k j) ↔
      M.Satisfies x (C atomOf k j) := by
  simp [C]

/-- Exact root type is likewise invariant. -/
theorem iterateUpdate_satisfies_A_iff {World : Type u} [Inhabited Atom]
    (M : Model World Atom Agent) (a b : Agent) (atomOf : Nat -> Atom)
    (k n : Nat) (x : World) :
    (M.iterateUpdate (witness a b atomOf k) n).Satisfies x (A atomOf k) ↔
      M.Satisfies x (A atomOf k) := by
  simp [A]

/-- Initially each positive type has a chosen `b`-successor at a `B₀` point. -/
theorem exists_initial_type_successor {World : Type u} [Inhabited Atom]
    (M : Model World Atom Agent) (a b : Agent) (atomOf : Nat -> Atom)
    (k j : Nat) {x : World} (hx : M.Satisfies x (B0 a b atomOf k))
    (hj1 : 1 <= j) (hjk : j < k) :
    ∃ y, M.rel b x y ∧ M.Satisfies y (C atomOf k j) := by
  exact (satisfies_everyPositiveType M x b atomOf k).mp hx.2.2.1 j hj1 hjk

/-- The key survivor claim from the paper: at time `n`, every initially
chosen type-`m` successor with `n ≤ m` is still accessible. -/
theorem high_type_successor_survives {World : Type u} [Inhabited Atom]
    (M : Model World Atom Agent) (hM : IsKD45 M)
    (a b : Agent) (atomOf : Nat -> Atom) (k : Nat)
    {x : World} (hx : M.Satisfies x (B0 a b atomOf k)) :
    ∀ n m y, 1 <= n -> n <= m -> m < k ->
      M.rel b x y -> M.Satisfies y (C atomOf k m) ->
      (M.iterateUpdate (witness a b atomOf k) n).rel b x y := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
      intro m y hn1 hnm hmk hxy hCy
      rw [Model.iterateUpdate_succ, Model.update_rel]
      constructor
      · cases n with
        | zero => exact hxy
        | succ n =>
            exact ih m y (by omega) (by omega) hmk hxy hCy
      · rw [satisfies_witness]
        intro hbad
        rw [satisfies_bad] at hbad
        rcases hbad with hB0 | ⟨j, hj1, hjk, hBj⟩
        · rw [satisfies_B0] at hB0
          have hAatY :
              ¬(M.iterateUpdate (witness a b atomOf k) n).Satisfies y (A atomOf k) := by
            intro hA
            have hAorig := (iterateUpdate_satisfies_A_iff
              M a b atomOf k n y).mp hA
            exact A_not_C M y atomOf (by omega) (by omega) ⟨hAorig, hCy⟩
          exact hAatY hB0.1
        · rw [satisfies_Bj] at hBj
          have hrootOrC := hBj.1
          rcases hrootOrC with hAy | hCj
          · have hAorig := (iterateUpdate_satisfies_A_iff
                M a b atomOf k n y).mp hAy
            exact A_not_C M y atomOf (by omega) (by omega) ⟨hAorig, hCy⟩
          · have hCjorig := (iterateUpdate_satisfies_C_iff
                M a b atomOf k j n y).mp hCj
            by_cases hjm : j = m
            · subst j
              by_cases hnzero : n = 0
              · subst n
                obtain ⟨z, hyz⟩ := (hM a).1 y
                exact (Model.satisfies_falsum M z) (hBj.2.1 z hyz)
              · have hnpos : 1 <= n := Nat.one_le_iff_ne_zero.mpr hnzero
                have hnltm : n < m := by omega
                have hnk : n < k := Nat.lt_trans hnltm hmk
                obtain ⟨s, hxs, hCs⟩ :=
                  exists_initial_type_successor M a b atomOf k n hx hnpos hnk
                have hxsN :
                    (M.iterateUpdate (witness a b atomOf k) n).rel b x s :=
                  ih n s hnpos (Nat.le_refl n) hnk hxs hCs
                have hxyN :
                    (M.iterateUpdate (witness a b atomOf k) n).rel b x y :=
                  ih m y hnpos (Nat.le_of_lt hnltm) hmk hxy hCy
                have hysN :
                    (M.iterateUpdate (witness a b atomOf k) n).rel b y s :=
                  ((M.iterateUpdate_isK45 hM.isK45
                    (witness a b atomOf k) n) b).2 hxyN hxsN
                have hnoEarlier := (satisfies_noEarlierType
                  (M.iterateUpdate (witness a b atomOf k) n) y b atomOf k m).mp
                  hBj.2.2.1
                exact hnoEarlier n hnpos hnltm s hysN
                  ((iterateUpdate_satisfies_C_iff M a b atomOf k n n s).mpr hCs)
            · exact C_mutuallyExclusive M y atomOf hjk hjm
                ⟨hCjorig, hCy⟩

/-- On a serial frame, an initially false witness must be false because `B₀`
holds: every positive `B_j` contains the impossible condition `□_a ⊥`. -/
theorem B0_of_not_witness {World : Type u} [Inhabited Atom]
    (M : Model World Atom Agent) (hM : IsKD45 M)
    (a b : Agent) (atomOf : Nat -> Atom) (k : Nat) {x : World}
    (hx : ¬M.Satisfies x (witness a b atomOf k)) :
    M.Satisfies x (B0 a b atomOf k) := by
  have hbad : M.Satisfies x (bad a b atomOf k) := by
    by_contra hnBad
    exact hx hnBad
  rw [satisfies_bad] at hbad
  rcases hbad with hB0 | ⟨j, _, _, hBj⟩
  · exact hB0
  · rw [satisfies_Bj] at hBj
    obtain ⟨y, hxy⟩ := (hM a).1 x
    exact ((Model.satisfies_falsum M y) (hBj.2.1 y hxy)).elim

/-- At every time below `k`, an initially false witness still satisfies one
of the `B_j`.  For positive time we choose the least positive exact type
actually realized at an accessible `b`-successor.  This is the corrected
least-index step in the paper's proof. -/
theorem bad_at_time_lt {World : Type u} [Inhabited Atom]
    (M : Model World Atom Agent) (hM : IsKD45 M)
    (a b : Agent) (atomOf : Nat -> Atom) (k n : Nat) {x : World}
    (hn : n < k)
    (hx : ¬M.Satisfies x (witness a b atomOf k)) :
    (M.iterateUpdate (witness a b atomOf k) n).Satisfies x
      (bad a b atomOf k) := by
  classical
  have hB0 := B0_of_not_witness M hM a b atomOf k hx
  cases n with
  | zero =>
      exact (satisfies_bad M x a b atomOf k).mpr (Or.inl hB0)
  | succ n =>
      let N := M.iterateUpdate (witness a b atomOf k) (n + 1)
      let P : Nat -> Prop := fun j =>
        1 <= j ∧ j < k ∧ ∃ y, N.rel b x y ∧ N.Satisfies y (C atomOf k j)
      have hTypeN := exists_initial_type_successor M a b atomOf k (n + 1)
        hB0 (by omega) (by omega)
      obtain ⟨s, hxs, hCs⟩ := hTypeN
      have hxsN : N.rel b x s := by
        exact high_type_successor_survives M hM a b atomOf k hB0
          (n + 1) (n + 1) s (by omega) (Nat.le_refl _) (by omega) hxs hCs
      have hCsN : N.Satisfies s (C atomOf k (n + 1)) := by
        exact (iterateUpdate_satisfies_C_iff
          M a b atomOf k (n + 1) (n + 1) s).mpr hCs
      have hExists : ∃ j, P j :=
        ⟨n + 1, by omega, by omega, s, hxsN, hCsN⟩
      let j := Nat.find hExists
      have hj : P j := Nat.find_spec hExists
      have hA : N.Satisfies x (A atomOf k) :=
        (iterateUpdate_satisfies_A_iff
          M a b atomOf k (n + 1) x).mpr hB0.1
      have hboxA : N.Satisfies x (.box a Formula.falsum) := by
        intro y hxy
        exact (no_a_successor_after M hM a b atomOf k (n + 1)
          hB0 (by omega) y hxy).elim
      have hnoEarlier : N.Satisfies x (noEarlierType b atomOf k j) := by
        apply (satisfies_noEarlierType N x b atomOf k j).mpr
        intro m hm1 hmj y hxy hCm
        have hmP : P m := ⟨hm1, Nat.lt_trans hmj hj.2.1, y, hxy, hCm⟩
        exact (Nat.not_lt_of_ge (Nat.find_min' hExists hmP)) hmj
      have hdia : N.Satisfies x (Formula.dia b (C atomOf k j)) :=
        (N.satisfies_dia x b (C atomOf k j)).mpr hj.2.2
      have hBj : N.Satisfies x (Bj a b atomOf k j) :=
        (satisfies_Bj N x a b atomOf k j).mpr
          ⟨Or.inl hA, hboxA, hnoEarlier, hdia⟩
      exact (satisfies_bad N x a b atomOf k).mpr
        (Or.inr ⟨j, hj.1, hj.2.1, hBj⟩)

/-- The witness formula is `0^k`-valid on every KD45 model. -/
theorem witness_valid_zeros [Inhabited Atom]
    (a b : Agent) (atomOf : Nat -> Atom) (k : Nat) (hk : 2 <= k) :
    Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      (witness a b atomOf k) (Pattern.zeros k hk) := by
  intro World M hM x hx
  have hxFalse : ¬M.Satisfies x (witness a b atomOf k) := by
    simpa [Pattern.zeros, Pattern.first, Pattern.HoldsBit, Model.trace] using hx
  intro n hn
  have hbad := bad_at_time_lt M hM a b atomOf k n (by simpa using hn) hxFalse
  have hfalse :
      ¬(M.iterateUpdate (witness a b atomOf k) n).Satisfies x
        (witness a b atomOf k) := by
    intro hw
    exact ((satisfies_witness
      (M.iterateUpdate (witness a b atomOf k) n) x a b atomOf k).mp hw) hbad
  simpa only [List.getElem_replicate, Pattern.HoldsBit, Model.trace] using hfalse

end Validity

section Countermodel


/-- The finite model from the paper.  World `0` is the root; world `j>0`
realizes exact type `j`.  Agent `a` sees only the root, agent `b` sees all
positive worlds, and every other agent has the universal relation. -/
noncomputable def countermodel {Agent : Type w}
    (a b : Agent) (k : Nat) : Model (Fin k) Nat Agent := by
  classical
  exact {
    rel := fun i _ y => if i = a then y.1 = 0 else if i = b then y.1 ≠ 0 else True
    val := fun p y => p = y.1
  }

/-- Pull a model back along a surjective map of world carriers.  This local
construction is used to place the finite canonical countermodel in an
arbitrary universe without changing any of its modal truth values. -/
private def pullbackModel {Source : Type u} {Target : Type u'}
    (M : Model Target Atom Agent) (f : Source -> Target) :
    Model Source Atom Agent where
  rel i x y := M.rel i (f x) (f y)
  val p x := M.val p (f x)

@[simp] private theorem pullbackModel_rel {Source : Type u} {Target : Type u'}
    (M : Model Target Atom Agent) (f : Source -> Target)
    (i : Agent) (x y : Source) :
    (pullbackModel M f).rel i x y ↔ M.rel i (f x) (f y) := Iff.rfl

@[simp] private theorem pullbackModel_val {Source : Type u} {Target : Type u'}
    (M : Model Target Atom Agent) (f : Source -> Target)
    (p : Atom) (x : Source) :
    (pullbackModel M f).val p x ↔ M.val p (f x) := Iff.rfl

private theorem pullbackModel_satisfies_iff
    {Source : Type u} {Target : Type u'}
    (M : Model Target Atom Agent) (f : Source -> Target)
    (hf : Function.Surjective f) (x : Source) (phi : Formula Atom Agent) :
    (pullbackModel M f).Satisfies x phi ↔ M.Satisfies (f x) phi := by
  induction phi generalizing x with
  | atom p => rfl
  | neg phi ih => simp only [Model.satisfies_neg, ih]
  | conj phi psi ihPhi ihPsi =>
      simp only [Model.satisfies_and, ihPhi, ihPsi]
  | box i phi ih =>
      constructor
      · intro h y hxy
        obtain ⟨y', rfl⟩ := hf y
        exact (ih y').mp (h y' hxy)
      · intro h y hxy
        exact (ih y).mpr (h (f y) hxy)

private theorem pullbackModel_update
    {Source : Type u} {Target : Type u'}
    (M : Model Target Atom Agent) (f : Source -> Target)
    (hf : Function.Surjective f) (phi : Formula Atom Agent) :
    (pullbackModel M f).update phi = pullbackModel (M.update phi) f := by
  apply Model.ext'
  · intro i x y
    exact and_congr Iff.rfl (pullbackModel_satisfies_iff M f hf y phi)
  · intro p x
    rfl

private theorem pullbackModel_iterateUpdate
    {Source : Type u} {Target : Type u'}
    (M : Model Target Atom Agent) (f : Source -> Target)
    (hf : Function.Surjective f) (phi : Formula Atom Agent) (n : Nat) :
    (pullbackModel M f).iterateUpdate phi n =
      pullbackModel (M.iterateUpdate phi n) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Model.iterateUpdate_succ, Model.iterateUpdate_succ, ih,
        pullbackModel_update (M.iterateUpdate phi n) f hf phi]

private theorem pullbackModel_trace_iff
    {Source : Type u} {Target : Type u'}
    (M : Model Target Atom Agent) (f : Source -> Target)
    (hf : Function.Surjective f) (x : Source)
    (phi : Formula Atom Agent) (n : Nat) :
    (pullbackModel M f).trace x phi n ↔ M.trace (f x) phi n := by
  rw [Model.trace, Model.trace, pullbackModel_iterateUpdate M f hf phi n]
  exact pullbackModel_satisfies_iff (M.iterateUpdate phi n) f hf x phi

private theorem pullbackModel_isKD45
    {Source : Type u} {Target : Type u'}
    {M : Model Target Atom Agent} (f : Source -> Target)
    (hf : Function.Surjective f) (hM : IsKD45 M) :
    IsKD45 (pullbackModel M f) := by
  intro i
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, hxy⟩ := (hM i).1 (f x)
    obtain ⟨y', rfl⟩ := hf y
    exact ⟨y', hxy⟩
  · intro x y z hxy hyz
    exact (hM i).2.1 hxy hyz
  · intro x y z hxy hxz
    exact (hM i).2.2 hxy hxz

/-- Universe-polymorphic copy of the finite countermodel. -/
noncomputable def liftedCountermodel {Agent : Type w}
    (a b : Agent) (k : Nat) : Model (ULift.{u} (Fin k)) Nat Agent :=
  pullbackModel (countermodel a b k) ULift.down

private theorem uliftDown_surjective (k : Nat) :
    Function.Surjective (ULift.down : ULift.{u} (Fin k) -> Fin k) := by
  intro x
  exact ⟨ULift.up x, rfl⟩

@[simp] theorem liftedCountermodel_satisfies_iff {Agent : Type w}
    (a b : Agent) (k : Nat) (x : ULift.{u} (Fin k))
    (phi : Formula Nat Agent) :
    (liftedCountermodel a b k).Satisfies x phi ↔
      (countermodel a b k).Satisfies x.down phi := by
  exact pullbackModel_satisfies_iff (countermodel a b k) ULift.down
    (uliftDown_surjective k) x phi

@[simp] theorem liftedCountermodel_trace_iff {Agent : Type w}
    (a b : Agent) (k : Nat) (x : ULift.{u} (Fin k))
    (phi : Formula Nat Agent) (n : Nat) :
    (liftedCountermodel a b k).trace x phi n ↔
      (countermodel a b k).trace x.down phi n := by
  exact pullbackModel_trace_iff (countermodel a b k) ULift.down
    (uliftDown_surjective k) x phi n

@[simp] theorem countermodel_val {Agent : Type w}
    (a b : Agent) (k : Nat) (p : Nat) (x : Fin k) :
    (countermodel a b k).val p x ↔ p = x.1 := by
  simp [countermodel]

@[simp] theorem countermodel_rel_a {Agent : Type w}
    (a b : Agent) (k : Nat) (x y : Fin k) :
    (countermodel a b k).rel a x y ↔ y.1 = 0 := by
  simp [countermodel]

@[simp] theorem countermodel_rel_b {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (x y : Fin k) :
    (countermodel a b k).rel b x y ↔ y.1 ≠ 0 := by
  simp [countermodel, Ne.symm hab]

theorem countermodel_rel_source_independent {Agent : Type w}
    (a b : Agent) (k : Nat) (i : Agent) (x x' y : Fin k) :
    (countermodel a b k).rel i x y ↔ (countermodel a b k).rel i x' y := by
  classical
  simp [countermodel]

/-- The canonical model is KD45 when `a` and `b` are distinct and `k≥2`. -/
theorem countermodel_isKD45 {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    IsKD45 (countermodel a b k) := by
  classical
  intro i
  by_cases hia : i = a
  · subst i
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨⟨0, by omega⟩, by simp⟩
    · intro x y z _ hyz
      simpa using hyz
    · intro x y z _ hxz
      simpa using hxz
  · by_cases hib : i = b
    · subst i
      refine ⟨?_, ?_, ?_⟩
      · intro x
        exact ⟨⟨1, by omega⟩, by simp [countermodel, Ne.symm hab]⟩
      · intro x y z _ hyz
        simpa [countermodel, Ne.symm hab] using hyz
      · intro x y z _ hxz
        simpa [countermodel, Ne.symm hab] using hxz
    · refine ⟨?_, ?_, ?_⟩
      · intro x
        exact ⟨x, by simp [countermodel, hia, hib]⟩
      · intro x y z _ _
        simp [countermodel, hia, hib]
      · intro x y z _ _
        simp [countermodel, hia, hib]

/-- The lifted countermodel is KD45 in every world-carrier universe. -/
theorem liftedCountermodel_isKD45 {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    IsKD45 (liftedCountermodel a b k :
      Model (ULift.{u} (Fin k)) Nat Agent) := by
  exact pullbackModel_isKD45 ULift.down (uliftDown_surjective k)
    (countermodel_isKD45 a b hab k hk)

/-- The root world. -/
def root (k : Nat) (hk : 1 <= k) : Fin k := ⟨0, hk⟩

/-- The world carrying positive type `j`. -/
def typeWorld (k j : Nat) (hj : j < k) : Fin k := ⟨j, hj⟩

@[simp] theorem countermodel_root_A {Agent : Type w}
    (a b : Agent) (k : Nat) (hk : 1 <= k) :
    (countermodel a b k).Satisfies (root k hk) (A id k) := by
  rw [satisfies_A]
  simp [root]

@[simp] theorem countermodel_typeWorld_C {Agent : Type w}
    (a b : Agent) (k j : Nat) (hj : j < k) :
    (countermodel a b k).Satisfies (typeWorld k j hj) (C id k j) := by
  rw [satisfies_C]
  simp [typeWorld]

/-- In the canonical model, satisfying `C_j` determines the world exactly. -/
theorem eq_typeWorld_of_countermodel_satisfies_C {Agent : Type w}
    (a b : Agent) (k j : Nat) (hj : j < k) (x : Fin k)
    (hx : (countermodel a b k).Satisfies x (C id k j)) :
    x = typeWorld k j hj := by
  apply Fin.ext
  exact ((satisfies_C (countermodel a b k) x id k j).mp hx).1.symm

/-- Source-independence is preserved by every target-restricting update. -/
theorem countermodel_iterate_rel_source_independent {Agent : Type w}
    (a b : Agent) (k n : Nat) (i : Agent) (x x' y : Fin k) :
    ((countermodel a b k).iterateUpdate (witness a b id k) n).rel i x y ↔
      ((countermodel a b k).iterateUpdate (witness a b id k) n).rel i x' y := by
  rw [(countermodel a b k).iterateUpdate_rel_iff,
    (countermodel a b k).iterateUpdate_rel_iff]
  exact and_congr (countermodel_rel_source_independent a b k i x x' y) Iff.rfl

/-- Initially the canonical root satisfies `B₀`. -/
theorem countermodel_root_B0 {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    (countermodel a b k).Satisfies (root k (by omega)) (B0 a b id k) := by
  let r := root k (by omega)
  rw [satisfies_B0]
  refine ⟨countermodel_root_A a b k (by omega), ?_, ?_, ?_⟩
  · apply ((countermodel a b k).satisfies_dia r a Formula.verum).mpr
    exact ⟨r, by simp [r, root], by simp⟩
  · apply (satisfies_everyPositiveType (countermodel a b k) r b id k).mpr
    intro j hj1 hjk
    let sj := typeWorld k j hjk
    have hsj : sj.1 ≠ 0 := by simp [sj, typeWorld]; omega
    exact ⟨sj, (countermodel_rel_b a b hab k r sj).mpr hsj,
      countermodel_typeWorld_C a b k j hjk⟩
  · intro y hry
    have hy : y = r := by
      apply Fin.ext
      simpa [r] using hry
    subst y
    exact ⟨countermodel_root_A a b k (by omega), by
      apply (satisfies_everyPositiveType (countermodel a b k) r b id k).mpr
      intro j hj1 hjk
      let sj := typeWorld k j hjk
      have hsj : sj.1 ≠ 0 := by simp [sj, typeWorld]; omega
      exact ⟨sj, (countermodel_rel_b a b hab k r sj).mpr hsj,
        countermodel_typeWorld_C a b k j hjk⟩⟩

/-- Initially the witness is false at the root. -/
theorem countermodel_root_not_witness {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    ¬(countermodel a b k).Satisfies (root k (by omega)) (witness a b id k) := by
  intro hw
  exact ((satisfies_witness (countermodel a b k) (root k (by omega))
    a b id k).mp hw)
    ((satisfies_bad (countermodel a b k) (root k (by omega)) a b id k).mpr
      (Or.inl (countermodel_root_B0 a b hab k hk)))

/-- Modal parts of `B_j` transfer between sources when accessibility is
source-independent; only the local exact-type disjunct must be supplied. -/
theorem Bj_of_source_independent [Inhabited Atom] {World : Type u}
    (N : Model World Atom Agent)
    (hsource : ∀ i x x' y, N.rel i x y ↔ N.rel i x' y)
    (a b : Agent) (atomOf : Nat -> Atom) (k j : Nat) {x y : World}
    (hx : N.Satisfies x (Bj a b atomOf k j))
    (hy : N.Satisfies y (A atomOf k) ∨ N.Satisfies y (C atomOf k j)) :
    N.Satisfies y (Bj a b atomOf k j) := by
  rw [satisfies_Bj] at hx ⊢
  refine ⟨hy, ?_, ?_, ?_⟩
  · intro z hyz
    exact hx.2.1 z ((hsource a x y z).mpr hyz)
  · apply (satisfies_noEarlierType N y b atomOf k j).mpr
    intro m hm1 hmj z hyz hCm
    have hno := (satisfies_noEarlierType N x b atomOf k j).mp hx.2.2.1
    exact hno m hm1 hmj z ((hsource b x y z).mpr hyz) hCm
  · obtain ⟨z, hxz, hCz⟩ := (N.satisfies_dia x b (C atomOf k j)).mp hx.2.2.2
    exact (N.satisfies_dia y b (C atomOf k j)).mpr
      ⟨z, (hsource b x y z).mp hxz, hCz⟩

/-- At time `j`, the root and the unique type-`j` world both satisfy `B_j`.
The strong induction is the exact canonical-model version of the corrected
least-index argument: every lower type was already removed at its own stage. -/
theorem countermodel_Bj_at_index {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    ∀ j, ∀ (hj : 1 <= j ∧ j < k),
      let M := countermodel a b k
      let r := root k (by omega)
      let sj := typeWorld k j hj.2
      (M.iterateUpdate (witness a b id k) j).Satisfies r (Bj a b id k j) ∧
        (M.iterateUpdate (witness a b id k) j).Satisfies sj (Bj a b id k j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj
      have hj1 := hj.1
      have hjk := hj.2
      let M := countermodel a b k
      let r := root k (by omega)
      let sj := typeWorld k j hjk
      let Nj := M.iterateUpdate (witness a b id k) j
      have hB0 : M.Satisfies r (B0 a b id k) :=
        countermodel_root_B0 a b hab k hk
      have hA : Nj.Satisfies r (A id k) :=
        (iterateUpdate_satisfies_A_iff M a b id k j r).mpr hB0.1
      have hboxA : Nj.Satisfies r (.box a Formula.falsum) := by
        intro y hry
        exact (no_a_successor_after M (countermodel_isKD45 a b hab k hk)
          a b id k j hB0 hj1 y hry).elim
      have hnoEarlier : Nj.Satisfies r (noEarlierType b id k j) := by
        apply (satisfies_noEarlierType Nj r b id k j).mpr
        intro m hm1 hmj y hry hCm
        have hCmOriginal : M.Satisfies y (C id k m) :=
          (iterateUpdate_satisfies_C_iff M a b id k m j y).mp hCm
        have hy : y = typeWorld k m (Nat.lt_trans hmj hjk) :=
          eq_typeWorld_of_countermodel_satisfies_C a b k m
            (Nat.lt_trans hmj hjk) y hCmOriginal
        subst y
        have hsurv := (M.iterateUpdate_rel_iff
          (witness a b id k) j b r (typeWorld k m (Nat.lt_trans hmj hjk))).mp hry |>.2
        have htrueM := hsurv m hmj
        have hBm := (ih m hmj ⟨hm1, Nat.lt_trans hmj hjk⟩).2
        have hbadM :
            (M.iterateUpdate (witness a b id k) m).Satisfies
              (typeWorld k m (Nat.lt_trans hmj hjk)) (bad a b id k) :=
          (satisfies_bad _ _ a b id k).mpr
            (Or.inr ⟨m, hm1, Nat.lt_trans hmj hjk, hBm⟩)
        exact ((satisfies_witness _ _ a b id k).mp htrueM) hbadM
      obtain ⟨s, hrs, hCs⟩ := exists_initial_type_successor
        M a b id k j hB0 hj1 hjk
      have hrsJ : Nj.rel b r s := high_type_successor_survives
        M (countermodel_isKD45 a b hab k hk) a b id k hB0
        j j s hj1 (Nat.le_refl j) hjk hrs hCs
      have hdia : Nj.Satisfies r (Formula.dia b (C id k j)) :=
        (Nj.satisfies_dia r b (C id k j)).mpr
          ⟨s, hrsJ, (iterateUpdate_satisfies_C_iff M a b id k j j s).mpr hCs⟩
      have hRootBj : Nj.Satisfies r (Bj a b id k j) :=
        (satisfies_Bj Nj r a b id k j).mpr
          ⟨Or.inl hA, hboxA, hnoEarlier, hdia⟩
      have hSjC : Nj.Satisfies sj (C id k j) :=
        (iterateUpdate_satisfies_C_iff M a b id k j j sj).mpr
          (countermodel_typeWorld_C a b k j hjk)
      have hSource : ∀ i x x' y, Nj.rel i x y ↔ Nj.rel i x' y := by
        intro i x x' y
        exact countermodel_iterate_rel_source_independent a b k j i x x' y
      exact ⟨hRootBj,
        Bj_of_source_independent Nj hSource a b id k j hRootBj (Or.inr hSjC)⟩

/-- After the `k`-th update the canonical root satisfies the witness.  Any
remaining `b`-successor of positive type `j` would have survived through time
`j`, contradicting the fact that its unique type-`j` world satisfies `B_j`
at that time. -/
theorem countermodel_root_witness_at_k {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    ((countermodel a b k).iterateUpdate (witness a b id k) k).Satisfies
      (root k (by omega)) (witness a b id k) := by
  let M := countermodel a b k
  let r := root k (by omega)
  let Nk := M.iterateUpdate (witness a b id k) k
  rw [satisfies_witness]
  intro hbad
  rw [satisfies_bad] at hbad
  have hB0 : M.Satisfies r (B0 a b id k) := countermodel_root_B0 a b hab k hk
  rcases hbad with hB0k | ⟨j, hj1, hjk, hBjk⟩
  · rw [satisfies_B0] at hB0k
    obtain ⟨y, hry, _⟩ := (Nk.satisfies_dia r a Formula.verum).mp hB0k.2.1
    exact no_a_successor_after M (countermodel_isKD45 a b hab k hk)
      a b id k k hB0 (by omega) y hry
  · rw [satisfies_Bj] at hBjk
    obtain ⟨y, hry, hCy⟩ :=
      (Nk.satisfies_dia r b (C id k j)).mp hBjk.2.2.2
    have hCyOriginal : M.Satisfies y (C id k j) :=
      (iterateUpdate_satisfies_C_iff M a b id k j k y).mp hCy
    have hy : y = typeWorld k j hjk :=
      eq_typeWorld_of_countermodel_satisfies_C a b k j hjk y hCyOriginal
    subst y
    have hsurv := (M.iterateUpdate_rel_iff (witness a b id k) k b r
      (typeWorld k j hjk)).mp hry |>.2
    have htrueJ := hsurv j hjk
    have hBjJ := (countermodel_Bj_at_index a b hab k hk j ⟨hj1, hjk⟩).2
    have hbadJ :
        (M.iterateUpdate (witness a b id k) j).Satisfies
          (typeWorld k j hjk) (bad a b id k) :=
      (satisfies_bad _ _ a b id k).mpr (Or.inr ⟨j, hj1, hjk, hBjJ⟩)
    exact ((satisfies_witness _ _ a b id k).mp htrueJ) hbadJ

/-- The canonical root realizes `0^k`. -/
theorem countermodel_root_realizes_zeros {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    Sigma.Realizes (countermodel a b k) (root k (by omega))
      (witness a b id k) (Pattern.zeros k hk) := by
  have hvalid := witness_valid_zeros (World := Fin k) a b id k hk
  apply hvalid (countermodel a b k) (countermodel_isKD45 a b hab k hk)
  simpa [Pattern.zeros, Pattern.first, Pattern.HoldsBit, Model.trace] using
    (countermodel_root_not_witness a b hab k hk)

/-- The witness is satisfiable with the required `0^k` trace. -/
private theorem witness_satisfiable_zeros_small {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    Sigma.Satisfiable
      (Classes.KD45 (Atom := Nat) (Agent := Agent) : FrameClass.{0} Nat Agent)
      (witness a b id k) (Pattern.zeros k hk) := by
  exact ⟨Fin k, countermodel a b k, countermodel_isKD45 a b hab k hk,
    root k (by omega), countermodel_root_realizes_zeros a b hab k hk⟩

/-- The same formula is not `0^(k+1)`-valid, witnessed by the canonical root,
which becomes true exactly at the next coordinate. -/
private theorem witness_not_valid_zeros_succ_small {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    ¬Sigma.Valid
      (Classes.KD45 (Atom := Nat) (Agent := Agent) : FrameClass.{0} Nat Agent)
      (witness a b id k) (Pattern.zeros (k + 1) (by omega)) := by
  intro hvalid
  have hfirst : Pattern.HoldsBit (Pattern.zeros (k + 1) (by omega)).first
      ((countermodel a b k).trace (root k (by omega)) (witness a b id k) 0) := by
    simpa [Pattern.zeros, Pattern.first, Pattern.HoldsBit, Model.trace] using
      (countermodel_root_not_witness a b hab k hk)
  have hreal := hvalid (countermodel a b k)
    (countermodel_isKD45 a b hab k hk) (root k (by omega)) hfirst
  have hkFalse := hreal k (by simp)
  have hkNot :
      ¬(countermodel a b k).trace (root k (by omega)) (witness a b id k) k := by
    simpa [Pattern.zeros, Pattern.HoldsBit] using hkFalse
  exact hkNot (countermodel_root_witness_at_k a b hab k hk)

/-- The paper's complete witness theorem: for every `k≥2` and every pair of
distinct agents, `φ_k` is nontrivially `0^k`-valid but not `0^(k+1)`-valid. -/
private theorem witness_nontriviallyValid_zeros_and_not_succ_small {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    Sigma.NontriviallyValid
      (Classes.KD45 (Atom := Nat) (Agent := Agent) : FrameClass.{0} Nat Agent)
      (witness a b id k) (Pattern.zeros k hk) ∧
    ¬Sigma.Valid
      (Classes.KD45 (Atom := Nat) (Agent := Agent) : FrameClass.{0} Nat Agent)
      (witness a b id k) (Pattern.zeros (k + 1) (by omega)) := by
  refine ⟨⟨?_, witness_satisfiable_zeros_small a b hab k hk⟩,
    witness_not_valid_zeros_succ_small a b hab k hk⟩
  intro World M hM x hx
  exact witness_valid_zeros (World := World) a b id k hk M hM x hx

/-- Existential formulation of the paper lemma. -/
private theorem exists_nontriviallyValid_zeros_not_succ_small {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    ∃ phi : Formula Nat Agent,
      Sigma.NontriviallyValid
        (Classes.KD45 (Atom := Nat) (Agent := Agent) : FrameClass.{0} Nat Agent)
        phi (Pattern.zeros k hk) ∧
      ¬Sigma.Valid
        (Classes.KD45 (Atom := Nat) (Agent := Agent) : FrameClass.{0} Nat Agent)
        phi (Pattern.zeros (k + 1) (by omega)) := by
  exact ⟨witness a b id k,
    witness_nontriviallyValid_zeros_and_not_succ_small a b hab k hk⟩

/-- The lifted canonical root realizes `0^k` in any chosen world-carrier
universe. -/
theorem liftedCountermodel_root_realizes_zeros {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    Sigma.Realizes (liftedCountermodel a b k :
      Model (ULift.{u} (Fin k)) Nat Agent)
      (ULift.up (root k (by omega))) (witness a b id k)
      (Pattern.zeros k hk) := by
  intro n hn
  rw [liftedCountermodel_trace_iff]
  exact countermodel_root_realizes_zeros a b hab k hk n hn

/-- Universe-polymorphic satisfiability half of the finite-zero witness. -/
theorem witness_satisfiable_zeros {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    Sigma.Satisfiable
      (Classes.KD45 (Atom := Nat) (Agent := Agent) : FrameClass.{u} Nat Agent)
      (witness a b id k) (Pattern.zeros k hk) := by
  exact ⟨ULift.{u} (Fin k), liftedCountermodel a b k,
    liftedCountermodel_isKD45 a b hab k hk, ULift.up (root k (by omega)),
    liftedCountermodel_root_realizes_zeros a b hab k hk⟩

/-- Universe-polymorphic counterexample to `0^(k+1)`-validity. -/
theorem witness_not_valid_zeros_succ {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    ¬Sigma.Valid
      (Classes.KD45 (Atom := Nat) (Agent := Agent) : FrameClass.{u} Nat Agent)
      (witness a b id k) (Pattern.zeros (k + 1) (by omega)) := by
  intro hvalid
  have hsmallFalse :
      ¬(countermodel a b k).trace (root k (by omega)) (witness a b id k) 0 := by
    exact countermodel_root_not_witness a b hab k hk
  have hliftFalse :
      ¬(liftedCountermodel a b k : Model (ULift.{u} (Fin k)) Nat Agent).trace
        (ULift.up (root k (by omega))) (witness a b id k) 0 := by
    intro h
    exact hsmallFalse ((liftedCountermodel_trace_iff a b k
      (ULift.up (root k (by omega))) (witness a b id k) 0).mp h)
  have hfirst :
      Pattern.HoldsBit (Pattern.zeros (k + 1) (by omega)).first
        ((liftedCountermodel a b k : Model (ULift.{u} (Fin k)) Nat Agent).trace
          (ULift.up (root k (by omega))) (witness a b id k) 0) := by
    simpa [Pattern.zeros, Pattern.first, Pattern.HoldsBit] using hliftFalse
  have hreal := hvalid
    (liftedCountermodel a b k : Model (ULift.{u} (Fin k)) Nat Agent)
    (liftedCountermodel_isKD45 a b hab k hk)
    (ULift.up (root k (by omega))) hfirst
  have hkFalse := hreal k (by simp)
  have hkNot :
      ¬(liftedCountermodel a b k : Model (ULift.{u} (Fin k)) Nat Agent).trace
        (ULift.up (root k (by omega))) (witness a b id k) k := by
    simpa [Pattern.zeros, Pattern.HoldsBit] using hkFalse
  have hsmallTrue :
      (countermodel a b k).trace (root k (by omega)) (witness a b id k) k := by
    exact countermodel_root_witness_at_k a b hab k hk
  have hliftTrue :
      (liftedCountermodel a b k : Model (ULift.{u} (Fin k)) Nat Agent).trace
        (ULift.up (root k (by omega))) (witness a b id k) k :=
    (liftedCountermodel_trace_iff a b k (ULift.up (root k (by omega)))
      (witness a b id k) k).mpr hsmallTrue
  exact hkNot hliftTrue

/-- The paper's complete finite-zero witness theorem, at an arbitrary model
universe. -/
theorem witness_nontriviallyValid_zeros_and_not_succ {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    Sigma.NontriviallyValid
      (Classes.KD45 (Atom := Nat) (Agent := Agent) : FrameClass.{u} Nat Agent)
      (witness a b id k) (Pattern.zeros k hk) ∧
    ¬Sigma.Valid
      (Classes.KD45 (Atom := Nat) (Agent := Agent) : FrameClass.{u} Nat Agent)
      (witness a b id k) (Pattern.zeros (k + 1) (by omega)) := by
  exact ⟨⟨witness_valid_zeros a b id k hk,
      witness_satisfiable_zeros a b hab k hk⟩,
    witness_not_valid_zeros_succ a b hab k hk⟩

/-- Existential publication-facing form of the finite-zero witness theorem,
with no universe restriction. -/
theorem exists_nontriviallyValid_zeros_not_succ {Agent : Type w}
    (a b : Agent) (hab : a ≠ b) (k : Nat) (hk : 2 <= k) :
    ∃ phi : Formula Nat Agent,
      Sigma.NontriviallyValid
        (Classes.KD45 (Atom := Nat) (Agent := Agent) : FrameClass.{u} Nat Agent)
        phi (Pattern.zeros k hk) ∧
      ¬Sigma.Valid
        (Classes.KD45 (Atom := Nat) (Agent := Agent) : FrameClass.{u} Nat Agent)
        phi (Pattern.zeros (k + 1) (by omega)) := by
  exact ⟨witness a b id k,
    witness_nontriviallyValid_zeros_and_not_succ a b hab k hk⟩

end Countermodel

end KD45Zero

end ClassificationSigmaValidity
