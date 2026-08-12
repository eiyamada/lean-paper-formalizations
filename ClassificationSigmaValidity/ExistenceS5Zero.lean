import ClassificationSigmaValidity.TypeDynamics

/-!
# The finite all-zero hierarchy over S5

This module formalizes the witness family in
`lem:0k-valid_but_not_0_plus1-validity`.  The formula is presented in a
slightly more uniform way than in the paper: its disjuncts are indexed by the
finite table of pairs `(state type, successor-type stage)` occurring in the
displayed formula.
-/

namespace ClassificationSigmaValidity

universe u w

namespace S5ZeroWitness

open Pattern Sigma TypeFormulas

variable {Agent : Type w}

/-- The type universe `{0, ..., k}`. -/
def tags (k : Nat) : List Nat := List.range (k + 1)

/-- The paper's `X_stage = {stage, ..., k}`; it is empty at `stage = k + 1`. -/
def tailTags (k stage : Nat) : List Nat :=
  (tags k).filter (fun t => stage <= t)

/-- The pairs `(j, stage)` whose conjunct `chi_j /\ E_(X_stage)` occurs in
the paper's formula `B_k`. -/
def Active (k j stage : Nat) : Prop :=
  (j = 0 /\ stage < k) \/
  (j = 1 /\ 1 <= stage /\ stage <= k) \/
  (2 <= j /\ j <= k /\ j <= stage /\ stage <= k + 1)

instance (k j stage : Nat) : Decidable (Active k j stage) := by
  unfold Active
  infer_instance

def configurations (k : Nat) : List (Nat × Nat) :=
  ((tags k).product (List.range (k + 2))).filter
    (fun pair => Active k pair.1 pair.2)

def chi (k j : Nat) : Formula Nat Agent :=
  exactType id (tags k) j

def successorDescription (i : Agent) (k stage : Nat) : Formula Nat Agent :=
  successorTypes i id (tags k) (tailTags k stage)

/-- The paper's `B_k`. -/
def bad (i : Agent) (k : Nat) : Formula Nat Agent :=
  Formula.disjList ((configurations k).map fun pair =>
    .conj (chi (Agent := Agent) k pair.1)
      (successorDescription i k pair.2))

/-- The witness `phi_k = not B_k`. -/
def formula (i : Agent) (k : Nat) : Formula Nat Agent :=
  .neg (bad i k)

@[simp] theorem mem_tags {k t : Nat} : t ∈ tags k <-> t <= k := by
  simp [tags]
  omega

@[simp] theorem mem_tailTags {k stage t : Nat} :
    t ∈ tailTags k stage <-> stage <= t /\ t <= k := by
  simp [tailTags]
  omega

@[simp] theorem mem_configurations {k j stage : Nat} :
    (j, stage) ∈ configurations k <->
      j <= k /\ stage <= k + 1 /\ Active k j stage := by
  simp [configurations, tags, Active]
  omega

theorem satisfies_bad_iff {World : Type u}
    (M : Model World Nat Agent) (x : World) (i : Agent) (k : Nat) :
    M.Satisfies x (bad i k) <->
      exists j stage, j <= k /\ stage <= k + 1 /\ Active k j stage /\
        M.Satisfies x (chi (Agent := Agent) k j) /\
        M.Satisfies x (successorDescription i k stage) := by
  simp only [bad, Model.satisfies_disjList, List.mem_map]
  constructor
  · rintro ⟨conjunct, ⟨pair, hpair, rfl⟩, hsat⟩
    refine ⟨pair.1, pair.2, ?_, ?_, ?_, hsat.1, hsat.2⟩
    · exact (mem_configurations.mp hpair).1
    · exact (mem_configurations.mp hpair).2.1
    · exact (mem_configurations.mp hpair).2.2
  · rintro ⟨j, stage, hj, hstage, hactive, hchi, hsuccessors⟩
    refine ⟨.conj (chi (Agent := Agent) k j)
      (successorDescription i k stage), ?_, hchi, hsuccessors⟩
    exact ⟨(j, stage), mem_configurations.mpr ⟨hj, hstage, hactive⟩, rfl⟩

theorem exact_index_eq {World : Type u}
    (M : Model World Nat Agent) (x : World) (k j t : Nat)
    (hj : j <= k)
    (hjSat : M.Satisfies x (chi (Agent := Agent) k j))
    (htSat : M.Satisfies x (chi (Agent := Agent) k t)) : j = t := by
  by_contra hjt
  exact exactType_mutuallyExclusive M x id (tags k)
    (mem_tags.mpr hj) (by simpa using hjt) ⟨hjSat, htSat⟩

/-- An exact successor-type description has a unique stage index. -/
theorem successorDescription_stage_unique {World : Type u}
    (M : Model World Nat Agent) (x : World) (i : Agent) (k l stage : Nat)
    (hl : l <= k + 1) (hstage : stage <= k + 1)
    (hlSat : M.Satisfies x (successorDescription i k l))
    (hstageSat : M.Satisfies x (successorDescription i k stage)) :
    l = stage := by
  have hmembership : forall t,
      t ∈ tailTags k l <-> t ∈ tailTags k stage := by
    intro t
    constructor
    · intro ht
      rcases (satisfies_successorTypes M x i id (tags k) (tailTags k l)).mp
        hlSat |>.2 t ht with ⟨y, hxy, htSat⟩
      rcases (satisfies_successorTypes M x i id (tags k) (tailTags k stage)).mp
        hstageSat |>.1 y hxy with
        ⟨q, hq, hqSat⟩
      have htLe : t <= k := (mem_tailTags.mp ht).2
      have hqt : q = t := exact_index_eq M y k q t
        ((mem_tailTags.mp hq).2) hqSat htSat
      simpa [hqt] using hq
    · intro ht
      rcases (satisfies_successorTypes M x i id (tags k) (tailTags k stage)).mp
        hstageSat |>.2 t ht with ⟨y, hxy, htSat⟩
      rcases (satisfies_successorTypes M x i id (tags k) (tailTags k l)).mp
        hlSat |>.1 y hxy with ⟨q, hq, hqSat⟩
      have hqt : q = t := exact_index_eq M y k q t
        ((mem_tailTags.mp hq).2) hqSat htSat
      simpa [hqt] using hq
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hlk : l <= k := by omega
    have hlMem : l ∈ tailTags k l := mem_tailTags.mpr ⟨le_rfl, hlk⟩
    have := mem_tailTags.mp ((hmembership l).mp hlMem)
    omega
  · have hstagek : stage <= k := by omega
    have hsMem : stage ∈ tailTags k stage :=
      mem_tailTags.mpr ⟨le_rfl, hstagek⟩
    have := mem_tailTags.mp ((hmembership stage).mpr hsMem)
    omega

/-- Once an exact type and the current successor stage are fixed, `B_k` is
equivalent to the finite arithmetic table `Active`. -/
theorem satisfies_bad_iff_active {World : Type u}
    (M : Model World Nat Agent) (x : World) (i : Agent) (k j stage : Nat)
    (hj : j <= k) (hstage : stage <= k + 1)
    (hjSat : M.Satisfies x (chi (Agent := Agent) k j))
    (hstageSat : M.Satisfies x (successorDescription i k stage)) :
    M.Satisfies x (bad i k) <-> Active k j stage := by
  constructor
  · intro hbad
    rcases (satisfies_bad_iff M x i k).mp hbad with
      ⟨q, l, hq, hl, hactive, hqSat, hlSat⟩
    have hqj : q = j := exact_index_eq M x k q j hq hqSat hjSat
    have hls : l = stage := successorDescription_stage_unique
      M x i k l stage hl hstage hlSat hstageSat
    simpa [hqj, hls] using hactive
  · intro hactive
    exact (satisfies_bad_iff M x i k).mpr
      ⟨j, stage, hj, hstage, hactive, hjSat, hstageSat⟩

theorem active_of_equal_stage (k stage : Nat) (hk : 2 <= k)
    (hstage : stage <= k) : Active k stage stage := by
  rcases Nat.eq_zero_or_pos stage with rfl | hpos
  · exact Or.inl ⟨rfl, by omega⟩
  · by_cases hone : stage = 1
    · subst stage
      exact Or.inr (Or.inl ⟨rfl, by omega, hstage⟩)
    · exact Or.inr (Or.inr ⟨by omega, hstage, le_rfl, by omega⟩)

theorem active_eq_of_member (k j stage : Nat) (hk : 2 <= k)
    (hstage : stage <= k) (hmember : stage <= j /\ j <= k) :
    Active k j stage <-> j = stage := by
  constructor
  · intro hactive
    rcases hactive with hzero | hone | hlarge
    · omega
    · omega
    · omega
  · intro h
    subst j
    exact active_of_equal_stage k stage hk hstage

/-- At a nonempty successor stage, the states rejected by the announcement
are exactly the states of the least remaining exact type. -/
theorem successor_satisfies_formula_iff {World : Type u}
    (M : Model World Nat Agent) (hM : IsK45 M) (x y : World) (i : Agent)
    (k stage : Nat) (hk : 2 <= k) (hstage : stage <= k)
    (hdescription : M.Satisfies x (successorDescription i k stage))
    (hxy : M.rel i x y) :
    M.Satisfies y (formula i k) <->
      exists t, t ∈ tailTags k (stage + 1) /\
        M.Satisfies y (chi (Agent := Agent) k t) := by
  have hdescriptionY : M.Satisfies y (successorDescription i k stage) :=
    (successorTypes_agreement hM hxy id (tags k) (tailTags k stage)).mp
      hdescription
  rcases (satisfies_successorTypes M x i id (tags k) (tailTags k stage)).mp
    hdescription |>.1 y hxy with
    ⟨t, ht, htSat⟩
  have htBounds := mem_tailTags.mp ht
  have hbad : M.Satisfies y (bad i k) <-> Active k t stage :=
    satisfies_bad_iff_active M y i k t stage htBounds.2 (by omega)
      htSat hdescriptionY
  constructor
  · intro hformula
    have htne : Not (t = stage) := by
      intro hts
      apply hformula
      exact hbad.mpr ((active_eq_of_member k t stage hk hstage htBounds).mpr hts)
    have hnext : stage + 1 <= t := by omega
    exact ⟨t, mem_tailTags.mpr ⟨hnext, htBounds.2⟩, htSat⟩
  · rintro ⟨q, hq, hqSat⟩ hbadSat
    have hqt : q = t := exact_index_eq M y k q t
      ((mem_tailTags.mp hq).2) hqSat htSat
    have hteq : t = stage :=
      (active_eq_of_member k t stage hk hstage htBounds).mp (hbad.mp hbadSat)
    have hqLower := (mem_tailTags.mp hq).1
    omega

/-- One announcement advances a nonempty successor stage by one. -/
theorem update_advances_stage {World : Type u}
    (M : Model World Nat Agent) (hM : IsK45 M) (x : World) (i : Agent)
    (k stage : Nat) (hk : 2 <= k) (hstage : stage <= k)
    (hdescription : M.Satisfies x (successorDescription i k stage)) :
    (M.update (formula i k)).Satisfies x
      (successorDescription i k (stage + 1)) := by
  apply update_satisfies_successorTypes_of_filter M x i id (tags k)
    (tailTags k stage) (tailTags k (stage + 1)) (formula i k)
    hdescription
  · intro t ht
    exact mem_tailTags.mpr
      ⟨Nat.le_trans (Nat.le_succ stage) (mem_tailTags.mp ht).1,
        (mem_tailTags.mp ht).2⟩
  · intro y hxy
    exact successor_satisfies_formula_iff M hM x y i k stage hk hstage
      hdescription hxy

/-- The empty successor stage remains empty after any further announcement. -/
theorem update_preserves_empty_stage {World : Type u}
    (M : Model World Nat Agent) (x : World) (i : Agent) (k : Nat)
    (hdescription : M.Satisfies x (successorDescription i k (k + 1))) :
    (M.update (formula i k)).Satisfies x
      (successorDescription i k (k + 1)) := by
  have hempty : tailTags k (k + 1) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro t ht
    have := mem_tailTags.mp ht
    omega
  unfold successorDescription
  rw [hempty]
  apply update_satisfies_successorTypes_empty M x i id (tags k) (formula i k)
  intro y hxy
  rcases (satisfies_successorTypes M x i id (tags k) (tailTags k (k + 1))).mp
    hdescription |>.1 y hxy with ⟨t, ht, _⟩
  have := mem_tailTags.mp ht
  omega

/-- Exact advancement while the indicated stage stays at most `k + 1`. -/
theorem iterate_advances_stage {World : Type u}
    (M : Model World Nat Agent) (hM : IsK45 M) (x : World) (i : Agent)
    (k stage n : Nat) (hk : 2 <= k) (hbound : stage + n <= k + 1)
    (hdescription : M.Satisfies x (successorDescription i k stage)) :
    (M.iterateUpdate (formula i k) n).Satisfies x
      (successorDescription i k (stage + n)) := by
  induction n with
  | zero => simpa using hdescription
  | succ n ih =>
      rw [show stage + (n + 1) = (stage + n) + 1 by omega]
      rw [Model.iterateUpdate_succ]
      apply update_advances_stage (M.iterateUpdate (formula i k) n)
        (M.iterateUpdate_isK45 hM (formula i k) n) x i k (stage + n) hk
      · omega
      · exact ih (by omega)

/-- From a stage at least `lower`, arbitrary iteration stays at a stage at
least `lower` and at most the final empty stage. -/
theorem iterate_reaches_later_stage {World : Type u}
    (M : Model World Nat Agent) (hM : IsK45 M) (x : World) (i : Agent)
    (k lower stage n : Nat) (hk : 2 <= k)
    (hlower : lower <= stage) (hstage : stage <= k + 1)
    (hdescription : M.Satisfies x (successorDescription i k stage)) :
    exists later, lower <= later /\ later <= k + 1 /\
      (M.iterateUpdate (formula i k) n).Satisfies x
        (successorDescription i k later) := by
  induction n with
  | zero => exact ⟨stage, hlower, hstage, hdescription⟩
  | succ n ih =>
      rcases ih with ⟨later, hlater, hlaterFinal, hlaterSat⟩
      rw [Model.iterateUpdate_succ]
      by_cases hnonempty : later <= k
      · exact ⟨later + 1, by omega, by omega,
          update_advances_stage (M.iterateUpdate (formula i k) n)
            (M.iterateUpdate_isK45 hM (formula i k) n) x i k later hk
            hnonempty hlaterSat⟩
      · have hfinal : later = k + 1 := by omega
        subst later
        exact ⟨k + 1, hlater, le_rfl,
          update_preserves_empty_stage
            (M.iterateUpdate (formula i k) n) x i k hlaterSat⟩

/-- Initial falsity in an S5 model fixes a unique exact type and the matching
initial successor stage. -/
theorem initial_false_structure {World : Type u}
    (M : Model World Nat Agent) (hM : IsS5 M) (x : World) (i : Agent)
    (k : Nat) (_hk : 2 <= k) (hfalse : Not (M.Satisfies x (formula i k))) :
    exists j, j <= k /\ Active k j j /\
      M.Satisfies x (chi (Agent := Agent) k j) /\
      M.Satisfies x (successorDescription i k j) := by
  have hbad : M.Satisfies x (bad i k) := by
    exact Classical.not_not.mp hfalse
  rcases (satisfies_bad_iff M x i k).mp hbad with
    ⟨j, stage, hj, hstage, hactive, hjSat, hdescription⟩
  rcases (satisfies_successorTypes M x i id (tags k) (tailTags k stage)).mp
    hdescription |>.1 x ((hM i).1 x) with
    ⟨t, ht, htSat⟩
  have hjt : j = t := exact_index_eq M x k j t hj hjSat htSat
  have hstageLe : stage <= j := by
    rw [hjt]
    exact (mem_tailTags.mp ht).1
  have hsj : stage = j := by
    rcases hactive with hzero | hone | hlarge
    · omega
    · omega
    · omega
  subst stage
  exact ⟨j, hj, hactive, hjSat, hdescription⟩

@[simp] theorem first_zeros (k : Nat) (hk : 2 <= k) :
    (Pattern.zeros k hk).first = false := by
  simp [Pattern.zeros, Pattern.first]

/-- The paper's witness is `0^k`-valid on every S5 model. -/
theorem valid_zeros (i : Agent) (k : Nat) (hk : 2 <= k) :
    Sigma.Valid (Classes.S5 : FrameClass.{u} Nat Agent)
      (formula i k) (Pattern.zeros k hk) := by
  intro World M hM x hx
  have hfalse : Not (M.Satisfies x (formula i k)) := by
    simpa [Pattern.HoldsBit] using hx
  rcases initial_false_structure M hM x i k hk hfalse with
    ⟨j, hj, hactive, hjSat, hdescription⟩
  intro n hn
  have hn' : n < k := by
    simpa [Pattern.zeros] using hn
  have hjSatN : (M.iterateUpdate (formula i k) n).Satisfies x
      (chi (Agent := Agent) k j) :=
    (iterateUpdate_satisfies_exactType_iff M (formula i k) n x id (tags k) j).mpr
      hjSat
  have hfalseN : Not ((M.iterateUpdate (formula i k) n).Satisfies x
      (formula i k)) := by
    rcases hactive with hzero | hone | hlarge
    · have hjzero : j = 0 := hzero.1
      subst j
      have hstageN := iterate_advances_stage M hM.isK45 x i k 0 n hk
        (by omega) hdescription
      intro hformula
      apply hformula
      exact (satisfies_bad_iff_active _ _ i k 0 n (by omega) (by omega)
        hjSatN (by simpa using hstageN)).mpr (Or.inl ⟨rfl, hn'⟩)
    · have hjone : j = 1 := hone.1
      subst j
      have hstageN := iterate_advances_stage M hM.isK45 x i k 1 n hk
        (by omega) hdescription
      intro hformula
      apply hformula
      exact (satisfies_bad_iff_active _ _ i k 1 (1 + n) (by omega) (by omega)
        hjSatN hstageN).mpr (Or.inr (Or.inl ⟨rfl, by omega, by omega⟩))
    · rcases iterate_reaches_later_stage M hM.isK45 x i k j j n hk
        le_rfl (by omega) hdescription with ⟨later, hjlater, hlater, hlaterSat⟩
      intro hformula
      apply hformula
      exact (satisfies_bad_iff_active _ _ i k j later hj hlater
        hjSatN hlaterSat).mpr
          (Or.inr (Or.inr ⟨hlarge.1, hj, hjlater, hlater⟩))
  simpa [Pattern.HoldsBit, Model.trace] using hfalseN

/-! ## The finite universal countermodel -/

def canonicalModel (k : Nat) (Agent : Type w) :
    Model (ULift.{u} (Fin (k + 1))) Nat Agent where
  rel _ _ _ := True
  val p x := p = x.down.val

theorem canonicalModel_isS5 (k : Nat) (Agent : Type w) :
    IsS5 (canonicalModel k Agent) := by
  intro i
  exact ⟨fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

theorem canonical_exact (k j : Nat) (hj : j <= k) :
    (canonicalModel k Agent).Satisfies ⟨⟨j, by omega⟩⟩
      (chi (Agent := Agent) k j) := by
  unfold chi
  rw [satisfies_exactType]
  constructor
  · simp [canonicalModel]
  · intro s hs hsj
    have hne : Not (s = j) := by simpa using hsj
    simpa [canonicalModel] using hne

theorem canonical_initial_description (i : Agent) (k : Nat) :
    (canonicalModel k Agent).Satisfies ⟨⟨0, by omega⟩⟩
      (successorDescription i k 0) := by
  unfold successorDescription
  apply (satisfies_successorTypes (canonicalModel k Agent) ⟨⟨0, by omega⟩⟩
    i id (tags k) (tailTags k 0)).mpr
  constructor
  · intro y hy
    refine ⟨y.down.val, mem_tailTags.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [satisfies_exactType]
    constructor
    · simp [canonicalModel]
    · intro s hs hne
      simpa [canonicalModel] using hne
  · intro t ht
    have htk : t <= k := (mem_tailTags.mp ht).2
    refine ⟨⟨⟨t, by omega⟩⟩, by trivial, ?_⟩
    exact canonical_exact (Agent := Agent) k t htk

theorem canonical_trace_false_before (i : Agent) (k n : Nat)
    (hk : 2 <= k) (hn : n < k) :
    Not ((canonicalModel k Agent).trace ⟨⟨0, by omega⟩⟩
      (formula i k) n) := by
  let M := canonicalModel k Agent
  have hdescription := canonical_initial_description (Agent := Agent) i k
  have hstageN := iterate_advances_stage M
    (canonicalModel_isS5 k Agent).isK45
    ⟨⟨0, by omega⟩⟩ i k 0 n hk (by omega) hdescription
  have hchiN : (M.iterateUpdate (formula i k) n).Satisfies ⟨⟨0, by omega⟩⟩
      (chi (Agent := Agent) k 0) :=
    (iterateUpdate_satisfies_exactType_iff M (formula i k) n
      ⟨⟨0, by omega⟩⟩ id (tags k) 0).mpr
      (canonical_exact (Agent := Agent) k 0 (by omega))
  intro hformula
  apply hformula
  exact (satisfies_bad_iff_active _ _ i k 0 n (by omega) (by omega)
    hchiN (by simpa using hstageN)).mpr (Or.inl ⟨rfl, hn⟩)

theorem canonical_trace_true_at_k (i : Agent) (k : Nat) (hk : 2 <= k) :
    (canonicalModel k Agent).trace ⟨⟨0, by omega⟩⟩
      (formula i k) k := by
  let M := canonicalModel k Agent
  have hdescription := canonical_initial_description (Agent := Agent) i k
  have hstageK := iterate_advances_stage M
    (canonicalModel_isS5 k Agent).isK45
    ⟨⟨0, by omega⟩⟩ i k 0 k hk (by omega) hdescription
  have hchiK : (M.iterateUpdate (formula i k) k).Satisfies ⟨⟨0, by omega⟩⟩
      (chi (Agent := Agent) k 0) :=
    (iterateUpdate_satisfies_exactType_iff M (formula i k) k
      ⟨⟨0, by omega⟩⟩ id (tags k) 0).mpr
      (canonical_exact (Agent := Agent) k 0 (by omega))
  intro hbad
  have hactive := (satisfies_bad_iff_active _ _ i k 0 k (by omega) (by omega)
    hchiK (by simpa using hstageK)).mp hbad
  rcases hactive with hzero | hone | hlarge <;> omega

theorem satisfiable_zeros (i : Agent) (k : Nat) (hk : 2 <= k) :
    Sigma.Satisfiable (Classes.S5 : FrameClass.{u} Nat Agent)
      (formula i k) (Pattern.zeros k hk) := by
  refine ⟨ULift.{u} (Fin (k + 1)), canonicalModel k Agent,
    canonicalModel_isS5 k Agent, ⟨⟨0, by omega⟩⟩, ?_⟩
  · intro n hn
    have hfalse := canonical_trace_false_before (Agent := Agent) i k n hk (by
      simpa [Pattern.zeros] using hn)
    simpa [Pattern.HoldsBit] using hfalse

theorem nontriviallyValid_zeros (i : Agent) (k : Nat) (hk : 2 <= k) :
    Sigma.NontriviallyValid (Classes.S5 : FrameClass.{u} Nat Agent)
      (formula i k) (Pattern.zeros k hk) :=
  ⟨valid_zeros i k hk, satisfiable_zeros i k hk⟩

/-- The same witness is not `0^(k+1)`-valid. -/
theorem not_valid_zeros_succ (i : Agent) (k : Nat) (hk : 2 <= k) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Nat Agent)
      (formula i k) (Pattern.zeros (k + 1) (by omega))) := by
  intro hvalid
  let M : Model (ULift.{u} (Fin (k + 1))) Nat Agent := canonicalModel k Agent
  have hM : IsS5 M := canonicalModel_isS5 k Agent
  have hinitial : Not (M.Satisfies ⟨⟨0, by omega⟩⟩ (formula i k)) := by
    have hfalse := canonical_trace_false_before (Agent := Agent) i k 0 hk
      (by omega)
    simpa [M, Model.trace] using hfalse
  have hreal := hvalid M hM ⟨⟨0, by omega⟩⟩ (by
    simpa [Pattern.zeros, Pattern.HoldsBit] using hinitial)
  have hfalseAtK := hreal k (by simp)
  have htrueAtK := canonical_trace_true_at_k (Agent := Agent) i k hk
  have hfalseAtK' : Not (M.trace ⟨⟨0, by omega⟩⟩ (formula i k) k) := by
    simpa [Pattern.HoldsBit] using hfalseAtK
  exact hfalseAtK' (by simpa [M] using htrueAtK)

end S5ZeroWitness

end ClassificationSigmaValidity
