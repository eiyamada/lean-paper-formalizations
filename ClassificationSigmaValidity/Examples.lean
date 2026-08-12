import ClassificationSigmaValidity.Collapse

/-!
# Basic witness formulas

This file formalizes the concrete witnesses used for the well-definedness
parts of the paper's classification theorem: the constant formulas, the Moore
sentence, the fundamental true lie, and the `101` witness caused by loss of
seriality under believed announcement.
-/

namespace ClassificationSigmaValidity

universe u v w

namespace Examples

open Pattern Sigma

variable {Atom : Type v} {Agent : Type w}

/-! ## Shared finite S5 witness models -/

/-- A one-state universal model, used for the constant truth patterns. -/
def unitModel (Atom : Type v) (Agent : Type w) :
    Model (ULift.{u} PUnit) Atom Agent where
  rel _ _ _ := True
  val _ _ := False

@[simp] theorem unitModel_rel (Atom : Type v) (Agent : Type w)
    (i : Agent) (x y : ULift.{u} PUnit) : (unitModel Atom Agent).rel i x y := by
  trivial

theorem unitModel_isS5 (Atom : Type v) (Agent : Type w) :
    IsS5 (unitModel Atom Agent) := by
  intro i
  exact ⟨fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

/-- A two-state universal S5 model in which `p` holds only at `true`. -/
def twoWorldModel (p : Atom) : Model (ULift.{u} Bool) Atom Agent where
  rel _ _ _ := True
  val q x := q = p /\ x.down = true

@[simp] theorem twoWorldModel_rel (p : Atom) (i : Agent)
    (x y : ULift.{u} Bool) :
    (twoWorldModel (Agent := Agent) p).rel i x y := by
  trivial

theorem twoWorldModel_isS5 (p : Atom) :
    IsS5 (twoWorldModel (Agent := Agent) p) := by
  intro i
  exact ⟨fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

/-- The three-state universal S5 model from the paper's `101` example.  The
distinguished atom holds at states `0` and `1`, but not at state `2`. -/
def threeWorldModel (p : Atom) : Model (ULift.{u} (Fin 3)) Atom Agent where
  rel _ _ _ := True
  val q x := q = p /\ x.down != (2 : Fin 3)

@[simp] theorem threeWorldModel_rel (p : Atom) (i : Agent)
    (x y : ULift.{u} (Fin 3)) :
    (threeWorldModel (Agent := Agent) p).rel i x y := by
  trivial

theorem threeWorldModel_isS5 (p : Atom) :
    IsS5 (threeWorldModel (Agent := Agent) p) := by
  intro i
  exact ⟨fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

/-! ## Constant patterns -/

theorem falsum_valid_zerosInf [Inhabited Atom]
    (C : FrameClass.{u} Atom Agent) :
    Sigma.Valid C (Formula.falsum : Formula Atom Agent) Pattern.zerosInf := by
  intro World M hM x hx n
  simp [Pattern.HoldsBit, Model.trace]

theorem verum_valid_onesInf [Inhabited Atom]
    (C : FrameClass.{u} Atom Agent) :
    Sigma.Valid C (Formula.verum : Formula Atom Agent) Pattern.onesInf := by
  intro World M hM x hx n
  simp [Pattern.HoldsBit, Model.trace]

theorem falsum_satisfiable_zerosInf_s5 [Inhabited Atom] :
    Sigma.Satisfiable (Classes.S5 : FrameClass.{u} Atom Agent)
      (Formula.falsum : Formula Atom Agent) Pattern.zerosInf := by
  refine ⟨ULift.{u} PUnit, unitModel Atom Agent, unitModel_isS5 Atom Agent,
    ⟨PUnit.unit⟩, ?_⟩
  intro n
  simp [Pattern.HoldsBit, Model.trace]

theorem verum_satisfiable_onesInf_s5 [Inhabited Atom] :
    Sigma.Satisfiable (Classes.S5 : FrameClass.{u} Atom Agent)
      (Formula.verum : Formula Atom Agent) Pattern.onesInf := by
  refine ⟨ULift.{u} PUnit, unitModel Atom Agent, unitModel_isS5 Atom Agent,
    ⟨PUnit.unit⟩, ?_⟩
  intro n
  simp [Pattern.HoldsBit, Model.trace]

theorem falsum_nontriviallyValid_zerosInf_k45 [Inhabited Atom] :
    Sigma.NontriviallyValid (Classes.K45 : FrameClass.{u} Atom Agent)
      (Formula.falsum : Formula Atom Agent) Pattern.zerosInf :=
  ⟨falsum_valid_zerosInf _,
    Sigma.satisfiable_mono_class
      (fun {World} (M : Model World Atom Agent) (hM : Classes.S5 M) =>
        Classes.s5_subset_k45 hM)
      falsum_satisfiable_zerosInf_s5⟩

theorem falsum_nontriviallyValid_zerosInf_kd45 [Inhabited Atom] :
    Sigma.NontriviallyValid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Formula.falsum : Formula Atom Agent) Pattern.zerosInf :=
  ⟨falsum_valid_zerosInf _,
    Sigma.satisfiable_mono_class
      (fun {World} (M : Model World Atom Agent) (hM : Classes.S5 M) =>
        Classes.s5_subset_kd45 hM)
      falsum_satisfiable_zerosInf_s5⟩

theorem falsum_nontriviallyValid_zerosInf_s5 [Inhabited Atom] :
    Sigma.NontriviallyValid (Classes.S5 : FrameClass.{u} Atom Agent)
      (Formula.falsum : Formula Atom Agent) Pattern.zerosInf :=
  ⟨falsum_valid_zerosInf _, falsum_satisfiable_zerosInf_s5⟩

theorem verum_nontriviallyValid_onesInf_k45 [Inhabited Atom] :
    Sigma.NontriviallyValid (Classes.K45 : FrameClass.{u} Atom Agent)
      (Formula.verum : Formula Atom Agent) Pattern.onesInf :=
  ⟨verum_valid_onesInf _,
    Sigma.satisfiable_mono_class
      (fun {World} (M : Model World Atom Agent) (hM : Classes.S5 M) =>
        Classes.s5_subset_k45 hM)
      verum_satisfiable_onesInf_s5⟩

theorem verum_nontriviallyValid_onesInf_kd45 [Inhabited Atom] :
    Sigma.NontriviallyValid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (Formula.verum : Formula Atom Agent) Pattern.onesInf :=
  ⟨verum_valid_onesInf _,
    Sigma.satisfiable_mono_class
      (fun {World} (M : Model World Atom Agent) (hM : Classes.S5 M) =>
        Classes.s5_subset_kd45 hM)
      verum_satisfiable_onesInf_s5⟩

theorem verum_nontriviallyValid_onesInf_s5 [Inhabited Atom] :
    Sigma.NontriviallyValid (Classes.S5 : FrameClass.{u} Atom Agent)
      (Formula.verum : Formula Atom Agent) Pattern.onesInf :=
  ⟨verum_valid_onesInf _, verum_satisfiable_onesInf_s5⟩

/-! ## The Moore sentence `p /\ not box p` -/

/-- The paper's Moore sentence. -/
def moore (p : Atom) (i : Agent) : Formula Atom Agent :=
  .conj (.atom p) (.neg (.box i (.atom p)))

theorem moore_selfRefuting (p : Atom) (i : Agent) :
    Sigma.SelfRefuting (Classes.K45 : FrameClass.{u} Atom Agent) (moore p i) := by
  intro World M hM x hx hupdated
  have hnotBox := hupdated.2
  apply hnotBox
  intro y hy
  exact hy.2.1

theorem moore_valid_oneZero (p : Atom) (i : Agent) :
    Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (moore p i) Pattern.oneZero :=
  (Sigma.valid_oneZero_iff_selfRefuting _ _).2 (moore_selfRefuting p i)

theorem moore_valid_oneZerosInf (p : Atom) (i : Agent) :
    Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (moore p i) Pattern.oneZerosInf :=
  Collapse.k45_valid_oneZero_implies_oneZerosInf (moore p i) (moore_valid_oneZero p i)

theorem twoWorldModel_moore_initial (p : Atom) (i : Agent) :
    (twoWorldModel (Agent := Agent) p).Satisfies
      (⟨true⟩ : ULift.{u} Bool) (moore p i) := by
  constructor
  · simp [twoWorldModel]
  · intro hbox
    have hpFalse := hbox (⟨false⟩ : ULift.{u} Bool) (by trivial)
    simp [twoWorldModel] at hpFalse

theorem moore_satisfiable_oneZerosInf (p : Atom) (i : Agent) :
    Sigma.Satisfiable (Classes.K45 : FrameClass.{u} Atom Agent)
      (moore p i) Pattern.oneZerosInf := by
  let M : Model (ULift.{u} Bool) Atom Agent := twoWorldModel p
  have hM : IsK45 M := (twoWorldModel_isS5 (Agent := Agent) p).isK45
  have hinitial : M.Satisfies (⟨true⟩ : ULift.{u} Bool) (moore p i) :=
    twoWorldModel_moore_initial p i
  refine ⟨ULift.{u} Bool, M, hM, ⟨true⟩, ?_⟩
  exact moore_valid_oneZerosInf p i M hM ⟨true⟩ (by simpa using hinitial)

theorem moore_nontriviallyValid_oneZerosInf (p : Atom) (i : Agent) :
    Sigma.NontriviallyValid (Classes.K45 : FrameClass.{u} Atom Agent)
      (moore p i) Pattern.oneZerosInf :=
  ⟨moore_valid_oneZerosInf p i, moore_satisfiable_oneZerosInf p i⟩

/-! ## The true lie `p \/ box p` -/

/-- The fundamental true lie from the paper. -/
def pOrBox (p : Atom) (i : Agent) : Formula Atom Agent :=
  Formula.or (.atom p) (.box i (.atom p))

theorem pOrBox_update_persistent {World : Type u}
    (M : Model World Atom Agent) (x : World) (p : Atom) (i : Agent)
    (h : M.Satisfies x (pOrBox p i)) :
    (M.update (pOrBox p i)).Satisfies x (pOrBox p i) := by
  rcases (Model.satisfies_or M x _ _).mp h with hp | hbox
  · exact (Model.satisfies_or _ _ _ _).mpr (Or.inl hp)
  · apply (Model.satisfies_or _ _ _ _).mpr
    apply Or.inr
    intro y hy
    exact hbox y hy.1

theorem pOrBox_trueLie (p : Atom) (i : Agent) :
    Sigma.TrueLie (Classes.K45 : FrameClass.{u} Atom Agent) (pOrBox p i) := by
  intro World M hM x hx
  apply (Model.satisfies_or _ _ _ _).mpr
  apply Or.inr
  intro y hy
  rcases (Model.satisfies_or M y _ _).mp hy.2 with hyp | hybox
  · exact hyp
  · have hxbox : Not (M.Satisfies x (.box i (.atom p))) := by
      intro hxbox
      exact hx ((Model.satisfies_or M x _ _).mpr (Or.inr hxbox))
    exact (hxbox ((M.modalAgreement_box hM hy.1 (.atom p)).mpr hybox)).elim

theorem pOrBox_valid_zeroOne (p : Atom) (i : Agent) :
    Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (pOrBox p i) Pattern.zeroOne :=
  (Sigma.valid_zeroOne_iff_trueLie _ _).2 (pOrBox_trueLie p i)

theorem pOrBox_valid_zeroOnesInf (p : Atom) (i : Agent) :
    Sigma.Valid (Classes.K45 : FrameClass.{u} Atom Agent)
      (pOrBox p i) Pattern.zeroOnesInf := by
  intro World M hM x hx
  have hxFalse : Not (M.Satisfies x (pOrBox p i)) := by simpa using hx
  have hfirst : (M.update (pOrBox p i)).Satisfies x (pOrBox p i) :=
    pOrBox_trueLie p i M hM x hxFalse
  have htail : forall n,
      (M.iterateUpdate (pOrBox p i) (n + 1)).Satisfies x (pOrBox p i) := by
    intro n
    induction n with
    | zero => simpa [Model.iterateUpdate] using hfirst
    | succ n ih =>
        rw [show Nat.succ n + 1 = (n + 1) + 1 by omega,
          Model.iterateUpdate_succ]
        exact pOrBox_update_persistent _ _ p i ih
  intro n
  cases n with
  | zero => simpa [Pattern.zeroOnesInf, Pattern.HoldsBit, Model.trace] using hxFalse
  | succ n =>
      simpa [Pattern.zeroOnesInf, Pattern.HoldsBit, Model.trace,
        Nat.succ_eq_add_one] using htail n

theorem twoWorldModel_pOrBox_initial_false (p : Atom) (i : Agent) :
    Not ((twoWorldModel (Agent := Agent) p).Satisfies
      (⟨false⟩ : ULift.{u} Bool) (pOrBox p i)) := by
  intro h
  rcases (Model.satisfies_or _ _ _ _).mp h with hp | hbox
  · simp [twoWorldModel] at hp
  · have hpFalse := hbox (⟨false⟩ : ULift.{u} Bool) (by trivial)
    simp [twoWorldModel] at hpFalse

theorem pOrBox_satisfiable_zeroOnesInf (p : Atom) (i : Agent) :
    Sigma.Satisfiable (Classes.K45 : FrameClass.{u} Atom Agent)
      (pOrBox p i) Pattern.zeroOnesInf := by
  let M : Model (ULift.{u} Bool) Atom Agent := twoWorldModel p
  have hM : IsK45 M := (twoWorldModel_isS5 (Agent := Agent) p).isK45
  have hinitial : Not (M.Satisfies (⟨false⟩ : ULift.{u} Bool) (pOrBox p i)) :=
    twoWorldModel_pOrBox_initial_false p i
  refine ⟨ULift.{u} Bool, M, hM, ⟨false⟩, ?_⟩
  exact pOrBox_valid_zeroOnesInf p i M hM ⟨false⟩ (by simpa using hinitial)

theorem pOrBox_nontriviallyValid_zeroOnesInf (p : Atom) (i : Agent) :
    Sigma.NontriviallyValid (Classes.K45 : FrameClass.{u} Atom Agent)
      (pOrBox p i) Pattern.zeroOnesInf :=
  ⟨pOrBox_valid_zeroOnesInf p i, pOrBox_satisfiable_zeroOnesInf p i⟩

/-! ## The `101` witness -/

/-- `(p /\ dia p /\ dia (not p)) \/ box false`, the paper's `101` witness. -/
def oneZeroOneFormula [Inhabited Atom] (p : Atom) (i : Agent) :
    Formula Atom Agent :=
  Formula.or
    (.conj (.atom p)
      (.conj (Formula.dia i (.atom p)) (Formula.dia i (.neg (.atom p)))))
    (.box i Formula.falsum)

theorem oneZeroOne_selfRefuting [Inhabited Atom] (p : Atom) (i : Agent) :
    Sigma.SelfRefuting (Classes.KD45 : FrameClass.{u} Atom Agent)
      (oneZeroOneFormula p i) := by
  intro World M hM x hx
  have hboxBottomFalse : forall z,
      Not (M.Satisfies z (.box i (Formula.falsum : Formula Atom Agent))) := by
    intro z hbox
    rcases (hM i).1 z with ⟨y, hzy⟩
    exact Model.satisfies_falsum M y (hbox y hzy)
  have hleft : M.Satisfies x
      (.conj (.atom p)
        (.conj (Formula.dia i (.atom p)) (Formula.dia i (.neg (.atom p))))) := by
    rcases (Model.satisfies_or M x _ _).mp hx with hleft | hbox
    · exact hleft
    · exact (hboxBottomFalse x hbox).elim
  have hdiaP : M.Satisfies x (Formula.dia i (.atom p)) := hleft.2.1
  have hdiaNotP : M.Satisfies x (Formula.dia i (.neg (.atom p))) := hleft.2.2
  intro hupdated
  rcases (Model.satisfies_or _ _ _ _).mp hupdated with hleftUpdated | hboxUpdated
  · rcases (Model.satisfies_dia _ _ _ _).mp hleftUpdated.2.2 with
      ⟨y, hy, hynotP⟩
    have hyp : M.Satisfies y (.atom p) := by
      rcases (Model.satisfies_or M y _ _).mp hy.2 with hleftY | hboxY
      · exact hleftY.1
      · exact (hboxBottomFalse y hboxY).elim
    exact hynotP hyp
  · rcases (Model.satisfies_dia M x i (.atom p)).mp hdiaP with ⟨y, hxy, hyp⟩
    have hydiaP : M.Satisfies y (Formula.dia i (.atom p)) :=
      (M.modalAgreement_dia hM.isK45 hxy (.atom p)).mp hdiaP
    have hydiaNotP : M.Satisfies y (Formula.dia i (.neg (.atom p))) :=
      (M.modalAgreement_dia hM.isK45 hxy (.neg (.atom p))).mp hdiaNotP
    have hyFormula : M.Satisfies y (oneZeroOneFormula p i) :=
      (Model.satisfies_or M y _ _).mpr (Or.inl ⟨hyp, hydiaP, hydiaNotP⟩)
    exact Model.satisfies_falsum (M.update (oneZeroOneFormula p i)) y
      (hboxUpdated y ⟨hxy, hyFormula⟩)

theorem oneZeroOne_valid_101 [Inhabited Atom] (p : Atom) (i : Agent) :
    Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (oneZeroOneFormula p i) (Pattern.bits3 true false true) := by
  intro World M hM x hx
  have hx0 : M.Satisfies x (oneZeroOneFormula p i) := by simpa using hx
  have hrefute : forall y, M.Satisfies y (oneZeroOneFormula p i) ->
      Not ((M.update (oneZeroOneFormula p i)).Satisfies y (oneZeroOneFormula p i)) := by
    intro y hy
    exact oneZeroOne_selfRefuting p i M hM y hy
  have hempty := M.iterateUpdate_two_rel_empty_of_selfRefuting
    (oneZeroOneFormula p i) hrefute
  apply (Pattern.realizesTrace_bits3
    (trace := M.trace x (oneZeroOneFormula p i))
    (b0 := true) (b1 := false) (b2 := true)).2
  refine ⟨?_, ?_, ?_⟩
  · simpa [Pattern.HoldsBit, Model.trace] using hx0
  · simpa [Pattern.HoldsBit, Model.trace] using hrefute x hx0
  · simp only [Pattern.HoldsBit, if_true]
    apply (Model.satisfies_or _ _ _ _).mpr
    apply Or.inr
    intro y hxy
    exact (hempty i x y hxy).elim

theorem oneZeroOne_valid_oneZeroOnesInf [Inhabited Atom] (p : Atom) (i : Agent) :
    Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (oneZeroOneFormula p i) Pattern.oneZeroOnesInf :=
  Collapse.valid_oneZeroOne_implies_oneZeroOnesInf _ _ (oneZeroOne_valid_101 p i)

theorem threeWorldModel_oneZeroOne_initial [Inhabited Atom] (p : Atom) (i : Agent) :
    (threeWorldModel (Agent := Agent) p).Satisfies
      (⟨0⟩ : ULift.{u} (Fin 3))
      (oneZeroOneFormula p i) := by
  apply (Model.satisfies_or _ _ _ _).mpr
  apply Or.inl
  refine ⟨?_, ?_, ?_⟩
  · simp [threeWorldModel]
  · apply (Model.satisfies_dia _ _ _ _).mpr
    exact ⟨⟨0⟩, by trivial, by simp [threeWorldModel]⟩
  · apply (Model.satisfies_dia _ _ _ _).mpr
    exact ⟨⟨2⟩, by trivial, by simp [threeWorldModel]⟩

/-- The explicit S5 countermodel follows the truth trace `101`. -/
theorem threeWorldModel_oneZeroOne_trace_101 [Inhabited Atom]
    (p : Atom) (i : Agent) :
    let M : Model (ULift.{u} (Fin 3)) Atom Agent := threeWorldModel p
    M.trace (⟨0⟩ : ULift.{u} (Fin 3)) (oneZeroOneFormula p i) 0 /\
      Not (M.trace (⟨0⟩ : ULift.{u} (Fin 3)) (oneZeroOneFormula p i) 1) /\
      M.trace (⟨0⟩ : ULift.{u} (Fin 3)) (oneZeroOneFormula p i) 2 := by
  dsimp
  let M : Model (ULift.{u} (Fin 3)) Atom Agent := threeWorldModel p
  have hM : IsKD45 M := (threeWorldModel_isS5 (Agent := Agent) p).isKD45
  have hinitial : M.Satisfies (⟨0⟩ : ULift.{u} (Fin 3)) (oneZeroOneFormula p i) :=
    threeWorldModel_oneZeroOne_initial p i
  have hreal := oneZeroOne_valid_101 p i M hM ⟨0⟩ (by simpa using hinitial)
  simpa [Sigma.Realizes, Pattern.HoldsBit] using
    (Pattern.realizesTrace_bits3.mp hreal)

theorem oneZeroOne_satisfiable_oneZeroOnesInf [Inhabited Atom]
    (p : Atom) (i : Agent) :
    Sigma.Satisfiable (Classes.KD45 : FrameClass.{u} Atom Agent)
      (oneZeroOneFormula p i) Pattern.oneZeroOnesInf := by
  let M : Model (ULift.{u} (Fin 3)) Atom Agent := threeWorldModel p
  have hM : IsKD45 M := (threeWorldModel_isS5 (Agent := Agent) p).isKD45
  have hinitial : M.Satisfies (⟨0⟩ : ULift.{u} (Fin 3)) (oneZeroOneFormula p i) :=
    threeWorldModel_oneZeroOne_initial p i
  refine ⟨ULift.{u} (Fin 3), M, hM, ⟨0⟩, ?_⟩
  exact oneZeroOne_valid_oneZeroOnesInf p i M hM ⟨0⟩ (by simpa using hinitial)

theorem oneZeroOne_nontriviallyValid_oneZeroOnesInf [Inhabited Atom]
    (p : Atom) (i : Agent) :
    Sigma.NontriviallyValid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (oneZeroOneFormula p i) Pattern.oneZeroOnesInf :=
  ⟨oneZeroOne_valid_oneZeroOnesInf p i,
    oneZeroOne_satisfiable_oneZeroOnesInf p i⟩

/-- Publication-facing finite-prefix form of paper Lemma
`lem:101-validity`, KD45 case. -/
theorem oneZeroOne_nontriviallyValid_101_kd45 [Inhabited Atom]
    (p : Atom) (i : Agent) :
    Sigma.NontriviallyValid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (oneZeroOneFormula p i) (Pattern.bits3 true false true) :=
  ⟨oneZeroOne_valid_101 p i,
    by
      rcases oneZeroOne_satisfiable_oneZeroOnesInf p i with
        ⟨World, M, hM, x, hreal⟩
      refine ⟨World, M, hM, x, ?_⟩
      exact (Pattern.realizesTrace_bits3.mpr
        ⟨by simpa [Pattern.HoldsBit] using hreal 0,
          by simpa [Pattern.HoldsBit] using hreal 1,
          by simpa [Pattern.HoldsBit] using hreal 2⟩)⟩

/-- Publication-facing finite-prefix form of paper Lemma
`lem:101-validity`, S5 case. -/
theorem oneZeroOne_nontriviallyValid_101_s5 [Inhabited Atom]
    (p : Atom) (i : Agent) :
    Sigma.NontriviallyValid (Classes.S5 : FrameClass.{u} Atom Agent)
      (oneZeroOneFormula p i) (Pattern.bits3 true false true) := by
  constructor
  · exact Sigma.valid_mono_class
      (fun {World} (M : Model World Atom Agent) (hM : IsS5 M) => hM.isKD45)
      (oneZeroOne_valid_101 p i)
  · let M : Model (ULift.{u} (Fin 3)) Atom Agent := threeWorldModel p
    refine ⟨ULift.{u} (Fin 3), M, threeWorldModel_isS5 p, ⟨0⟩, ?_⟩
    exact (Pattern.realizesTrace_bits3.mpr
      (threeWorldModel_oneZeroOne_trace_101 p i))

/-- The same explicit three-world S5 model refutes `100`-validity. -/
theorem oneZeroOne_not_valid_100 [Inhabited Atom] (p : Atom) (i : Agent) :
    Not (Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      (oneZeroOneFormula p i) (Pattern.bits3 true false false)) := by
  intro h100
  let M : Model (ULift.{u} (Fin 3)) Atom Agent := threeWorldModel p
  have hM : IsKD45 M := (threeWorldModel_isS5 (Agent := Agent) p).isKD45
  have hinitial : M.Satisfies (⟨0⟩ : ULift.{u} (Fin 3)) (oneZeroOneFormula p i) :=
    threeWorldModel_oneZeroOne_initial p i
  have hreal100 := h100 M hM ⟨0⟩ (by simpa using hinitial)
  have htrace100 := Pattern.realizesTrace_bits3.mp hreal100
  have hfalse2 : Not (M.trace (⟨0⟩ : ULift.{u} (Fin 3))
      (oneZeroOneFormula p i) 2) := by
    simpa [Pattern.HoldsBit] using htrace100.2.2
  have htrace101 := threeWorldModel_oneZeroOne_trace_101 p i
  exact hfalse2 htrace101.2.2

/-- The same countermodel is S5, so it also gives the S5 half of the
non-`100` claim in paper Lemma `lem:10k-validity_collapse`. -/
theorem oneZeroOne_not_valid_100_s5 [Inhabited Atom] (p : Atom) (i : Agent) :
    Not (Sigma.Valid (Classes.S5 : FrameClass.{u} Atom Agent)
      (oneZeroOneFormula p i) (Pattern.bits3 true false false)) := by
  intro h100
  let M : Model (ULift.{u} (Fin 3)) Atom Agent := threeWorldModel p
  have hM : IsS5 M := threeWorldModel_isS5 p
  have hinitial : M.Satisfies (⟨0⟩ : ULift.{u} (Fin 3))
      (oneZeroOneFormula p i) := threeWorldModel_oneZeroOne_initial p i
  have hreal100 := h100 M hM ⟨0⟩ (by simpa using hinitial)
  have hfalse2 : Not (M.trace ⟨0⟩ (oneZeroOneFormula p i) 2) := by
    simpa [Pattern.HoldsBit] using
      (Pattern.realizesTrace_bits3.mp hreal100).2.2
  exact hfalse2 (threeWorldModel_oneZeroOne_trace_101 p i).2.2

end Examples

end ClassificationSigmaValidity
