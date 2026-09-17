import SourcesOfUnknowability.Static

/-!
# Agent-relative normal forms and the multi-agent subset decomposition

The paper's `i`-objective formulas may contain beliefs of other agents.  Hence
their objective component cannot be restricted to propositional formulas.  The
subset argument needs only the leading `i`-modal part of each clause to be
constant along `i`-accessibility, which holds on K45 frames.
-/

namespace SourcesOfUnknowability.AgentDNF

open ClassificationSigmaValidity

universe u v w

variable {Atom : Type v} {Agent : Type w}

/-- Definition 13: every outermost modal operator has an agent other than
`i`; the contents of such an operator may still mention `i`. -/
def Objective (i : Agent) : Formula Atom Agent → Prop
  | .atom _ => True
  | .neg phi => Objective i phi
  | .conj phi psi => Objective i phi ∧ Objective i psi
  | .box j _ => j ≠ i

/-- The semantic components of an `i`-DNF disjunct. -/
structure Clause (Atom : Type v) (Agent : Type w) where
  alpha : Formula Atom Agent
  boxes : List (Formula Atom Agent)
  diamonds : List (Formula Atom Agent)

/-- The syntactic `i`-objective side conditions of Definition 13.  A single
objective formula counts as a one-term conjunction or disjunction. -/
def IsIDNF (i : Agent) (clauses : List (Clause Atom Agent)) : Prop :=
  ∀ c ∈ clauses, Objective i c.alpha ∧
    (∀ beta ∈ c.boxes, Objective i beta) ∧
    (∀ gamma ∈ c.diamonds, Objective i gamma)

def ModalPart (c : Clause Atom Agent) {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent) : Prop :=
  (∀ beta ∈ c.boxes, M.Satisfies x (.box i beta)) ∧
    (∀ gamma ∈ c.diamonds, M.Satisfies x (Formula.dia i gamma))

def Holds (c : Clause Atom Agent) {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent) : Prop :=
  M.Satisfies x c.alpha ∧ ModalPart c M x i

def HoldsDNF (clauses : List (Clause Atom Agent)) {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent) : Prop :=
  ∃ c ∈ clauses, Holds c M x i

theorem modalPart_agree (c : Clause Atom Agent) {World : Type u}
    {M : Model World Atom Agent} (hM : IsK45 M)
    {i : Agent} {x y : World} (hxy : M.rel i x y) :
    ModalPart c M x i ↔ ModalPart c M y i := by
  constructor
  · rintro ⟨hb, hd⟩
    constructor
    · intro beta hbeta
      exact (M.modalAgreement_box hM hxy beta).mp (hb beta hbeta)
    · intro gamma hgamma
      exact (M.modalAgreement_dia hM hxy gamma).mp (hd gamma hgamma)
  · rintro ⟨hb, hd⟩
    constructor
    · intro beta hbeta
      exact (M.modalAgreement_box hM hxy beta).mpr (hb beta hbeta)
    · intro gamma hgamma
      exact (M.modalAgreement_dia hM hxy gamma).mpr (hd gamma hgamma)

/-- The semantic right hand side of Lemma 7 and Theorem 4(4). -/
def Decomposed (clauses : List (Clause Atom Agent)) {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent) : Prop :=
  ∃ selected : List (Clause Atom Agent),
    (∀ c, c ∈ selected ↔ c ∈ clauses ∧ ModalPart c M x i) ∧
    ∀ y, M.rel i x y → ∃ c ∈ selected, M.Satisfies y c.alpha

/-- The paper's subset formulation requires the selected modal parts to hold;
it imposes no condition on unselected clauses. -/
def DecomposedWeak (clauses : List (Clause Atom Agent)) {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent) : Prop :=
  ∃ selected : List (Clause Atom Agent),
    (∀ c ∈ selected, c ∈ clauses ∧ ModalPart c M x i) ∧
    ∀ y, M.rel i x y → ∃ c ∈ selected, M.Satisfies y c.alpha

/-- Lemma 7, in a pointwise semantic form that works for multi-agent K45.
The selected list represents the subset `S` of disjuncts in the paper. -/
theorem box_iff_decomposed (clauses : List (Clause Atom Agent))
    {World : Type u} {M : Model World Atom Agent} (hM : IsK45 M)
    (x : World) (i : Agent) :
    (∀ y, M.rel i x y → HoldsDNF clauses M y i) ↔
      Decomposed clauses M x i := by
  classical
  constructor
  · intro h
    refine ⟨clauses.filter (fun c => decide (ModalPart c M x i)), ?_, ?_⟩
    · intro c
      simp
    · intro y hxy
      obtain ⟨c, hc, ha, hm⟩ := h y hxy
      refine ⟨c, ?_, ha⟩
      simp [hc, (modalPart_agree c hM hxy).mpr hm]
  · rintro ⟨selected, hselected, h⟩ y hxy
    obtain ⟨c, hc, ha⟩ := h y hxy
    have hc' := (hselected c).mp hc
    exact ⟨c, hc'.1, ha, (modalPart_agree c hM hxy).mp hc'.2⟩

/-- Lemma 7 with the paper's unrestricted choice of subset `S`. -/
theorem box_iff_decomposedWeak (clauses : List (Clause Atom Agent))
    {World : Type u} {M : Model World Atom Agent} (hM : IsK45 M)
    (x : World) (i : Agent) :
    (∀ y, M.rel i x y → HoldsDNF clauses M y i) ↔
      DecomposedWeak clauses M x i := by
  constructor
  · intro h
    obtain ⟨selected, hselected, halpha⟩ :=
      (box_iff_decomposed clauses hM x i).mp h
    exact ⟨selected, fun c hc => (hselected c).mp hc, halpha⟩
  · rintro ⟨selected, hselected, halpha⟩ y hxy
    obtain ⟨c, hc, ha⟩ := halpha y hxy
    obtain ⟨hmem, hmodal⟩ := hselected c hc
    exact ⟨c, hmem, ha, (modalPart_agree c hM hxy).mp hmodal⟩

/-- Theorem 4(1) iff (4): in any K45 subclass, unbelievability is precisely
unsatisfiability of the decomposed boxed normal form. -/
theorem unbelievable_iff_no_decomposed
    (C : FrameClass.{u} Atom Agent)
    (hC : ∀ {World : Type u} (M : Model World Atom Agent), C M → IsK45 M)
    (clauses : List (Clause Atom Agent)) (phi : Formula Atom Agent) (i : Agent)
    (hform : ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x : World,
      M.Satisfies x phi ↔ HoldsDNF clauses M x i) :
    Static.Unbelievable C i phi ↔
      ∀ (World : Type u) (M : Model World Atom Agent), C M → ∀ x,
        ¬ Decomposed clauses M x i := by
  constructor
  · intro h World M hM x hd
    apply h
    refine ⟨World, M, hM, x, ?_⟩
    intro y hxy
    exact (hform M (hC M hM) y).mpr
      ((box_iff_decomposed clauses (hC M hM) x i).mpr hd y hxy)
  · intro h ⟨World, M, hM, x, hbox⟩
    apply h World M hM x
    apply (box_iff_decomposed clauses (hC M hM) x i).mp
    intro y hxy
    exact (hform M (hC M hM) y).mp (hbox y hxy)

theorem unbelievable_iff_no_decomposed_kd45
    (clauses : List (Clause Atom Agent)) (phi : Formula Atom Agent) (i : Agent)
    (hform : ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x : World,
      M.Satisfies x phi ↔ HoldsDNF clauses M x i) :
    Static.Unbelievable
      (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi ↔
      ∀ (World : Type u) (M : Model World Atom Agent), IsKD45 M → ∀ x,
        ¬ Decomposed clauses M x i := by
  exact unbelievable_iff_no_decomposed _
    (fun M hM => hM.isK45) clauses phi i hform

theorem unbelievable_iff_no_decomposed_s5
    (clauses : List (Clause Atom Agent)) (phi : Formula Atom Agent) (i : Agent)
    (hform : ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x : World,
      M.Satisfies x phi ↔ HoldsDNF clauses M x i) :
    Static.Unbelievable
      (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi ↔
      ∀ (World : Type u) (M : Model World Atom Agent), IsS5 M → ∀ x,
        ¬ Decomposed clauses M x i := by
  exact unbelievable_iff_no_decomposed _
    (fun M hM => hM.isK45) clauses phi i hform

/-- Theorem 4(4), literally using the selected-subset expression in the
paper, for KD45. -/
theorem unbelievable_iff_no_decomposedWeak_kd45
    (clauses : List (Clause Atom Agent)) (phi : Formula Atom Agent) (i : Agent)
    (hform : ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x : World,
      M.Satisfies x phi ↔ HoldsDNF clauses M x i) :
    Static.Unbelievable
      (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi ↔
      ∀ (World : Type u) (M : Model World Atom Agent), IsKD45 M → ∀ x,
        ¬ DecomposedWeak clauses M x i := by
  constructor
  · intro h World M hM x hd
    apply h
    refine ⟨World, M, hM, x, ?_⟩
    intro y hxy
    exact (hform M hM.isK45 y).mpr
      ((box_iff_decomposedWeak clauses hM.isK45 x i).mpr hd y hxy)
  · intro h ⟨World, M, hM, x, hbox⟩
    apply h World M hM x
    apply (box_iff_decomposedWeak clauses hM.isK45 x i).mp
    intro y hxy
    exact (hform M hM.isK45 y).mp (hbox y hxy)

theorem unbelievable_iff_no_decomposedWeak_s5
    (clauses : List (Clause Atom Agent)) (phi : Formula Atom Agent) (i : Agent)
    (hform : ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x : World,
      M.Satisfies x phi ↔ HoldsDNF clauses M x i) :
    Static.Unbelievable
      (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi ↔
      ∀ (World : Type u) (M : Model World Atom Agent), IsS5 M → ∀ x,
        ¬ DecomposedWeak clauses M x i := by
  constructor
  · intro h World M hM x hd
    apply h
    refine ⟨World, M, hM, x, ?_⟩
    intro y hxy
    exact (hform M hM.isK45 y).mpr
      ((box_iff_decomposedWeak clauses hM.isK45 x i).mpr hd y hxy)
  · intro h ⟨World, M, hM, x, hbox⟩
    apply h World M hM x
    apply (box_iff_decomposedWeak clauses hM.isK45 x i).mp
    intro y hxy
    exact (hform M hM.isK45 y).mp (hbox y hxy)

end SourcesOfUnknowability.AgentDNF
