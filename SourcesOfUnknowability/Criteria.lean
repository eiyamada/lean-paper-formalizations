import SourcesOfUnknowability.AgentDNF
import SourcesOfUnknowability.Independence
import ClassificationSigmaValidity.TypeFormulas

/-!
# Satisfiability criterion for independent agent-relative DNF clauses

This is the set-theoretic condition (4') in Theorem 4.  The finite lists below
represent the sets `B_S` and `Γ_S`; duplicates do not affect the criterion.
-/

namespace SourcesOfUnknowability.Criteria

open ClassificationSigmaValidity

universe u v w

variable {Atom : Type v} {Agent : Type w} [Inhabited Atom]

def boxInputs (selected : List (AgentDNF.Clause Atom Agent)) :
    List (Formula Atom Agent) := selected.flatMap AgentDNF.Clause.boxes

def diamondInputs (selected : List (AgentDNF.Clause Atom Agent)) :
    List (Formula Atom Agent) := selected.flatMap AgentDNF.Clause.diamonds

def alphaInputs (selected : List (AgentDNF.Clause Atom Agent)) :
    List (Formula Atom Agent) := selected.map AgentDNF.Clause.alpha

/-- `∧B_S ∧ (∨_{k∈S} α_k)` from Theorem 4(4'). -/
def objectiveCore (selected : List (AgentDNF.Clause Atom Agent)) :
    Formula Atom Agent :=
  .conj (Formula.conjList (boxInputs selected))
    (Formula.disjList (alphaInputs selected))

def SelectedCondition (selected : List (AgentDNF.Clause Atom Agent))
    {World : Type u} (M : Model World Atom Agent) (x : World) (i : Agent) : Prop :=
  (∀ c ∈ selected, AgentDNF.ModalPart c M x i) ∧
    ∀ y, M.rel i x y → ∃ c ∈ selected, M.Satisfies y c.alpha

theorem selectedCondition_iff_box_diamonds
    (selected : List (AgentDNF.Clause Atom Agent))
    {World : Type u} (M : Model World Atom Agent) (x : World) (i : Agent) :
    SelectedCondition selected M x i ↔
      M.Satisfies x (.box i (objectiveCore selected)) ∧
        (∀ gamma ∈ diamondInputs selected,
          M.Satisfies x (Formula.dia i gamma)) := by
  constructor
  · rintro ⟨hmodal, halpha⟩
    constructor
    · intro y hxy
      constructor
      · apply (M.satisfies_conjList y (boxInputs selected)).2
        intro beta hbeta
        obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp hbeta
        exact (hmodal c hc).1 beta hb y hxy
      · apply (M.satisfies_disjList y (alphaInputs selected)).2
        obtain ⟨c, hc, ha⟩ := halpha y hxy
        exact ⟨c.alpha, List.mem_map.mpr ⟨c, hc, rfl⟩, ha⟩
    · intro gamma hgamma
      obtain ⟨c, hc, hg⟩ := List.mem_flatMap.mp hgamma
      exact (hmodal c hc).2 gamma hg
  · rintro ⟨hbox, hdiamonds⟩
    constructor
    · intro c hc
      constructor
      · intro beta hbeta y hxy
        have hb : beta ∈ boxInputs selected :=
          List.mem_flatMap.mpr ⟨c, hc, hbeta⟩
        exact (M.satisfies_conjList y (boxInputs selected)).1
          (hbox y hxy).1 beta hb
      · intro gamma hgamma
        apply hdiamonds gamma
        exact List.mem_flatMap.mpr ⟨c, hc, hgamma⟩
    · intro y hxy
      obtain ⟨a, ha, hsat⟩ := (M.satisfies_disjList y
        (alphaInputs selected)).1 (hbox y hxy).2
      obtain ⟨c, hc, hca⟩ := List.mem_map.mp ha
      refine ⟨c, hc, ?_⟩
      simpa [hca] using hsat

def IndependentSelection (i : Agent)
    (selected : List (AgentDNF.Clause Atom Agent)) : Prop :=
  ∀ c ∈ selected, Independence.Independent i c.alpha ∧
    (∀ beta ∈ c.boxes, Independence.Independent i beta) ∧
    (∀ gamma ∈ c.diamonds, Independence.Independent i gamma)

private theorem independent_conjList (i : Agent)
    (formulas : List (Formula Atom Agent))
    (h : ∀ f ∈ formulas, Independence.Independent i f) :
    Independence.Independent i (Formula.conjList formulas) := by
  induction formulas with
  | nil => simp [Formula.conjList, Formula.verum, Formula.falsum,
      Independence.Independent]
  | cons f fs ih =>
      exact ⟨h f (by simp), ih (by
        intro g hg
        exact h g (by simp [hg]))⟩

private theorem independent_disjList (i : Agent)
    (formulas : List (Formula Atom Agent))
    (h : ∀ f ∈ formulas, Independence.Independent i f) :
    Independence.Independent i (Formula.disjList formulas) := by
  induction formulas with
  | nil => simp [Formula.disjList, Formula.falsum,
      Independence.Independent]
  | cons f fs ih =>
      change Independence.Independent i
        (Formula.or f (Formula.disjList fs))
      exact ⟨h f (by simp), ih (by
        intro g hg
        exact h g (by simp [hg]))⟩

theorem objectiveCore_independent (i : Agent)
    (selected : List (AgentDNF.Clause Atom Agent))
    (h : IndependentSelection i selected) :
    Independence.Independent i (objectiveCore selected) := by
  constructor
  · apply independent_conjList i (boxInputs selected)
    intro beta hb
    obtain ⟨c, hc, hbc⟩ := List.mem_flatMap.mp hb
    exact (h c hc).2.1 beta hbc
  · apply independent_disjList i (alphaInputs selected)
    intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    exact (h c hc).1

omit [Inhabited Atom] in theorem diamondInputs_independent (i : Agent)
    (selected : List (AgentDNF.Clause Atom Agent))
    (h : IndependentSelection i selected) :
    ∀ gamma ∈ diamondInputs selected,
      Independence.Independent i gamma := by
  intro gamma hg
  obtain ⟨c, hc, hgc⟩ := List.mem_flatMap.mp hg
  exact (h c hc).2.2 gamma hgc

/-- Lemma 8 applied to one selected subfamily in the theorem's condition
(4'): satisfiability is completely propositional/`i`-independent. -/
theorem selected_satisfiable_iff_kd45 (i : Agent)
    (selected : List (AgentDNF.Clause Atom Agent))
    (h : IndependentSelection i selected) :
    (∃ (World : Type u) (M : Model World Atom Agent) (x : World),
      IsKD45 M ∧ SelectedCondition selected M x i) ↔
      Static.Satisfiable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent)
        (objectiveCore selected) ∧
      (∀ gamma ∈ diamondInputs selected,
        Static.Satisfiable
          (Static.Classes.KD45 : FrameClass.{u} Atom Agent)
          (.conj (objectiveCore selected) gamma)) := by
  rw [← Independence.lemma8_kd45 i (objectiveCore selected)
    (diamondInputs selected) (objectiveCore_independent i selected h)
    (diamondInputs_independent i selected h)]
  constructor
  · rintro ⟨World, M, x, hM, hselected⟩
    exact ⟨World, M, x, hM,
      (selectedCondition_iff_box_diamonds selected M x i).mp hselected⟩
  · rintro ⟨World, M, x, hM, hbox, hdia⟩
    exact ⟨World, M, x, hM,
      (selectedCondition_iff_box_diamonds selected M x i).mpr ⟨hbox, hdia⟩⟩

theorem selected_satisfiable_iff_s5 (i : Agent)
    (selected : List (AgentDNF.Clause Atom Agent))
    (h : IndependentSelection i selected) :
    (∃ (World : Type u) (M : Model World Atom Agent) (x : World),
      IsS5 M ∧ SelectedCondition selected M x i) ↔
      Static.Satisfiable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent)
        (objectiveCore selected) ∧
      (∀ gamma ∈ diamondInputs selected,
        Static.Satisfiable
          (Static.Classes.S5 : FrameClass.{u} Atom Agent)
          (.conj (objectiveCore selected) gamma)) := by
  rw [← Independence.lemma8_s5 i (objectiveCore selected)
    (diamondInputs selected) (objectiveCore_independent i selected h)
    (diamondInputs_independent i selected h)]
  constructor
  · rintro ⟨World, M, x, hM, hselected⟩
    exact ⟨World, M, x, hM,
      (selectedCondition_iff_box_diamonds selected M x i).mp hselected⟩
  · rintro ⟨World, M, x, hM, hbox, hdia⟩
    exact ⟨World, M, x, hM,
      (selectedCondition_iff_box_diamonds selected M x i).mpr ⟨hbox, hdia⟩⟩

/-- Theorem 4(4') in KD45.  The `IndependentSelection` hypothesis is exactly
the paper's stated condition that the selected objective and modal scopes do
not contain the distinguished agent's modality. -/
theorem unbelievable_iff_independent_obstructions_kd45
    (i : Agent) (phi : Formula Atom Agent)
    (clauses : List (AgentDNF.Clause Atom Agent))
    (hform : ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x : World,
      M.Satisfies x phi ↔ AgentDNF.HoldsDNF clauses M x i)
    (hind : IndependentSelection i clauses) :
    Static.Unbelievable
      (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi ↔
      ∀ selected : List (AgentDNF.Clause Atom Agent),
        (∀ c ∈ selected, c ∈ clauses) →
          (¬ Static.Satisfiable
              (Static.Classes.KD45 : FrameClass.{u} Atom Agent)
              (objectiveCore selected) ∨
            ∃ gamma ∈ diamondInputs selected,
              ¬ Static.Satisfiable
                (Static.Classes.KD45 : FrameClass.{u} Atom Agent)
                (.conj (objectiveCore selected) gamma)) := by
  classical
  constructor
  · intro h selected hsub
    have hsel : IndependentSelection i selected :=
      fun c hc => hind c (hsub c hc)
    have hno := (AgentDNF.unbelievable_iff_no_decomposedWeak_kd45
      clauses phi i hform).mp h
    have hbad : ¬ (Static.Satisfiable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent)
        (objectiveCore selected) ∧
      ∀ gamma ∈ diamondInputs selected,
        Static.Satisfiable
          (Static.Classes.KD45 : FrameClass.{u} Atom Agent)
          (.conj (objectiveCore selected) gamma)) := by
      intro hs
      obtain ⟨World, M, x, hM, hc⟩ :=
        (selected_satisfiable_iff_kd45 i selected hsel).mpr hs
      exact hno World M hM x
        ⟨selected, fun c hcs => ⟨hsub c hcs, hc.1 c hcs⟩, hc.2⟩
    by_cases hb : Static.Satisfiable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent)
        (objectiveCore selected)
    · right
      by_contra hnone
      apply hbad
      refine ⟨hb, ?_⟩
      intro gamma hgamma
      by_contra hnot
      exact hnone ⟨gamma, hgamma, hnot⟩
    · exact Or.inl hb
  · intro h
    apply (AgentDNF.unbelievable_iff_no_decomposedWeak_kd45
      clauses phi i hform).mpr
    intro World M hM x hd
    obtain ⟨selected, hsubset, halpha⟩ := hd
    have hsub : ∀ c ∈ selected, c ∈ clauses :=
      fun c hc => (hsubset c hc).1
    have hsel : IndependentSelection i selected :=
      fun c hc => hind c (hsub c hc)
    have hs := (selected_satisfiable_iff_kd45 i selected hsel).mp
      ⟨World, M, x, hM,
        ⟨fun c hc => (hsubset c hc).2, halpha⟩⟩
    rcases h selected hsub with hbad | ⟨gamma, hgamma, hbad⟩
    · exact hbad hs.1
    · exact hbad (hs.2 gamma hgamma)

/-- The S5 version of the simplified multi-agent criterion. -/
theorem unbelievable_iff_independent_obstructions_s5
    (i : Agent) (phi : Formula Atom Agent)
    (clauses : List (AgentDNF.Clause Atom Agent))
    (hform : ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x : World,
      M.Satisfies x phi ↔ AgentDNF.HoldsDNF clauses M x i)
    (hind : IndependentSelection i clauses) :
    Static.Unbelievable
      (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi ↔
      ∀ selected : List (AgentDNF.Clause Atom Agent),
        (∀ c ∈ selected, c ∈ clauses) →
          (¬ Static.Satisfiable
              (Static.Classes.S5 : FrameClass.{u} Atom Agent)
              (objectiveCore selected) ∨
            ∃ gamma ∈ diamondInputs selected,
              ¬ Static.Satisfiable
                (Static.Classes.S5 : FrameClass.{u} Atom Agent)
                (.conj (objectiveCore selected) gamma)) := by
  classical
  constructor
  · intro h selected hsub
    have hsel : IndependentSelection i selected :=
      fun c hc => hind c (hsub c hc)
    have hno := (AgentDNF.unbelievable_iff_no_decomposedWeak_s5
      clauses phi i hform).mp h
    have hbad : ¬ (Static.Satisfiable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent)
        (objectiveCore selected) ∧
      ∀ gamma ∈ diamondInputs selected,
        Static.Satisfiable
          (Static.Classes.S5 : FrameClass.{u} Atom Agent)
          (.conj (objectiveCore selected) gamma)) := by
      intro hs
      obtain ⟨World, M, x, hM, hc⟩ :=
        (selected_satisfiable_iff_s5 i selected hsel).mpr hs
      exact hno World M hM x
        ⟨selected, fun c hcs => ⟨hsub c hcs, hc.1 c hcs⟩, hc.2⟩
    by_cases hb : Static.Satisfiable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent)
        (objectiveCore selected)
    · right
      by_contra hnone
      apply hbad
      refine ⟨hb, ?_⟩
      intro gamma hgamma
      by_contra hnot
      exact hnone ⟨gamma, hgamma, hnot⟩
    · exact Or.inl hb
  · intro h
    apply (AgentDNF.unbelievable_iff_no_decomposedWeak_s5
      clauses phi i hform).mpr
    intro World M hM x hd
    obtain ⟨selected, hsubset, halpha⟩ := hd
    have hsub : ∀ c ∈ selected, c ∈ clauses :=
      fun c hc => (hsubset c hc).1
    have hsel : IndependentSelection i selected :=
      fun c hc => hind c (hsub c hc)
    have hs := (selected_satisfiable_iff_s5 i selected hsel).mp
      ⟨World, M, x, hM,
        ⟨fun c hc => (hsubset c hc).2, halpha⟩⟩
    rcases h selected hsub with hbad | ⟨gamma, hgamma, hbad⟩
    · exact hbad hs.1
    · exact hbad (hs.2 gamma hgamma)

/- With a single agent, every agent-objective formula is propositional and
therefore independent of that agent. -/
omit [Inhabited Atom] in theorem objective_unit_independent (phi : Formula Atom Unit)
    (h : AgentDNF.Objective () phi) : Independence.Independent () phi := by
  induction phi with
  | atom _ => trivial
  | neg psi ih => exact ih h
  | conj psi chi ihpsi ihchi => exact ⟨ihpsi h.1, ihchi h.2⟩
  | box j _ =>
      cases j
      exact False.elim (h rfl)

omit [Inhabited Atom] in theorem independentSelection_unit_of_isIDNF
    (clauses : List (AgentDNF.Clause Atom Unit))
    (h : AgentDNF.IsIDNF () clauses) :
    IndependentSelection () clauses := by
  intro c hc
  obtain ⟨ha, hb, hd⟩ := h c hc
  exact ⟨objective_unit_independent c.alpha ha,
    fun beta hbeta => objective_unit_independent beta (hb beta hbeta),
    fun gamma hgamma => objective_unit_independent gamma (hd gamma hgamma)⟩

/-- Theorem 3(4) in its propositional satisfiability form.  The
`IsIDNF` condition makes the single-agent clause components propositional. -/
theorem unbelievable_iff_propositional_obstructions_s5
    (phi : Formula Atom Unit)
    (clauses : List (AgentDNF.Clause Atom Unit))
    (hform : ∀ {World : Type u} (M : Model World Atom Unit), IsK45 M → ∀ x : World,
      M.Satisfies x phi ↔ AgentDNF.HoldsDNF clauses M x ())
    (hidnf : AgentDNF.IsIDNF () clauses) :
    Static.Unbelievable
      (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      ∀ selected : List (AgentDNF.Clause Atom Unit),
        (∀ c ∈ selected, c ∈ clauses) →
          (¬ Static.Satisfiable
              (Static.Classes.S5 : FrameClass.{u} Atom Unit)
              (objectiveCore selected) ∨
            ∃ gamma ∈ diamondInputs selected,
              ¬ Static.Satisfiable
                (Static.Classes.S5 : FrameClass.{u} Atom Unit)
                (.conj (objectiveCore selected) gamma)) :=
  unbelievable_iff_independent_obstructions_s5 () phi clauses hform
    (independentSelection_unit_of_isIDNF clauses hidnf)

/-- Theorem 3(4) for KD45 in its propositional satisfiability form. -/
theorem unbelievable_iff_propositional_obstructions_kd45
    (phi : Formula Atom Unit)
    (clauses : List (AgentDNF.Clause Atom Unit))
    (hform : ∀ {World : Type u} (M : Model World Atom Unit), IsK45 M → ∀ x : World,
      M.Satisfies x phi ↔ AgentDNF.HoldsDNF clauses M x ())
    (hidnf : AgentDNF.IsIDNF () clauses) :
    Static.Unbelievable
      (Static.Classes.KD45 : FrameClass.{u} Atom Unit) () phi ↔
      ∀ selected : List (AgentDNF.Clause Atom Unit),
        (∀ c ∈ selected, c ∈ clauses) →
          (¬ Static.Satisfiable
              (Static.Classes.KD45 : FrameClass.{u} Atom Unit)
              (objectiveCore selected) ∨
            ∃ gamma ∈ diamondInputs selected,
              ¬ Static.Satisfiable
                (Static.Classes.KD45 : FrameClass.{u} Atom Unit)
                (.conj (objectiveCore selected) gamma)) :=
  unbelievable_iff_independent_obstructions_kd45 () phi clauses hform
    (independentSelection_unit_of_isIDNF clauses hidnf)

end SourcesOfUnknowability.Criteria
