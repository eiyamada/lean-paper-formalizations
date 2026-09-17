import SourcesOfUnknowability.AgentNormalization
import SourcesOfUnknowability.Main
import SourcesOfUnknowability.Criteria
import SourcesOfUnknowability.LiteralNormalForms

/-!
# Main results with constructed normal forms

The preceding theorems allow a supplied `i`-DNF. Lemma 9 now constructs one
for every formula, so the numbered results can be stated without a separate
normal-form equivalence hypothesis.
-/

namespace SourcesOfUnknowability.NormalizedResults

open ClassificationSigmaValidity

universe u v w

variable {Atom : Type v} {Agent : Type w} [Inhabited Atom]

/-- The explicit normal form, with classical equality used only to decide
whether an operator belongs to the selected agent. -/
noncomputable def clauses (i : Agent) (phi : Formula Atom Agent) :
    List (AgentDNF.Clause Atom Agent) := by
  classical
  exact AgentNormalization.positive i phi

theorem clauses_are_iDNF (i : Agent) (phi : Formula Atom Agent) :
    AgentDNF.IsIDNF i (clauses i phi) := by
  classical
  simpa [clauses] using (AgentNormalization.normalizers_are_iDNF i phi).1

theorem clauses_equivalent_k45 (i : Agent) (phi : Formula Atom Agent)
    {World : Type u} (M : Model World Atom Agent) (hM : IsK45 M)
    (x : World) :
    M.Satisfies x phi ↔ AgentDNF.HoldsDNF (clauses i phi) M x i := by
  classical
  simpa [clauses] using (AgentNormalization.lemma9 i phi).2 M hM x

/-- Theorem 4(1)--(4) for every formula in KD45, with its `i`-DNF built
by the normalizer. -/
theorem theorem4_kd45 (i : Agent) (phi : Formula Atom Agent) :
    (Static.Unbelievable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi ↔
      Static.Unknowable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi) ∧
    (Static.Unknowable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi ↔
      Static.Equivalent
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent) phi
        (Static.moore i phi)) ∧
    (Static.Unbelievable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi ↔
      ∀ (World : Type u) (M : Model World Atom Agent), IsKD45 M → ∀ x,
        ¬ AgentDNF.DecomposedWeak (clauses i phi) M x i) := by
  exact Main.theorem4_kd45 i phi (clauses i phi)
    (fun M hM x => clauses_equivalent_k45 i phi M hM x)

/-- Theorem 4(1)--(4) for every formula in S5. -/
theorem theorem4_s5 (i : Agent) (phi : Formula Atom Agent) :
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi ↔
      Static.Unknowable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi) ∧
    (Static.Unknowable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi ↔
      Static.Equivalent
        (Static.Classes.S5 : FrameClass.{u} Atom Agent) phi
        (Static.moore i phi)) ∧
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi ↔
      ∀ (World : Type u) (M : Model World Atom Agent), IsS5 M → ∀ x,
        ¬ AgentDNF.DecomposedWeak (clauses i phi) M x i) := by
  exact Main.theorem4_s5 i phi (clauses i phi)
    (fun M hM x => clauses_equivalent_k45 i phi M hM x)

/-- Theorem 3(1)--(5) in KD45, using a constructed K45-DNF with the
paper's exact literal grammar. -/
theorem theorem3_kd45 (phi : Formula Atom Unit) :
    (Static.Unbelievable
        (Static.Classes.KD45 : FrameClass.{u} Atom Unit) () phi ↔
      Static.Unknowable
        (Static.Classes.KD45 : FrameClass.{u} Atom Unit) () phi) ∧
    (Static.Unknowable
        (Static.Classes.KD45 : FrameClass.{u} Atom Unit) () phi ↔
      Static.Equivalent
        (Static.Classes.KD45 : FrameClass.{u} Atom Unit) phi
        (Static.moore () phi)) ∧
    (Static.Unbelievable
        (Static.Classes.KD45 : FrameClass.{u} Atom Unit) () phi ↔
      ∀ selected : List (AgentDNF.Clause Atom Unit),
        (∀ c ∈ selected, c ∈ LiteralNormalForms.strictK45DNF phi) →
          (¬ Static.Satisfiable
              (Static.Classes.KD45 : FrameClass.{u} Atom Unit)
              (Criteria.objectiveCore selected) ∨
            ∃ gamma ∈ Criteria.diamondInputs selected,
              ¬ Static.Satisfiable
                (Static.Classes.KD45 : FrameClass.{u} Atom Unit)
                (.conj (Criteria.objectiveCore selected) gamma))) ∧
    (Static.Unbelievable
        (Static.Classes.KD45 : FrameClass.{u} Atom Unit) () phi ↔
      Dynamic.AlwaysInformative
        (Static.Classes.KD45 : FrameClass.{u} Atom Unit) phi) := by
  exact ⟨Static.unbelievable_iff_unknowable_kd45 () phi,
    Static.unknowable_iff_mooreFixed _ () phi,
    Criteria.unbelievable_iff_propositional_obstructions_kd45
      phi (LiteralNormalForms.strictK45DNF phi)
      (fun M hM x => LiteralNormalForms.strictK45DNF_equivalent phi M hM x)
      (LiteralNormalForms.strictK45DNF_isIDNF phi),
    DynamicResults.unbelievable_iff_alwaysInformative_kd45 phi⟩

/-- Theorem 3's six conditions in S5. Condition (4) uses a constructed
K45-DNF satisfying the paper's exact literal grammar. -/
theorem theorem3_s5 (phi : Formula Atom Unit) :
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Static.Unknowable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi) ∧
    (Static.Unknowable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Static.Equivalent
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi
        (Static.moore () phi)) ∧
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      ∀ selected : List (AgentDNF.Clause Atom Unit),
        (∀ c ∈ selected, c ∈ LiteralNormalForms.strictK45DNF phi) →
          (¬ Static.Satisfiable
              (Static.Classes.S5 : FrameClass.{u} Atom Unit)
              (Criteria.objectiveCore selected) ∨
            ∃ gamma ∈ Criteria.diamondInputs selected,
              ¬ Static.Satisfiable
                (Static.Classes.S5 : FrameClass.{u} Atom Unit)
                (.conj (Criteria.objectiveCore selected) gamma))) ∧
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Dynamic.AlwaysInformative
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi) ∧
    (Static.Unbelievable
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
      Dynamic.EventuallySelfRefuting
        (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi) := by
  exact ⟨Static.unbelievable_iff_unknowable_s5 () phi,
    Static.unknowable_iff_mooreFixed _ () phi,
    Criteria.unbelievable_iff_propositional_obstructions_s5
      phi (LiteralNormalForms.strictK45DNF phi)
      (fun M hM x => LiteralNormalForms.strictK45DNF_equivalent phi M hM x)
      (LiteralNormalForms.strictK45DNF_isIDNF phi),
    DynamicResults.unbelievable_iff_alwaysInformative_s5 phi,
    Eventually.unbelievable_iff_eventuallySelfRefuting_s5 phi⟩

/-- Theorem 4(4′) for the constructed normal form in KD45, under exactly
the paper's independence condition on its selected components. -/
theorem theorem4_prime_kd45 (i : Agent) (phi : Formula Atom Agent)
    (hind : Criteria.IndependentSelection i (clauses i phi)) :
    Static.Unbelievable
      (Static.Classes.KD45 : FrameClass.{u} Atom Agent) i phi ↔
      ∀ selected : List (AgentDNF.Clause Atom Agent),
        (∀ c ∈ selected, c ∈ clauses i phi) →
          (¬ Static.Satisfiable
              (Static.Classes.KD45 : FrameClass.{u} Atom Agent)
              (Criteria.objectiveCore selected) ∨
            ∃ gamma ∈ Criteria.diamondInputs selected,
              ¬ Static.Satisfiable
                (Static.Classes.KD45 : FrameClass.{u} Atom Agent)
                (.conj (Criteria.objectiveCore selected) gamma)) := by
  exact Criteria.unbelievable_iff_independent_obstructions_kd45
    i phi (clauses i phi)
    (fun M hM x => clauses_equivalent_k45 i phi M hM x) hind

/-- Theorem 4(4′) for the constructed normal form in S5. -/
theorem theorem4_prime_s5 (i : Agent) (phi : Formula Atom Agent)
    (hind : Criteria.IndependentSelection i (clauses i phi)) :
    Static.Unbelievable
      (Static.Classes.S5 : FrameClass.{u} Atom Agent) i phi ↔
      ∀ selected : List (AgentDNF.Clause Atom Agent),
        (∀ c ∈ selected, c ∈ clauses i phi) →
          (¬ Static.Satisfiable
              (Static.Classes.S5 : FrameClass.{u} Atom Agent)
              (Criteria.objectiveCore selected) ∨
            ∃ gamma ∈ Criteria.diamondInputs selected,
              ¬ Static.Satisfiable
                (Static.Classes.S5 : FrameClass.{u} Atom Agent)
                (.conj (Criteria.objectiveCore selected) gamma)) := by
  exact Criteria.unbelievable_iff_independent_obstructions_s5
    i phi (clauses i phi)
    (fun M hM x => clauses_equivalent_k45 i phi M hM x) hind

end SourcesOfUnknowability.NormalizedResults
