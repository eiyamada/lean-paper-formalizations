import SourcesOfUnknowability.DNFNormalization
import SourcesOfUnknowability.AgentNormalization

/-!
# Literal normal-form grammar

Definitions 3 and 5 of the paper specify literal conjunctions and disjunctions
rather than merely modal-free formulas. The predicates below make that
additional syntactic condition explicit. Truth and falsity are the empty
conjunction and disjunction, represented by the existing formula abbreviations.
-/

namespace SourcesOfUnknowability.LiteralNormalForms

open ClassificationSigmaValidity

universe u v

variable {Atom : Type v} [Inhabited Atom]

/-- A finite conjunction of positive or negative proposition letters. -/
inductive LiteralConjunction : Formula Atom Unit → Prop where
  | verum : LiteralConjunction Formula.verum
  | pos (p : Atom) : LiteralConjunction (.atom p)
  | neg (p : Atom) : LiteralConjunction (.neg (.atom p))
  | conj {φ ψ : Formula Atom Unit} :
      LiteralConjunction φ → LiteralConjunction ψ →
        LiteralConjunction (.conj φ ψ)

/-- A finite disjunction of positive or negative proposition letters. -/
inductive LiteralDisjunction : Formula Atom Unit → Prop where
  | falsum : LiteralDisjunction Formula.falsum
  | pos (p : Atom) : LiteralDisjunction (.atom p)
  | neg (p : Atom) : LiteralDisjunction (.neg (.atom p))
  | disj {φ ψ : Formula Atom Unit} :
      LiteralDisjunction φ → LiteralDisjunction ψ →
        LiteralDisjunction (Formula.or φ ψ)

/-- Definition 3's exact condition on the propositional part of a K-DNF
clause. The box and diamond scopes remain arbitrary formulas. -/
def IsKClause (c : DNF.Clause Atom Unit) : Prop :=
  LiteralConjunction c.alpha

def IsKDNF (cs : List (DNF.Clause Atom Unit)) : Prop :=
  ∀ c ∈ cs, IsKClause c

/-- Definition 5's exact literal grammar for a single-agent K45-DNF clause. -/
def IsK45Clause (c : AgentDNF.Clause Atom Unit) : Prop :=
  LiteralConjunction c.alpha ∧
    (∀ β ∈ c.boxes, LiteralDisjunction β) ∧
    (∀ γ ∈ c.diamonds, LiteralConjunction γ)

def IsK45DNF (cs : List (AgentDNF.Clause Atom Unit)) : Prop :=
  ∀ c ∈ cs, IsK45Clause c

theorem literalConjunction_modalFree {φ : Formula Atom Unit}
    (h : LiteralConjunction φ) : φ.modalDepth = 0 := by
  induction h with
  | verum => simp [Formula.verum, Formula.falsum, Formula.modalDepth]
  | pos p => rfl
  | neg p => rfl
  | conj hφ hψ ihφ ihψ => simp [Formula.modalDepth, ihφ, ihψ]

theorem literalDisjunction_modalFree {φ : Formula Atom Unit}
    (h : LiteralDisjunction φ) : φ.modalDepth = 0 := by
  induction h with
  | falsum => simp [Formula.falsum, Formula.modalDepth]
  | pos p => rfl
  | neg p => rfl
  | disj hφ hψ ihφ ihψ => simp [Formula.modalDepth_or, ihφ, ihψ]

private theorem k_join (c d : DNF.Clause Atom Unit)
    (hc : IsKClause c) (hd : IsKClause d) :
    IsKClause (DNFNormalization.join c d) :=
  LiteralConjunction.conj hc hd

private theorem k_conjunction (xs ys : List (DNF.Clause Atom Unit))
    (hx : IsKDNF xs) (hy : IsKDNF ys) :
    IsKDNF (DNFNormalization.conjunction xs ys) := by
  intro e he
  change e ∈ xs.flatMap (fun c => ys.map (DNFNormalization.join c)) at he
  obtain ⟨c, hc, hmap⟩ := List.mem_flatMap.mp he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmap
  exact k_join c d (hx c hc) (hy d hd)

/-- Both recursive K normalizers output clauses satisfying the manuscript's
literal-conjunction grammar. -/
theorem k_normalizers_literal (φ : Formula Atom Unit) :
    IsKDNF (DNFNormalization.positive φ) ∧
      IsKDNF (DNFNormalization.negative φ) := by
  induction φ with
  | atom p =>
      constructor
      · intro c hc
        have heq : c = DNFNormalization.atomClause p := by
          simpa [DNFNormalization.positive] using hc
        subst c
        exact LiteralConjunction.pos p
      · intro c hc
        have heq : c = DNFNormalization.negAtomClause p := by
          simpa [DNFNormalization.negative] using hc
        subst c
        exact LiteralConjunction.neg p
  | neg ψ ih =>
      simpa [DNFNormalization.positive, DNFNormalization.negative] using And.symm ih
  | conj ψ χ ihψ ihχ =>
      constructor
      · simpa [DNFNormalization.positive] using
          k_conjunction (DNFNormalization.positive ψ)
            (DNFNormalization.positive χ) ihψ.1 ihχ.1
      · intro c hc
        have hmem : c ∈ DNFNormalization.negative ψ ++
            DNFNormalization.negative χ := by
          simpa [DNFNormalization.negative] using hc
        rcases List.mem_append.mp hmem with hψ | hχ
        · exact ihψ.2 c hψ
        · exact ihχ.2 c hχ
  | box i ψ ih =>
      cases i
      constructor
      · intro c hc
        have heq : c = DNFNormalization.boxClause ψ := by
          simpa [DNFNormalization.positive] using hc
        subst c
        exact LiteralConjunction.verum
      · intro c hc
        have heq : c = DNFNormalization.notBoxClause ψ := by
          simpa [DNFNormalization.negative] using hc
        subst c
        exact LiteralConjunction.verum

/-- The constructed K-DNF of every formula really has the paper's literal
syntax, as well as the semantic equivalence proved in `DNFNormalization`. -/
theorem k_dnf_exists (φ : Formula Atom Unit) :
    ∃ cs : List (DNF.Clause Atom Unit), IsKDNF cs ∧
      ∀ {World : Type u} (M : Model World Atom Unit) (x : World),
        M.Satisfies x φ ↔ DNF.Holds cs M x () := by
  exact ⟨DNFNormalization.positive φ, (k_normalizers_literal φ).1,
    fun M x => DNFNormalization.positive_equivalent φ M x⟩

/-! ## Propositional conjunctive normal forms for K45 box scopes -/

/-- Conjunction of a finite list of propositional clauses. -/
def HoldsCNF {World : Type u} (M : Model World Atom Unit) (x : World)
    (cs : List (Formula Atom Unit)) : Prop :=
  ∀ β ∈ cs, M.Satisfies x β

/-- Distribution of disjunction over two finite conjunctions. -/
def disjoinCNF (xs ys : List (Formula Atom Unit)) :
    List (Formula Atom Unit) :=
  xs.flatMap (fun α => ys.map (Formula.or α))

omit [Inhabited Atom] in theorem holds_disjoinCNF {World : Type u}
    (M : Model World Atom Unit) (x : World)
    (xs ys : List (Formula Atom Unit)) :
    HoldsCNF M x (disjoinCNF xs ys) ↔
      HoldsCNF M x xs ∨ HoldsCNF M x ys := by
  classical
  simp only [HoldsCNF, disjoinCNF, List.mem_flatMap, List.mem_map]
  constructor
  · intro h
    by_cases hxs : ∀ α ∈ xs, M.Satisfies x α
    · exact Or.inl hxs
    · right
      intro β hβ
      by_contra hnβ
      obtain ⟨α, hαbad⟩ := not_forall.mp hxs
      have hα : α ∈ xs := by
        by_contra hnot
        exact hαbad (fun hmem => (hnot hmem).elim)
      have hαfalse : ¬ M.Satisfies x α := by
        intro htrue
        exact hαbad (fun _ => htrue)
      have hor := h (Formula.or α β)
        ⟨α, hα, β, hβ, rfl⟩
      rcases (M.satisfies_or x α β).mp hor with ha | hb
      · exact hαfalse ha
      · exact hnβ hb
  · intro h β hβ
    obtain ⟨α, hα, γ, hγ, rfl⟩ := hβ
    apply (M.satisfies_or x α γ).mpr
    rcases h with hxs | hys
    · exact Or.inl (hxs α hα)
    · exact Or.inr (hys γ hγ)

private theorem disjoinCNF_literal (xs ys : List (Formula Atom Unit))
    (hx : ∀ α ∈ xs, LiteralDisjunction α)
    (hy : ∀ β ∈ ys, LiteralDisjunction β) :
    ∀ δ ∈ disjoinCNF xs ys, LiteralDisjunction δ := by
  intro δ hδ
  change δ ∈ xs.flatMap (fun α => ys.map (Formula.or α)) at hδ
  obtain ⟨α, hα, hmap⟩ := List.mem_flatMap.mp hδ
  obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp hmap
  exact LiteralDisjunction.disj (hx α hα) (hy β hβ)

mutual

/-- A propositional CNF equivalent to a formula, when the formula has no
single-agent modal operator. -/
def positiveCNF : Formula Atom Unit → List (Formula Atom Unit)
  | .atom p => [.atom p]
  | .neg φ => negativeCNF φ
  | .conj φ ψ => positiveCNF φ ++ positiveCNF ψ
  | .box _ _ => []

/-- A propositional CNF equivalent to the negation of a formula. -/
def negativeCNF : Formula Atom Unit → List (Formula Atom Unit)
  | .atom p => [.neg (.atom p)]
  | .neg φ => positiveCNF φ
  | .conj φ ψ => disjoinCNF (negativeCNF φ) (negativeCNF ψ)
  | .box _ _ => []

end

theorem cnf_outputs_literal (φ : Formula Atom Unit) :
    (∀ β ∈ positiveCNF φ, LiteralDisjunction β) ∧
    (∀ β ∈ negativeCNF φ, LiteralDisjunction β) := by
  induction φ with
  | atom p =>
      constructor
      · intro β hβ
        have h : β = .atom p := by simpa [positiveCNF] using hβ
        subst β
        exact LiteralDisjunction.pos p
      · intro β hβ
        have h : β = .neg (.atom p) := by simpa [negativeCNF] using hβ
        subst β
        exact LiteralDisjunction.neg p
  | neg ψ ih =>
      simpa [positiveCNF, negativeCNF] using And.symm ih
  | conj ψ χ ihψ ihχ =>
      constructor
      · intro β hβ
        have hmem : β ∈ positiveCNF ψ ++ positiveCNF χ := by
          simpa [positiveCNF] using hβ
        rcases List.mem_append.mp hmem with hψ | hχ
        · exact ihψ.1 β hψ
        · exact ihχ.1 β hχ
      · simpa [negativeCNF] using
          disjoinCNF_literal (negativeCNF ψ) (negativeCNF χ)
            ihψ.2 ihχ.2
  | box i ψ ih =>
      constructor <;> intro β hβ <;> simp [positiveCNF, negativeCNF] at hβ

/- The CNF converter is semantically correct on the agent-objective formulas
that can occur as box scopes in the single-agent K45 normalizer. -/
omit [Inhabited Atom] in theorem cnf_correct (φ : Formula Atom Unit) :
    (AgentDNF.Objective () φ →
      ∀ {World : Type u} (M : Model World Atom Unit) (x : World),
        HoldsCNF M x (positiveCNF φ) ↔ M.Satisfies x φ) ∧
    (AgentDNF.Objective () φ →
      ∀ {World : Type u} (M : Model World Atom Unit) (x : World),
        HoldsCNF M x (negativeCNF φ) ↔ ¬ M.Satisfies x φ) := by
  classical
  induction φ with
  | atom p =>
      constructor
      · intro _ World M x
        simp [HoldsCNF, positiveCNF]
      · intro _ World M x
        simp [HoldsCNF, negativeCNF]
  | neg ψ ih =>
      constructor
      · intro h World M x
        simpa [positiveCNF, Model.Satisfies] using ih.2 h M x
      · intro h World M x
        simpa [negativeCNF, Model.Satisfies] using ih.1 h M x
  | conj ψ χ ihψ ihχ =>
      constructor
      · intro h World M x
        change HoldsCNF M x (positiveCNF ψ ++ positiveCNF χ) ↔ _
        simp only [HoldsCNF, List.mem_append]
        constructor
        · intro hh
          exact ⟨(ihψ.1 h.1 M x).1 (fun β hβ => hh β (Or.inl hβ)),
            (ihχ.1 h.2 M x).1 (fun β hβ => hh β (Or.inr hβ))⟩
        · rintro ⟨hψ, hχ⟩ β hβ
          rcases hβ with hβ | hβ
          · exact (ihψ.1 h.1 M x).2 hψ β hβ
          · exact (ihχ.1 h.2 M x).2 hχ β hβ
      · intro h World M x
        rw [negativeCNF, holds_disjoinCNF,
          ihψ.2 h.1 M x, ihχ.2 h.2 M x]
        change (¬ M.Satisfies x ψ ∨ ¬ M.Satisfies x χ) ↔
          ¬ (M.Satisfies x ψ ∧ M.Satisfies x χ)
        tauto
  | box i ψ ih =>
      cases i
      have hImpossible : ¬ AgentDNF.Objective () (.box () ψ) := by
        intro h
        exact h rfl
      exact ⟨fun h => (hImpossible h).elim,
        fun h => (hImpossible h).elim⟩

/- A box of an objective propositional formula is equivalent to the boxes
of all clauses of its CNF. -/
omit [Inhabited Atom] in theorem box_positiveCNF_iff {World : Type u}
    (M : Model World Atom Unit) (x : World)
    (β : Formula Atom Unit) (hβ : AgentDNF.Objective () β) :
    M.Satisfies x (.box () β) ↔
      ∀ δ ∈ positiveCNF β, M.Satisfies x (.box () δ) := by
  constructor
  · intro h δ hδ y hxy
    exact ((cnf_correct β).1 hβ M y).2 (h y hxy) δ hδ
  · intro h y hxy
    exact ((cnf_correct β).1 hβ M y).1
      (fun δ hδ => h δ hδ y hxy)

/-! ## Refinement of the single-agent K45 normalizer -/

/-- Before CNF refinement, the existing normalizer already has literal
conjunctions as its alpha and diamond components. -/
def IsK45PreClause (c : AgentDNF.Clause Atom Unit) : Prop :=
  LiteralConjunction c.alpha ∧
    ∀ γ ∈ c.diamonds, LiteralConjunction γ

def IsK45PreDNF (cs : List (AgentDNF.Clause Atom Unit)) : Prop :=
  ∀ c ∈ cs, IsK45PreClause c

private theorem pre_join (c d : AgentDNF.Clause Atom Unit)
    (hc : IsK45PreClause c) (hd : IsK45PreClause d) :
    IsK45PreClause (AgentNormalization.join c d) := by
  constructor
  · exact LiteralConjunction.conj hc.1 hd.1
  · intro γ hγ
    rcases List.mem_append.mp hγ with hγ | hγ
    · exact hc.2 γ hγ
    · exact hd.2 γ hγ

private theorem pre_conjunction
    (xs ys : List (AgentDNF.Clause Atom Unit))
    (hx : IsK45PreDNF xs) (hy : IsK45PreDNF ys) :
    IsK45PreDNF (AgentNormalization.conjunction xs ys) := by
  intro e he
  change e ∈ xs.flatMap (fun c => ys.map (AgentNormalization.join c)) at he
  obtain ⟨c, hc, hmap⟩ := List.mem_flatMap.mp he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmap
  exact pre_join c d (hx c hc) (hy d hd)

private theorem pre_append (xs ys : List (AgentDNF.Clause Atom Unit))
    (hx : IsK45PreDNF xs) (hy : IsK45PreDNF ys) :
    IsK45PreDNF (xs ++ ys) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hx c hc
  · exact hy c hc

private theorem pre_boxLift
    (cs : List (AgentDNF.Clause Atom Unit)) (h : IsK45PreDNF cs) :
    IsK45PreDNF (AgentNormalization.boxLift cs) := by
  intro d hd
  obtain ⟨selected, hselected, rfl⟩ := List.mem_map.mp hd
  have hsub : List.Sublist selected cs := List.mem_sublists.mp hselected
  constructor
  · exact LiteralConjunction.verum
  · intro γ hγ
    obtain ⟨c, hc, hcγ⟩ := List.mem_flatMap.mp hγ
    exact (h c (hsub.subset hc)).2 γ hcγ

private theorem pre_diaLift
    (cs : List (AgentDNF.Clause Atom Unit)) (h : IsK45PreDNF cs) :
    IsK45PreDNF (AgentNormalization.diaLift cs) := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  constructor
  · exact LiteralConjunction.verum
  · intro γ hγ
    rcases List.mem_append.mp hγ with hγ | hγ
    · exact (h c hc).2 γ hγ
    · have heq : γ = c.alpha := by simpa using hγ
      subst γ
      exact (h c hc).1

theorem agent_normalizers_pre (φ : Formula Atom Unit) :
    IsK45PreDNF (AgentNormalization.positive () φ) ∧
      IsK45PreDNF (AgentNormalization.negative () φ) := by
  classical
  induction φ with
  | atom p =>
      constructor
      · intro c hc
        have heq : c = AgentNormalization.objectiveClause (.atom p) := by
          simpa [AgentNormalization.positive] using hc
        subst c
        exact ⟨LiteralConjunction.pos p, by simp [AgentNormalization.objectiveClause]⟩
      · intro c hc
        have heq : c = AgentNormalization.objectiveClause (.neg (.atom p)) := by
          simpa [AgentNormalization.negative] using hc
        subst c
        exact ⟨LiteralConjunction.neg p, by simp [AgentNormalization.objectiveClause]⟩
  | neg ψ ih =>
      simpa [AgentNormalization.positive, AgentNormalization.negative] using And.symm ih
  | conj ψ χ ihψ ihχ =>
      constructor
      · simpa [AgentNormalization.positive] using
          pre_conjunction (AgentNormalization.positive () ψ)
            (AgentNormalization.positive () χ) ihψ.1 ihχ.1
      · simpa [AgentNormalization.negative] using
          pre_append (AgentNormalization.negative () ψ)
            (AgentNormalization.negative () χ) ihψ.2 ihχ.2
  | box i ψ ih =>
      cases i
      constructor
      · simpa [AgentNormalization.positive] using
          pre_boxLift (AgentNormalization.positive () ψ) ih.1
      · simpa [AgentNormalization.negative] using
          pre_diaLift (AgentNormalization.negative () ψ) ih.2

/-- Replace each propositional box scope by the literal-disjunction clauses
of its CNF. The other clause components remain unchanged. -/
def refineBoxScopes (c : AgentDNF.Clause Atom Unit) :
    AgentDNF.Clause Atom Unit where
  alpha := c.alpha
  boxes := c.boxes.flatMap positiveCNF
  diamonds := c.diamonds

def refineDNF (cs : List (AgentDNF.Clause Atom Unit)) :
    List (AgentDNF.Clause Atom Unit) :=
  cs.map refineBoxScopes

theorem refineBoxScopes_isK45Clause (c : AgentDNF.Clause Atom Unit)
    (h : IsK45PreClause c) : IsK45Clause (refineBoxScopes c) := by
  constructor
  · exact h.1
  constructor
  · intro δ hδ
    obtain ⟨β, hβ, hδ⟩ := List.mem_flatMap.mp hδ
    exact (cnf_outputs_literal β).1 δ hδ
  · exact h.2

theorem refineDNF_isK45DNF (cs : List (AgentDNF.Clause Atom Unit))
    (h : IsK45PreDNF cs) : IsK45DNF (refineDNF cs) := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  exact refineBoxScopes_isK45Clause c (h c hc)

omit [Inhabited Atom] in theorem holds_refineBoxScopes {World : Type u}
    (M : Model World Atom Unit) (x : World)
    (c : AgentDNF.Clause Atom Unit)
    (hobj : ∀ β ∈ c.boxes, AgentDNF.Objective () β) :
    AgentDNF.Holds (refineBoxScopes c) M x () ↔
      AgentDNF.Holds c M x () := by
  constructor
  · rintro ⟨hα, hboxes, hdiamonds⟩
    refine ⟨hα, ?_, hdiamonds⟩
    intro β hβ
    apply (box_positiveCNF_iff M x β (hobj β hβ)).2
    intro δ hδ
    exact hboxes δ (List.mem_flatMap.mpr ⟨β, hβ, hδ⟩)
  · rintro ⟨hα, hboxes, hdiamonds⟩
    refine ⟨hα, ?_, hdiamonds⟩
    intro δ hδ
    obtain ⟨β, hβ, hδ⟩ := List.mem_flatMap.mp hδ
    exact (box_positiveCNF_iff M x β (hobj β hβ)).1
      (hboxes β hβ) δ hδ

omit [Inhabited Atom] in theorem holds_refineDNF {World : Type u}
    (M : Model World Atom Unit) (x : World)
    (cs : List (AgentDNF.Clause Atom Unit))
    (h : AgentDNF.IsIDNF () cs) :
    AgentDNF.HoldsDNF (refineDNF cs) M x () ↔
      AgentDNF.HoldsDNF cs M x () := by
  constructor
  · rintro ⟨d, hd, hholds⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    exact ⟨c, hc,
      (holds_refineBoxScopes M x c (h c hc).2.1).1 hholds⟩
  · rintro ⟨c, hc, hholds⟩
    exact ⟨refineBoxScopes c, List.mem_map.mpr ⟨c, hc, rfl⟩,
      (holds_refineBoxScopes M x c (h c hc).2.1).2 hholds⟩

theorem literalConjunction_objective {φ : Formula Atom Unit}
    (h : LiteralConjunction φ) : AgentDNF.Objective () φ := by
  induction h with
  | verum => exact AgentNormalization.objective_verum ()
  | pos p => trivial
  | neg p => trivial
  | conj hφ hψ ihφ ihψ => exact ⟨ihφ, ihψ⟩

theorem literalDisjunction_objective {φ : Formula Atom Unit}
    (h : LiteralDisjunction φ) : AgentDNF.Objective () φ := by
  induction h with
  | falsum => exact AgentNormalization.objective_falsum ()
  | pos p => trivial
  | neg p => trivial
  | disj hφ hψ ihφ ihψ =>
      exact AgentNormalization.objective_or () _ _ ihφ ihψ

theorem isK45DNF_isIDNF (cs : List (AgentDNF.Clause Atom Unit))
    (h : IsK45DNF cs) : AgentDNF.IsIDNF () cs := by
  intro c hc
  obtain ⟨hα, hboxes, hdiamonds⟩ := h c hc
  exact ⟨literalConjunction_objective hα,
    fun β hβ => literalDisjunction_objective (hboxes β hβ),
    fun γ hγ => literalConjunction_objective (hdiamonds γ hγ)⟩

/-- The paper's Definition 5 normal form, constructed for every formula.
Every box scope is literally a disjunction of literals, and the normal form
is equivalent to the input on all K45 frames. -/
noncomputable def strictK45DNF (φ : Formula Atom Unit) :
    List (AgentDNF.Clause Atom Unit) := by
  classical
  exact refineDNF (AgentNormalization.positive () φ)

theorem strictK45DNF_grammar (φ : Formula Atom Unit) :
    IsK45DNF (strictK45DNF φ) := by
  classical
  exact refineDNF_isK45DNF _ (agent_normalizers_pre φ).1

theorem strictK45DNF_isIDNF (φ : Formula Atom Unit) :
    AgentDNF.IsIDNF () (strictK45DNF φ) :=
  isK45DNF_isIDNF _ (strictK45DNF_grammar φ)

theorem strictK45DNF_equivalent (φ : Formula Atom Unit)
    {World : Type u} (M : Model World Atom Unit)
    (hM : IsK45 M) (x : World) :
    M.Satisfies x φ ↔
      AgentDNF.HoldsDNF (strictK45DNF φ) M x () := by
  classical
  have hnormal := (AgentNormalization.normalizers_correct () φ).1 M hM x
  exact hnormal.symm.trans
    (holds_refineDNF M x (AgentNormalization.positive () φ)
      (AgentNormalization.normalizers_are_iDNF () φ).1).symm

theorem strict_k45_dnf_exists (φ : Formula Atom Unit) :
    ∃ cs : List (AgentDNF.Clause Atom Unit),
      IsK45DNF cs ∧ AgentDNF.IsIDNF () cs ∧
      ∀ {World : Type u} (M : Model World Atom Unit), IsK45 M →
        ∀ x : World, M.Satisfies x φ ↔ AgentDNF.HoldsDNF cs M x () := by
  exact ⟨strictK45DNF φ, strictK45DNF_grammar φ,
    strictK45DNF_isIDNF φ,
    fun M hM x => strictK45DNF_equivalent φ M hM x⟩

end SourcesOfUnknowability.LiteralNormalForms
