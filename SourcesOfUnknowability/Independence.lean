import SourcesOfUnknowability.Static

/-!
# Formulas independent of one agent

Definition 13's `i`-independent formulas and the semantic invariance used in
Lemma 8. We also construct the S5 cluster that witnesses the constructive half
of Lemma 8 when the required pointed witnesses live in a common model.
-/

namespace SourcesOfUnknowability
namespace Independence

open ClassificationSigmaValidity

universe u v t

variable {World : Type u} {Atom : Type v} {Agent : Type t}

/-- A formula has no modal operator for agent `i` anywhere in its syntax. -/
def Independent (i : Agent) : Formula Atom Agent → Prop
  | .atom _ => True
  | .neg φ => Independent i φ
  | .conj φ ψ => Independent i φ ∧ Independent i ψ
  | .box j φ => j ≠ i ∧ Independent i φ

@[simp] theorem independent_atom (i : Agent) (p : Atom) :
    Independent i (.atom p) := trivial

@[simp] theorem independent_neg (i : Agent) (φ : Formula Atom Agent) :
    Independent i (.neg φ) ↔ Independent i φ := Iff.rfl

@[simp] theorem independent_conj (i : Agent) (φ ψ : Formula Atom Agent) :
    Independent i (.conj φ ψ) ↔
      Independent i φ ∧ Independent i ψ := Iff.rfl

@[simp] theorem independent_box (i j : Agent) (φ : Formula Atom Agent) :
    Independent i (.box j φ) ↔ j ≠ i ∧ Independent i φ := Iff.rfl

@[simp] theorem independent_dia (i j : Agent) (φ : Formula Atom Agent) :
    Independent i (Formula.dia j φ) ↔ j ≠ i ∧ Independent i φ := by
  simp [Formula.dia, Independent]

/-- Truth of an `i`-independent formula is unaffected by a change to agent
`i`'s relation, provided valuations and all other relations agree. -/
theorem satisfies_iff_of_independent (M N : Model World Atom Agent)
    (i : Agent)
    (hval : ∀ p x, M.val p x ↔ N.val p x)
    (hother : ∀ j, j ≠ i → ∀ x y, M.rel j x y ↔ N.rel j x y)
    (φ : Formula Atom Agent) (hφ : Independent i φ) (x : World) :
    M.Satisfies x φ ↔ N.Satisfies x φ := by
  induction φ generalizing x with
  | atom p => exact hval p x
  | neg ψ ih => exact not_congr (ih hφ x)
  | conj ψ χ ihψ ihχ =>
      exact and_congr (ihψ hφ.1 x) (ihχ hφ.2 x)
  | box j ψ ih =>
      constructor
      · intro h y hNxy
        exact (ih hφ.2 y).mp (h y ((hother j hφ.1 x y).mpr hNxy))
      · intro h y hMxy
        exact (ih hφ.2 y).mpr (h y ((hother j hφ.1 x y).mp hMxy))

/-- Disjoint union of two Kripke models. -/
def sumModel {W₁ W₂ : Type u}
    (M : Model W₁ Atom Agent) (N : Model W₂ Atom Agent) :
    Model (Sum W₁ W₂) Atom Agent where
  rel i x y :=
    match x, y with
    | .inl a, .inl b => M.rel i a b
    | .inr a, .inr b => N.rel i a b
    | _, _ => False
  val p x :=
    match x with
    | .inl a => M.val p a
    | .inr b => N.val p b

theorem sumModel_left_truth {W₁ W₂ : Type u}
    (M : Model W₁ Atom Agent) (N : Model W₂ Atom Agent)
    (φ : Formula Atom Agent) :
    ∀ x : W₁, (sumModel M N).Satisfies (.inl x) φ ↔ M.Satisfies x φ := by
  induction φ with
  | atom p => intro x; rfl
  | neg ψ ih => intro x; exact not_congr (ih x)
  | conj ψ χ ihψ ihχ =>
      intro x
      exact and_congr (ihψ x) (ihχ x)
  | box i ψ ih =>
      intro x
      constructor
      · intro h y hxy
        exact (ih y).mp (h (.inl y) hxy)
      · intro h y hxy
        cases y with
        | inl y => exact (ih y).mpr (h y hxy)
        | inr y => exact False.elim hxy

theorem sumModel_right_truth {W₁ W₂ : Type u}
    (M : Model W₁ Atom Agent) (N : Model W₂ Atom Agent)
    (φ : Formula Atom Agent) :
    ∀ x : W₂, (sumModel M N).Satisfies (.inr x) φ ↔ N.Satisfies x φ := by
  induction φ with
  | atom p => intro x; rfl
  | neg ψ ih => intro x; exact not_congr (ih x)
  | conj ψ χ ihψ ihχ =>
      intro x
      exact and_congr (ihψ x) (ihχ x)
  | box i ψ ih =>
      intro x
      constructor
      · intro h y hxy
        exact (ih y).mp (h (.inr y) hxy)
      · intro h y hxy
        cases y with
        | inl y => exact False.elim hxy
        | inr y => exact (ih y).mpr (h y hxy)

theorem sumModel_isK45 {W₁ W₂ : Type u}
    (M : Model W₁ Atom Agent) (N : Model W₂ Atom Agent)
    (hM : IsK45 M) (hN : IsK45 N) : IsK45 (sumModel M N) := by
  intro i
  constructor
  · intro x y z hxy hyz
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            cases z with
            | inl z => exact (hM i).1 hxy hyz
            | inr z => exact False.elim hyz
        | inr y => exact False.elim hxy
    | inr x =>
        cases y with
        | inl y => exact False.elim hxy
        | inr y =>
            cases z with
            | inl z => exact False.elim hyz
            | inr z => exact (hN i).1 hxy hyz
  · intro x y z hxy hxz
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            cases z with
            | inl z => exact (hM i).2 hxy hxz
            | inr z => exact False.elim hxz
        | inr y => exact False.elim hxy
    | inr x =>
        cases y with
        | inl y => exact False.elim hxy
        | inr y =>
            cases z with
            | inl z => exact False.elim hxz
            | inr z => exact (hN i).2 hxy hxz

theorem sumModel_isKD45 {W₁ W₂ : Type u}
    (M : Model W₁ Atom Agent) (N : Model W₂ Atom Agent)
    (hM : IsKD45 M) (hN : IsKD45 N) : IsKD45 (sumModel M N) := by
  intro i
  have hK : IsK45 (sumModel M N) :=
    sumModel_isK45 M N hM.isK45 hN.isK45
  refine ⟨?_, (hK i).1, (hK i).2⟩
  intro x
  cases x with
  | inl x =>
      obtain ⟨y, hxy⟩ := (hM i).1 x
      exact ⟨.inl y, hxy⟩
  | inr x =>
      obtain ⟨y, hxy⟩ := (hN i).1 x
      exact ⟨.inr y, hxy⟩

theorem sumModel_isS5 {W₁ W₂ : Type u}
    (M : Model W₁ Atom Agent) (N : Model W₂ Atom Agent)
    (hM : IsS5 M) (hN : IsS5 N) : IsS5 (sumModel M N) := by
  intro i
  have hK : IsK45 (sumModel M N) :=
    sumModel_isK45 M N hM.isK45 hN.isK45
  refine ⟨?_, (hK i).1, (hK i).2⟩
  intro x
  cases x with
  | inl x => exact (hM i).1 x
  | inr x => exact (hN i).1 x

/-- Finitely many separate satisfiability witnesses can be placed in one
disjoint-union model whenever the frame class is closed under sums. -/
theorem common_model_of_satisfiable
    (C : FrameClass.{u} Atom Agent)
    (hsum : ∀ {W₁ W₂ : Type u} (M : Model W₁ Atom Agent)
      (N : Model W₂ Atom Agent), C M → C N → C (sumModel M N))
    (β : Formula Atom Agent) (Γ : List (Formula Atom Agent))
    (hβ : Static.Satisfiable C β)
    (hΓ : ∀ γ ∈ Γ, Static.Satisfiable C (.conj β γ)) :
    ∃ (W : Type u) (M : Model W Atom Agent), C M ∧
      ∃ s : W, M.Satisfies s β ∧
        ∀ γ ∈ Γ, ∃ y : W, M.Satisfies y β ∧ M.Satisfies y γ := by
  revert hΓ
  induction Γ with
  | nil =>
      intro _
      obtain ⟨W, M, hM, s, hs⟩ := hβ
      exact ⟨W, M, hM, s, hs, by simp⟩
  | cons γ tail ih =>
      intro hΓ
      have htail : ∀ δ ∈ tail, Static.Satisfiable C (.conj β δ) := by
        intro δ hδ
        exact hΓ δ (by simp [hδ])
      obtain ⟨W₁, M, hM, s, hs, hrest⟩ := ih htail
      obtain ⟨W₂, N, hN, t, ht⟩ := hΓ γ (by simp)
      refine ⟨Sum W₁ W₂, sumModel M N, hsum M N hM hN,
        .inl s, (sumModel_left_truth M N β s).mpr hs, ?_⟩
      intro δ hδ
      rcases List.mem_cons.mp hδ with rfl | hδ
      · exact ⟨.inr t,
          (sumModel_right_truth M N β t).mpr ht.1,
          (sumModel_right_truth M N δ t).mpr ht.2⟩
      · obtain ⟨y, hyβ, hyδ⟩ := hrest δ hδ
        exact ⟨.inl y,
          (sumModel_left_truth M N β y).mpr hyβ,
          (sumModel_left_truth M N δ y).mpr hyδ⟩

/-- Complete relation on `S` and identity outside `S`. It is an equivalence
relation, with no finiteness requirement on the world type. -/
def clusterRel (S : Set World) (x y : World) : Prop :=
  (x ∈ S ∧ y ∈ S) ∨ (x ∉ S ∧ x = y)

theorem clusterRel_reflexive (S : Set World) :
    Frame.Reflexive (clusterRel S) := by
  intro x
  by_cases hx : x ∈ S
  · exact Or.inl ⟨hx, hx⟩
  · exact Or.inr ⟨hx, rfl⟩

theorem clusterRel_transitive (S : Set World) :
    Frame.Transitive (clusterRel S) := by
  intro x y z hxy hyz
  rcases hxy with ⟨hx, hy⟩ | ⟨hx, hxy⟩
  · rcases hyz with ⟨_, hz⟩ | ⟨hny, heq⟩
    · exact Or.inl ⟨hx, hz⟩
    · exact (hny hy).elim
  · subst y
    exact hyz

theorem clusterRel_euclidean (S : Set World) :
    Frame.Euclidean (clusterRel S) := by
  intro x y z hxy hxz
  rcases hxy with ⟨hx, hy⟩ | ⟨hnx, hxy⟩
  · rcases hxz with ⟨_, hz⟩ | ⟨hnx, _⟩
    · exact Or.inl ⟨hy, hz⟩
    · exact (hnx hx).elim
  · subst y
    rcases hxz with ⟨hx, _⟩ | ⟨_, hxz⟩
    · exact (hnx hx).elim
    · subst z
      exact Or.inr ⟨hnx, rfl⟩

/-- Replace one agent's relation with the S5 cluster relation. -/
def replaceRelation (M : Model World Atom Agent) (i : Agent) (S : Set World) :
    Model World Atom Agent where
  rel j x y :=
    (j = i ∧ clusterRel S x y) ∨ (j ≠ i ∧ M.rel j x y)
  val := M.val

theorem replaceRelation_rel_self (M : Model World Atom Agent)
    (i : Agent) (S : Set World) (x y : World) :
    (replaceRelation M i S).rel i x y ↔ clusterRel S x y := by
  simp [replaceRelation]

theorem replaceRelation_rel_other (M : Model World Atom Agent)
    (i j : Agent) (hji : j ≠ i) (S : Set World) (x y : World) :
    (replaceRelation M i S).rel j x y ↔ M.rel j x y := by
  simp [replaceRelation, hji]

theorem replaceRelation_satisfies_independent (M : Model World Atom Agent)
    (i : Agent) (S : Set World) (φ : Formula Atom Agent)
    (hφ : Independent i φ) (x : World) :
    (replaceRelation M i S).Satisfies x φ ↔ M.Satisfies x φ := by
  symm
  exact satisfies_iff_of_independent M (replaceRelation M i S) i
    (fun _ _ => Iff.rfl)
    (fun j hji x y => (replaceRelation_rel_other M i j hji S x y).symm)
    φ hφ x

theorem replaceRelation_isKD45 (M : Model World Atom Agent)
    (hM : IsKD45 M) (i : Agent) (S : Set World) :
    IsKD45 (replaceRelation M i S) := by
  intro j
  by_cases hji : j = i
  · subst j
    constructor
    · intro x
      exact ⟨x, (replaceRelation_rel_self M i S x x).mpr
        (clusterRel_reflexive S x)⟩
    constructor
    · intro x y z hxy hyz
      exact (replaceRelation_rel_self M i S x z).mpr
        (clusterRel_transitive S
          ((replaceRelation_rel_self M i S x y).mp hxy)
          ((replaceRelation_rel_self M i S y z).mp hyz))
    · intro x y z hxy hxz
      exact (replaceRelation_rel_self M i S y z).mpr
        (clusterRel_euclidean S
          ((replaceRelation_rel_self M i S x y).mp hxy)
          ((replaceRelation_rel_self M i S x z).mp hxz))
  · constructor
    · intro x
      obtain ⟨y, hxy⟩ := (hM j).1 x
      exact ⟨y, (replaceRelation_rel_other M i j hji S x y).mpr hxy⟩
    constructor
    · intro x y z hxy hyz
      exact (replaceRelation_rel_other M i j hji S x z).mpr
        ((hM j).2.1
          ((replaceRelation_rel_other M i j hji S x y).mp hxy)
          ((replaceRelation_rel_other M i j hji S y z).mp hyz))
    · intro x y z hxy hxz
      exact (replaceRelation_rel_other M i j hji S y z).mpr
        ((hM j).2.2
          ((replaceRelation_rel_other M i j hji S x y).mp hxy)
          ((replaceRelation_rel_other M i j hji S x z).mp hxz))

theorem replaceRelation_isS5 (M : Model World Atom Agent)
    (hM : IsS5 M) (i : Agent) (S : Set World) :
    IsS5 (replaceRelation M i S) := by
  intro j
  by_cases hji : j = i
  · subst j
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (replaceRelation_rel_self M i S x x).mpr
        (clusterRel_reflexive S x)
    · intro x y z hxy hyz
      exact (replaceRelation_rel_self M i S x z).mpr
        (clusterRel_transitive S
          ((replaceRelation_rel_self M i S x y).mp hxy)
          ((replaceRelation_rel_self M i S y z).mp hyz))
    · intro x y z hxy hxz
      exact (replaceRelation_rel_self M i S y z).mpr
        (clusterRel_euclidean S
          ((replaceRelation_rel_self M i S x y).mp hxy)
          ((replaceRelation_rel_self M i S x z).mp hxz))
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (replaceRelation_rel_other M i j hji S x x).mpr
        ((hM j).1 x)
    · intro x y z hxy hyz
      exact (replaceRelation_rel_other M i j hji S x z).mpr
        ((hM j).2.1
          ((replaceRelation_rel_other M i j hji S x y).mp hxy)
          ((replaceRelation_rel_other M i j hji S y z).mp hyz))
    · intro x y z hxy hxz
      exact (replaceRelation_rel_other M i j hji S y z).mpr
        ((hM j).2.2
          ((replaceRelation_rel_other M i j hji S x y).mp hxy)
          ((replaceRelation_rel_other M i j hji S x z).mp hxz))

/-- Construct the root cluster for Lemma 8 when all propositional witnesses
are points of one model. The truth of independent formulas survives the
replacement of the distinguished agent's relation. -/
theorem box_diamonds_of_common_model (M : Model World Atom Agent)
    (i : Agent) (β : Formula Atom Agent)
    (Γ : List (Formula Atom Agent))
    (hβ : Independent i β)
    (hΓ : ∀ γ ∈ Γ, Independent i γ)
    (s : World) (hs : M.Satisfies s β)
    (hcompat : ∀ γ ∈ Γ, ∃ y, M.Satisfies y β ∧ M.Satisfies y γ) :
    ∃ S : Set World, s ∈ S ∧
      (replaceRelation M i S).Satisfies s (.box i β) ∧
      ∀ γ ∈ Γ, (replaceRelation M i S).Satisfies s (Formula.dia i γ) := by
  classical
  let pick (γ : Formula Atom Agent) (hγ : γ ∈ Γ) : World :=
    Classical.choose (hcompat γ hγ)
  let S : Set World :=
    {y | y = s ∨ ∃ γ, ∃ hγ : γ ∈ Γ, y = pick γ hγ}
  have hsS : s ∈ S := Or.inl rfl
  have hβS : ∀ y ∈ S, M.Satisfies y β := by
    intro y hy
    rcases hy with rfl | ⟨γ, hγ, rfl⟩
    · exact hs
    · exact (Classical.choose_spec (hcompat γ hγ)).1
  refine ⟨S, hsS, ?_, ?_⟩
  · intro y hsy
    have hyS : y ∈ S := by
      rcases (replaceRelation_rel_self M i S s y).mp hsy with h | h
      · exact h.2
      · exact (h.1 hsS).elim
    exact (replaceRelation_satisfies_independent M i S β hβ y).mpr
      (hβS y hyS)
  · intro γ hγ
    apply ((replaceRelation M i S).satisfies_dia s i γ).mpr
    refine ⟨pick γ hγ, ?_, ?_⟩
    · apply (replaceRelation_rel_self M i S s (pick γ hγ)).mpr
      apply Or.inl
      exact ⟨hsS, Or.inr ⟨γ, hγ, rfl⟩⟩
    · exact (replaceRelation_satisfies_independent M i S γ
        (hΓ γ hγ) (pick γ hγ)).mpr
        (Classical.choose_spec (hcompat γ hγ)).2

/-- The common-model construction yields a KD45 witness. -/
theorem box_diamonds_satisfiable_kd45_of_common_model
    (M : Model World Atom Agent) (hM : IsKD45 M)
    (i : Agent) (β : Formula Atom Agent) (Γ : List (Formula Atom Agent))
    (hβ : Independent i β) (hΓ : ∀ γ ∈ Γ, Independent i γ)
    (s : World) (hs : M.Satisfies s β)
    (hcompat : ∀ γ ∈ Γ, ∃ y, M.Satisfies y β ∧ M.Satisfies y γ) :
    ∃ (N : Model World Atom Agent) (x : World),
      IsKD45 N ∧ N.Satisfies x (.box i β) ∧
      ∀ γ ∈ Γ, N.Satisfies x (Formula.dia i γ) := by
  obtain ⟨S, _, hbox, hdiamonds⟩ :=
    box_diamonds_of_common_model M i β Γ hβ hΓ s hs hcompat
  exact ⟨replaceRelation M i S, s,
    replaceRelation_isKD45 M hM i S, hbox, hdiamonds⟩

/-- The same construction yields an S5 witness from an S5 common model. -/
theorem box_diamonds_satisfiable_s5_of_common_model
    (M : Model World Atom Agent) (hM : IsS5 M)
    (i : Agent) (β : Formula Atom Agent) (Γ : List (Formula Atom Agent))
    (hβ : Independent i β) (hΓ : ∀ γ ∈ Γ, Independent i γ)
    (s : World) (hs : M.Satisfies s β)
    (hcompat : ∀ γ ∈ Γ, ∃ y, M.Satisfies y β ∧ M.Satisfies y γ) :
    ∃ (N : Model World Atom Agent) (x : World),
      IsS5 N ∧ N.Satisfies x (.box i β) ∧
      ∀ γ ∈ Γ, N.Satisfies x (Formula.dia i γ) := by
  obtain ⟨S, _, hbox, hdiamonds⟩ :=
    box_diamonds_of_common_model M i β Γ hβ hΓ s hs hcompat
  exact ⟨replaceRelation M i S, s,
    replaceRelation_isS5 M hM i S, hbox, hdiamonds⟩

/-- Necessary half of Lemma 8 in KD45. It does not need independence: a
serial successor witnesses `β`, while each diamond witnesses `β ∧ γ`. -/
theorem box_diamonds_necessary_kd45 (i : Agent)
    (β : Formula Atom Agent) (Γ : List (Formula Atom Agent))
    (h : ∃ (W : Type u) (M : Model W Atom Agent) (x : W),
      IsKD45 M ∧ M.Satisfies x (.box i β) ∧
      ∀ γ ∈ Γ, M.Satisfies x (Formula.dia i γ)) :
    Static.Satisfiable (Static.Classes.KD45 : FrameClass.{u} Atom Agent) β ∧
      ∀ γ ∈ Γ,
        Static.Satisfiable (Static.Classes.KD45 : FrameClass.{u} Atom Agent)
          (.conj β γ) := by
  obtain ⟨W, M, x, hM, hbox, hdiamonds⟩ := h
  constructor
  · obtain ⟨y, hxy⟩ := (hM i).1 x
    exact ⟨W, M, hM, y, hbox y hxy⟩
  · intro γ hγ
    obtain ⟨y, hxy, hyγ⟩ :=
      (M.satisfies_dia x i γ).mp (hdiamonds γ hγ)
    exact ⟨W, M, hM, y, ⟨hbox y hxy, hyγ⟩⟩

/-- Necessary half of Lemma 8 in S5. -/
theorem box_diamonds_necessary_s5 (i : Agent)
    (β : Formula Atom Agent) (Γ : List (Formula Atom Agent))
    (h : ∃ (W : Type u) (M : Model W Atom Agent) (x : W),
      IsS5 M ∧ M.Satisfies x (.box i β) ∧
      ∀ γ ∈ Γ, M.Satisfies x (Formula.dia i γ)) :
    Static.Satisfiable (Static.Classes.S5 : FrameClass.{u} Atom Agent) β ∧
      ∀ γ ∈ Γ,
        Static.Satisfiable (Static.Classes.S5 : FrameClass.{u} Atom Agent)
          (.conj β γ) := by
  obtain ⟨W, M, x, hM, hbox, hdiamonds⟩ := h
  constructor
  · exact ⟨W, M, hM, x, hbox x ((hM i).1 x)⟩
  · intro γ hγ
    obtain ⟨y, hxy, hyγ⟩ :=
      (M.satisfies_dia x i γ).mp (hdiamonds γ hγ)
    exact ⟨W, M, hM, y, ⟨hbox y hxy, hyγ⟩⟩

/-- Lemma 8 for KD45, with the finite conjunction of diamonds expressed as
a list of semantic requirements. -/
theorem lemma8_kd45 (i : Agent) (β : Formula Atom Agent)
    (Γ : List (Formula Atom Agent))
    (hβ : Independent i β)
    (hΓ : ∀ γ ∈ Γ, Independent i γ) :
    (∃ (W : Type u) (M : Model W Atom Agent) (x : W),
      IsKD45 M ∧ M.Satisfies x (.box i β) ∧
      ∀ γ ∈ Γ, M.Satisfies x (Formula.dia i γ)) ↔
    Static.Satisfiable (Static.Classes.KD45 : FrameClass.{u} Atom Agent) β ∧
      (∀ γ ∈ Γ,
        Static.Satisfiable (Static.Classes.KD45 : FrameClass.{u} Atom Agent)
          (.conj β γ)) := by
  constructor
  · exact box_diamonds_necessary_kd45 i β Γ
  · rintro ⟨hsβ, hsΓ⟩
    obtain ⟨W, M, hM, s, hs, hcompat⟩ :=
      common_model_of_satisfiable
        (Static.Classes.KD45 : FrameClass.{u} Atom Agent)
        (fun M N hM hN => sumModel_isKD45 M N hM hN)
        β Γ hsβ hsΓ
    obtain ⟨N, x, hN, hbox, hdia⟩ :=
      box_diamonds_satisfiable_kd45_of_common_model
        M hM i β Γ hβ hΓ s hs hcompat
    exact ⟨W, N, x, hN, hbox, hdia⟩

/-- Lemma 8 for S5. The same disjoint-union and cluster construction works
because it makes the distinguished agent's relation an equivalence relation. -/
theorem lemma8_s5 (i : Agent) (β : Formula Atom Agent)
    (Γ : List (Formula Atom Agent))
    (hβ : Independent i β)
    (hΓ : ∀ γ ∈ Γ, Independent i γ) :
    (∃ (W : Type u) (M : Model W Atom Agent) (x : W),
      IsS5 M ∧ M.Satisfies x (.box i β) ∧
      ∀ γ ∈ Γ, M.Satisfies x (Formula.dia i γ)) ↔
    Static.Satisfiable (Static.Classes.S5 : FrameClass.{u} Atom Agent) β ∧
      (∀ γ ∈ Γ,
        Static.Satisfiable (Static.Classes.S5 : FrameClass.{u} Atom Agent)
          (.conj β γ)) := by
  constructor
  · exact box_diamonds_necessary_s5 i β Γ
  · rintro ⟨hsβ, hsΓ⟩
    obtain ⟨W, M, hM, s, hs, hcompat⟩ :=
      common_model_of_satisfiable
        (Static.Classes.S5 : FrameClass.{u} Atom Agent)
        (fun M N hM hN => sumModel_isS5 M N hM hN)
        β Γ hsβ hsΓ
    obtain ⟨N, x, hN, hbox, hdia⟩ :=
      box_diamonds_satisfiable_s5_of_common_model
        M hM i β Γ hβ hΓ s hs hcompat
    exact ⟨W, N, x, hN, hbox, hdia⟩

/-- A propositional formula contains no agent's modal operator. -/
theorem independent_of_modalDepth_zero (i : Agent)
    (φ : Formula Atom Agent) (hdepth : φ.modalDepth = 0) :
    Independent i φ := by
  induction φ with
  | atom p => trivial
  | neg ψ ih =>
      exact ih hdepth
  | conj ψ χ ihψ ihχ =>
      have hψ : ψ.modalDepth = 0 := by
        simp only [Formula.modalDepth] at hdepth
        omega
      have hχ : χ.modalDepth = 0 := by
        simp only [Formula.modalDepth] at hdepth
        omega
      exact ⟨ihψ hψ, ihχ hχ⟩
  | box j ψ =>
      simp [Formula.modalDepth] at hdepth

/-- Lemma 5, the single-agent propositional instance of Lemma 8 in KD45. -/
theorem lemma5_kd45 (β : Formula Atom Unit)
    (Γ : List (Formula Atom Unit))
    (hβ : β.modalDepth = 0)
    (hΓ : ∀ γ ∈ Γ, γ.modalDepth = 0) :
    (∃ (W : Type u) (M : Model W Atom Unit) (x : W),
      IsKD45 M ∧ M.Satisfies x (.box () β) ∧
      ∀ γ ∈ Γ, M.Satisfies x (Formula.dia () γ)) ↔
    Static.Satisfiable (Static.Classes.KD45 : FrameClass.{u} Atom Unit) β ∧
      (∀ γ ∈ Γ,
        Static.Satisfiable (Static.Classes.KD45 : FrameClass.{u} Atom Unit)
          (.conj β γ)) := by
  exact lemma8_kd45 () β Γ
    (independent_of_modalDepth_zero () β hβ)
    (fun γ hγ => independent_of_modalDepth_zero () γ (hΓ γ hγ))

/-- Lemma 5 in S5. -/
theorem lemma5_s5 (β : Formula Atom Unit)
    (Γ : List (Formula Atom Unit))
    (hβ : β.modalDepth = 0)
    (hΓ : ∀ γ ∈ Γ, γ.modalDepth = 0) :
    (∃ (W : Type u) (M : Model W Atom Unit) (x : W),
      IsS5 M ∧ M.Satisfies x (.box () β) ∧
      ∀ γ ∈ Γ, M.Satisfies x (Formula.dia () γ)) ↔
    Static.Satisfiable (Static.Classes.S5 : FrameClass.{u} Atom Unit) β ∧
      (∀ γ ∈ Γ,
        Static.Satisfiable (Static.Classes.S5 : FrameClass.{u} Atom Unit)
          (.conj β γ)) := by
  exact lemma8_s5 () β Γ
    (independent_of_modalDepth_zero () β hβ)
    (fun γ hγ => independent_of_modalDepth_zero () γ (hΓ γ hγ))

/-- Example 2's first formula, with two distinct agents. -/
def example2_first (p : Atom) : Formula Atom (Fin 2) :=
  .conj (.box 0 (.atom p)) (.box 1 (.neg (.atom p)))

/-- Agent 1 and agent 2 cannot both know contradictory propositional facts
at one S5 state. -/
theorem example2_first_unsatisfiable_s5 (p : Atom) :
    ¬ Static.Satisfiable
      (Static.Classes.S5 : FrameClass.{u} Atom (Fin 2))
      (example2_first p) := by
  rintro ⟨W, M, hM, x, h⟩
  have hp : M.Satisfies x (.atom p) := h.1 x ((hM 0).1 x)
  have hnp : ¬ M.Satisfies x (.atom p) := h.2 x ((hM 1).1 x)
  exact hnp hp

/-- Consequently the first formula of Example 2 is unbelievable to either
agent in S5. -/
theorem example2_first_unbelievable_s5 (p : Atom) (i : Fin 2) :
    Static.Unbelievable
      (Static.Classes.S5 : FrameClass.{u} Atom (Fin 2))
      i (example2_first p) := by
  rintro ⟨W, M, hM, x, hbox⟩
  exact example2_first_unsatisfiable_s5 p
    ⟨W, M, hM, x, hbox x ((hM i).1 x)⟩

/-- Example 2's second formula: agent 1 believes agent 2 considers `p`
possible, but `p` is false. -/
def example2_second (p : Atom) : Formula Atom (Fin 2) :=
  .conj (.box 0 (Formula.dia 1 (.atom p))) (.neg (.atom p))

/-- Example 2's third formula: agent 1 believes `p`, while agent 2
considers possible that agent 1 considers `¬p` possible. -/
def example2_third (p : Atom) : Formula Atom (Fin 2) :=
  .conj (.box 0 (.atom p))
    (Formula.dia 1 (Formula.dia 0 (.neg (.atom p))))

/-- The second formula is unbelievable to agent 2 in S5. -/
theorem example2_second_unbelievable_to_two_s5 (p : Atom) :
    Static.Unbelievable
      (Static.Classes.S5 : FrameClass.{u} Atom (Fin 2))
      1 (example2_second p) := by
  rintro ⟨W, M, hM, x, hbel⟩
  have hψx := hbel x ((hM 1).1 x)
  have hdia : M.Satisfies x (Formula.dia 1 (.atom p)) :=
    hψx.1 x ((hM 0).1 x)
  obtain ⟨y, hxy, hp⟩ := (M.satisfies_dia x 1 (.atom p)).mp hdia
  exact (hbel y hxy).2 hp

/-- The third formula is unbelievable to agent 2 already in KD45. -/
theorem example2_third_unbelievable_to_two_kd45 (p : Atom) :
    Static.Unbelievable
      (Static.Classes.KD45 : FrameClass.{u} Atom (Fin 2))
      1 (example2_third p) := by
  rintro ⟨W, M, hM, x, hbel⟩
  obtain ⟨y, hxy⟩ := (hM 1).1 x
  have hχy := hbel y hxy
  obtain ⟨z, hyz, hdia⟩ :=
    (M.satisfies_dia y 1 (Formula.dia 0 (.neg (.atom p)))).mp hχy.2
  obtain ⟨t, hzt, hnotp⟩ :=
    (M.satisfies_dia z 0 (.neg (.atom p))).mp hdia
  have hχz := hbel z ((hM 1).2.1 hxy hyz)
  exact hnotp (hχz.1 t hzt)

/-- A KD45 model where agent 1 always sees the `p`-world and agent 2
sees only the current world. -/
private def forwardModel : Model (ULift.{u} Bool) Atom (Fin 2) where
  rel j x y := if j = 0 then y.down = true else x = y
  val _ x := x.down = true

private theorem forwardModel_isKD45 :
    IsKD45 (forwardModel (Atom := Atom) :
      Model (ULift.{u} Bool) Atom (Fin 2)) := by
  intro j
  by_cases hj : j = 0
  · subst j
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨ULift.up true, by simp [forwardModel]⟩
    · intro x y z _ hyz
      simpa [forwardModel] using hyz
    · intro x y z _ hxz
      simpa [forwardModel] using hxz
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨x, by simp [forwardModel, hj]⟩
    · intro x y z hxy hyz
      have hxy' : x = y := by simpa [forwardModel, hj] using hxy
      have hyz' : y = z := by simpa [forwardModel, hj] using hyz
      simpa [forwardModel, hj] using hxy'.trans hyz'
    · intro x y z hxy hxz
      have hxy' : x = y := by simpa [forwardModel, hj] using hxy
      have hxz' : x = z := by simpa [forwardModel, hj] using hxz
      simpa [forwardModel, hj] using hxy'.symm.trans hxz'

/-- The second formula remains believable to agent 2 in KD45. -/
theorem example2_second_believable_to_two_kd45 (p : Atom) :
    Static.Believable
      (Static.Classes.KD45 : FrameClass.{u} Atom (Fin 2))
      1 (example2_second p) := by
  let M : Model (ULift.{u} Bool) Atom (Fin 2) := forwardModel
  have hψ : M.Satisfies (ULift.up false) (example2_second p) := by
    constructor
    · intro y h0y
      have hy : y.down = true := by
        simpa [M, forwardModel] using h0y
      cases y with
      | up b =>
          cases b with
          | false => cases hy
          | true =>
              exact (M.satisfies_dia (ULift.up true) 1 (.atom p)).mpr
                ⟨ULift.up true,
                  by simp [M, forwardModel],
                  by simp [M, forwardModel, Model.Satisfies]⟩
    · simp [M, forwardModel, Model.Satisfies]
  refine ⟨ULift.{u} Bool, M, forwardModel_isKD45,
    ULift.up false, ?_⟩
  intro y h1y
  have hy : ULift.up false = y := by
    simpa [M, forwardModel] using h1y
  subst y
  exact hψ

/-- An S5 model where agent 1 distinguishes the two worlds, while agent 2
can access both. -/
private def splitModel : Model (ULift.{u} Bool) Atom (Fin 2) where
  rel j x y := if j = 0 then x = y else True
  val _ x := x.down = true

private theorem splitModel_isS5 :
    IsS5 (splitModel (Atom := Atom) :
      Model (ULift.{u} Bool) Atom (Fin 2)) := by
  intro j
  by_cases hj : j = 0
  · subst j
    refine ⟨?_, ?_, ?_⟩
    · intro x
      simp [splitModel]
    · intro x y z hxy hyz
      have hxy' : x = y := by simpa [splitModel] using hxy
      have hyz' : y = z := by simpa [splitModel] using hyz
      simpa [splitModel] using hxy'.trans hyz'
    · intro x y z hxy hxz
      have hxy' : x = y := by simpa [splitModel] using hxy
      have hxz' : x = z := by simpa [splitModel] using hxz
      simpa [splitModel] using hxy'.symm.trans hxz'
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      simp [splitModel, hj]
    · intro x y z _ _
      simp [splitModel, hj]
    · intro x y z _ _
      simp [splitModel, hj]

/-- The second formula is believable to agent 1, even in S5. -/
theorem example2_second_believable_to_one_s5 (p : Atom) :
    Static.Believable
      (Static.Classes.S5 : FrameClass.{u} Atom (Fin 2))
      0 (example2_second p) := by
  let M : Model (ULift.{u} Bool) Atom (Fin 2) := splitModel
  have hψ : M.Satisfies (ULift.up false) (example2_second p) := by
    constructor
    · intro y h0y
      have hy : ULift.up false = y := by
        simpa [M, splitModel] using h0y
      subst y
      exact (M.satisfies_dia (ULift.up false) 1 (.atom p)).mpr
        ⟨ULift.up true,
          by simp [M, splitModel],
          by simp [M, splitModel, Model.Satisfies]⟩
    · simp [M, splitModel, Model.Satisfies]
  refine ⟨ULift.{u} Bool, M, splitModel_isS5,
    ULift.up false, ?_⟩
  intro y h0y
  have hy : ULift.up false = y := by
    simpa [M, splitModel] using h0y
  subst y
  exact hψ

/-- The third formula is believable to agent 1, even in S5. -/
theorem example2_third_believable_to_one_s5 (p : Atom) :
    Static.Believable
      (Static.Classes.S5 : FrameClass.{u} Atom (Fin 2))
      0 (example2_third p) := by
  let M : Model (ULift.{u} Bool) Atom (Fin 2) := splitModel
  have hχ : M.Satisfies (ULift.up true) (example2_third p) := by
    constructor
    · intro y h0y
      have hy : ULift.up true = y := by
        simpa [M, splitModel] using h0y
      subst y
      simp [M, splitModel, Model.Satisfies]
    · apply (M.satisfies_dia (ULift.up true) 1 _).mpr
      refine ⟨ULift.up false, by simp [M, splitModel], ?_⟩
      apply (M.satisfies_dia (ULift.up false) 0 _).mpr
      exact ⟨ULift.up false,
        by simp [M, splitModel],
        by simp [M, splitModel, Model.Satisfies]⟩
  refine ⟨ULift.{u} Bool, M, splitModel_isS5,
    ULift.up true, ?_⟩
  intro y h0y
  have hy : ULift.up true = y := by
    simpa [M, splitModel] using h0y
  subst y
  exact hχ

/-- These stronger S5 witnesses imply the paper's KD45 believability
claims for agent 1. -/
theorem example2_second_believable_to_one_kd45 (p : Atom) :
    Static.Believable
      (Static.Classes.KD45 : FrameClass.{u} Atom (Fin 2))
      0 (example2_second p) := by
  have hS5 :
      Static.Believable
        (Static.Classes.S5 : FrameClass.{u} Atom (Fin 2))
        0 (example2_second p) :=
    example2_second_believable_to_one_s5 p
  obtain ⟨W, M, hM, x, hx⟩ := hS5
  exact ⟨W, M, hM.isKD45, x, hx⟩

theorem example2_third_believable_to_one_kd45 (p : Atom) :
    Static.Believable
      (Static.Classes.KD45 : FrameClass.{u} Atom (Fin 2))
      0 (example2_third p) := by
  have hS5 :
      Static.Believable
        (Static.Classes.S5 : FrameClass.{u} Atom (Fin 2))
        0 (example2_third p) :=
    example2_third_believable_to_one_s5 p
  obtain ⟨W, M, hM, x, hx⟩ := hS5
  exact ⟨W, M, hM.isKD45, x, hx⟩

end Independence
end SourcesOfUnknowability
