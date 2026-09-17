import SourcesOfUnknowability.AgentDNF
import Mathlib.Data.List.Sublists

/-!
# Constructive agent-relative K45 normal forms

Lemma 9: for any agent `i`, every multi-agent modal formula is equivalent on
K45 frames to a finite `i`-DNF. The normalizer treats operators of other
agents as objective atoms, and uses the K45 modal-subset decomposition for an
outer `i`-box.
-/

namespace SourcesOfUnknowability.AgentNormalization

open ClassificationSigmaValidity
open SourcesOfUnknowability.AgentDNF

universe u v t

variable {Atom : Type v} {Agent : Type t}

/-- A one-clause normal form for an objective formula. -/
def objectiveClause (φ : Formula Atom Agent) : Clause Atom Agent where
  alpha := φ
  boxes := []
  diamonds := []

/-- The empty modal component with a true objective part. -/
def truthClause [Inhabited Atom] : Clause Atom Agent :=
  objectiveClause Formula.verum

/-- Conjunction of two DNF clauses. -/
def join (c d : Clause Atom Agent) : Clause Atom Agent where
  alpha := .conj c.alpha d.alpha
  boxes := c.boxes ++ d.boxes
  diamonds := c.diamonds ++ d.diamonds

/-- Distribution of conjunction over finite disjunctions. -/
def conjunction (xs ys : List (Clause Atom Agent)) :
    List (Clause Atom Agent) :=
  xs.flatMap (fun c => ys.map (join c))

theorem holds_objectiveClause {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent)
    (φ : Formula Atom Agent) :
    Holds (objectiveClause φ) M x i ↔ M.Satisfies x φ := by
  simp [Holds, ModalPart, objectiveClause]

theorem holds_truthClause [Inhabited Atom] {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent) :
    Holds (truthClause : Clause Atom Agent) M x i := by
  simp [truthClause, holds_objectiveClause]

theorem holds_join {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent)
    (c d : Clause Atom Agent) :
    Holds (join c d) M x i ↔ Holds c M x i ∧ Holds d M x i := by
  simp only [Holds, ModalPart, join, Model.satisfies_and,
    List.mem_append]
  constructor
  · rintro ⟨⟨hcα, hdα⟩, hboxes, hdias⟩
    constructor
    · refine ⟨hcα, ?_, ?_⟩
      · intro β hβ; exact hboxes β (Or.inl hβ)
      · intro γ hγ; exact hdias γ (Or.inl hγ)
    · refine ⟨hdα, ?_, ?_⟩
      · intro β hβ; exact hboxes β (Or.inr hβ)
      · intro γ hγ; exact hdias γ (Or.inr hγ)
  · rintro ⟨⟨hcα, hcbox, hcdia⟩, ⟨hdα, hdbox, hddia⟩⟩
    refine ⟨⟨hcα, hdα⟩, ?_, ?_⟩
    · intro β hβ
      rcases hβ with hβ | hβ
      · exact hcbox β hβ
      · exact hdbox β hβ
    · intro γ hγ
      rcases hγ with hγ | hγ
      · exact hcdia γ hγ
      · exact hddia γ hγ

theorem holds_singleton {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent)
    (c : Clause Atom Agent) :
    HoldsDNF [c] M x i ↔ Holds c M x i := by
  simp [HoldsDNF]

theorem holds_append {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent)
    (xs ys : List (Clause Atom Agent)) :
    HoldsDNF (xs ++ ys) M x i ↔
      HoldsDNF xs M x i ∨ HoldsDNF ys M x i := by
  simp only [HoldsDNF, List.mem_append]
  constructor
  · rintro ⟨c, hc, hholds⟩
    rcases hc with hx | hy
    · exact Or.inl ⟨c, hx, hholds⟩
    · exact Or.inr ⟨c, hy, hholds⟩
  · rintro (⟨c, hc, hholds⟩ | ⟨c, hc, hholds⟩)
    · exact ⟨c, Or.inl hc, hholds⟩
    · exact ⟨c, Or.inr hc, hholds⟩

theorem holds_conjunction {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent)
    (xs ys : List (Clause Atom Agent)) :
    HoldsDNF (conjunction xs ys) M x i ↔
      HoldsDNF xs M x i ∧ HoldsDNF ys M x i := by
  simp only [HoldsDNF, conjunction, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨e, ⟨c, hc, d, hd, he⟩, hehold⟩
    subst e
    obtain ⟨hcHold, hdHold⟩ := (holds_join M x i c d).1 hehold
    exact ⟨⟨c, hc, hcHold⟩, ⟨d, hd, hdHold⟩⟩
  · rintro ⟨⟨c, hc, hcHold⟩, ⟨d, hd, hdHold⟩⟩
    exact ⟨join c d, ⟨c, hc, d, hd, rfl⟩,
      (holds_join M x i c d).2 ⟨hcHold, hdHold⟩⟩

theorem objective_or (i : Agent) (φ ψ : Formula Atom Agent)
    (hφ : Objective i φ) (hψ : Objective i ψ) :
    Objective i (Formula.or φ ψ) := by
  exact ⟨hφ, hψ⟩

theorem objective_verum [Inhabited Atom] (i : Agent) :
    Objective i (Formula.verum : Formula Atom Agent) := by
  simp [Formula.verum, Formula.falsum, Objective]

theorem objective_falsum [Inhabited Atom] (i : Agent) :
    Objective i (Formula.falsum : Formula Atom Agent) := by
  simp [Formula.falsum, Objective]

theorem isIDNF_objectiveClause (i : Agent)
    (φ : Formula Atom Agent) (hφ : Objective i φ) :
    IsIDNF i [objectiveClause φ] := by
  simp [IsIDNF, objectiveClause, hφ]

theorem isIDNF_join (i : Agent) (c d : Clause Atom Agent)
    (hc : Objective i c.alpha ∧
      (∀ β ∈ c.boxes, Objective i β) ∧
      (∀ γ ∈ c.diamonds, Objective i γ))
    (hd : Objective i d.alpha ∧
      (∀ β ∈ d.boxes, Objective i β) ∧
      (∀ γ ∈ d.diamonds, Objective i γ)) :
    Objective i (join c d).alpha ∧
      (∀ β ∈ (join c d).boxes, Objective i β) ∧
      (∀ γ ∈ (join c d).diamonds, Objective i γ) := by
  constructor
  · exact ⟨hc.1, hd.1⟩
  constructor
  · intro β hβ
    rcases List.mem_append.mp hβ with hβ | hβ
    · exact hc.2.1 β hβ
    · exact hd.2.1 β hβ
  · intro γ hγ
    rcases List.mem_append.mp hγ with hγ | hγ
    · exact hc.2.2 γ hγ
    · exact hd.2.2 γ hγ

theorem isIDNF_conjunction (i : Agent)
    (xs ys : List (Clause Atom Agent))
    (hx : IsIDNF i xs) (hy : IsIDNF i ys) :
    IsIDNF i (conjunction xs ys) := by
  intro e he
  obtain ⟨c, hc, hmap⟩ := List.mem_flatMap.mp he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmap
  exact isIDNF_join i c d (hx c hc) (hy d hd)

/-- Objective disjunction of the alpha parts of selected clauses. -/
def alphaOr [Inhabited Atom] :
    List (Clause Atom Agent) → Formula Atom Agent
  | [] => Formula.falsum
  | c :: cs => Formula.or c.alpha (alphaOr cs)

theorem holds_alphaOr [Inhabited Atom] {World : Type u}
    (M : Model World Atom Agent) (x : World)
    (cs : List (Clause Atom Agent)) :
    M.Satisfies x (alphaOr cs) ↔
      ∃ c ∈ cs, M.Satisfies x c.alpha := by
  induction cs with
  | nil => simp [alphaOr]
  | cons c cs ih =>
      rw [alphaOr, M.satisfies_or, ih]
      simp only [List.mem_cons]
      constructor
      · rintro (hc | ⟨d, hd, hda⟩)
        · exact ⟨c, Or.inl rfl, hc⟩
        · exact ⟨d, Or.inr hd, hda⟩
      · rintro ⟨d, hd, hda⟩
        rcases hd with rfl | hd
        · exact Or.inl hda
        · exact Or.inr ⟨d, hd, hda⟩

theorem objective_alphaOr [Inhabited Atom] (i : Agent)
    (cs : List (Clause Atom Agent))
    (h : ∀ c ∈ cs, Objective i c.alpha) :
    Objective i (alphaOr cs) := by
  induction cs with
  | nil => exact objective_falsum i
  | cons c cs ih =>
      apply objective_or i c.alpha (alphaOr cs)
      · exact h c (by simp)
      · apply ih
        intro d hd
        exact h d (by simp [hd])

/-- A K45 diamond pulls the modal part of a clause outside and leaves a
diamond over its objective alpha part. -/
def diaLiftClause [Inhabited Atom] (c : Clause Atom Agent) :
    Clause Atom Agent where
  alpha := Formula.verum
  boxes := c.boxes
  diamonds := c.diamonds ++ [c.alpha]

def diaLift [Inhabited Atom] (cs : List (Clause Atom Agent)) :
    List (Clause Atom Agent) :=
  cs.map diaLiftClause

theorem holds_diaLiftClause [Inhabited Atom] {World : Type u}
    (M : Model World Atom Agent) (hM : IsK45 M)
    (x : World) (i : Agent) (c : Clause Atom Agent) :
    Holds (diaLiftClause c) M x i ↔
      ∃ y, M.rel i x y ∧ Holds c M y i := by
  constructor
  · rintro ⟨_, hboxes, hdias⟩
    have halphaDia : M.Satisfies x (Formula.dia i c.alpha) :=
      hdias c.alpha (List.mem_append.mpr (Or.inr (by simp)))
    obtain ⟨y, hxy, halpha⟩ :=
      (M.satisfies_dia x i c.alpha).mp halphaDia
    have hmodalX : ModalPart c M x i := by
      constructor
      · exact hboxes
      · intro γ hγ
        exact hdias γ (List.mem_append.mpr (Or.inl hγ))
    exact ⟨y, hxy, halpha,
      (modalPart_agree c hM hxy).mp hmodalX⟩
  · rintro ⟨y, hxy, halpha, hmodalY⟩
    have hmodalX := (modalPart_agree c hM hxy).mpr hmodalY
    refine ⟨M.satisfies_verum x, hmodalX.1, ?_⟩
    intro γ hγ
    rcases List.mem_append.mp hγ with hγ | hγ
    · exact hmodalX.2 γ hγ
    · simp only [List.mem_singleton] at hγ
      subst γ
      exact (M.satisfies_dia x i c.alpha).mpr ⟨y, hxy, halpha⟩

theorem holds_diaLift [Inhabited Atom] {World : Type u}
    (M : Model World Atom Agent) (hM : IsK45 M)
    (x : World) (i : Agent) (cs : List (Clause Atom Agent)) :
    HoldsDNF (diaLift cs) M x i ↔
      ∃ y, M.rel i x y ∧ HoldsDNF cs M y i := by
  constructor
  · rintro ⟨d, hd, hholds⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    obtain ⟨y, hxy, hy⟩ := (holds_diaLiftClause M hM x i c).mp hholds
    exact ⟨y, hxy, c, hc, hy⟩
  · rintro ⟨y, hxy, c, hc, hy⟩
    exact ⟨diaLiftClause c, List.mem_map.mpr ⟨c, hc, rfl⟩,
      (holds_diaLiftClause M hM x i c).mpr ⟨y, hxy, hy⟩⟩

theorem isIDNF_diaLift [Inhabited Atom] (i : Agent)
    (cs : List (Clause Atom Agent)) (h : IsIDNF i cs) :
    IsIDNF i (diaLift cs) := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  obtain ⟨ha, hb, hd⟩ := h c hc
  refine ⟨objective_verum i, hb, ?_⟩
  intro γ hγ
  rcases List.mem_append.mp hγ with hγ | hγ
  · exact hd γ hγ
  · simp only [List.mem_singleton] at hγ
    subst γ
    exact ha

/-- The clause induced by one selected subfamily in Lemma 7. -/
def boxLiftClause [Inhabited Atom]
    (selected : List (Clause Atom Agent)) : Clause Atom Agent where
  alpha := Formula.verum
  boxes := selected.flatMap (fun c => c.boxes) ++ [alphaOr selected]
  diamonds := selected.flatMap (fun c => c.diamonds)

/-- Enumerate all finite choices of clauses. -/
def boxLift [Inhabited Atom] (cs : List (Clause Atom Agent)) :
    List (Clause Atom Agent) :=
  cs.sublists.map boxLiftClause

theorem holds_boxLiftClause [Inhabited Atom] {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent)
    (selected : List (Clause Atom Agent)) :
    Holds (boxLiftClause selected) M x i ↔
      (∀ c ∈ selected, ModalPart c M x i) ∧
      (∀ y, M.rel i x y →
        ∃ c ∈ selected, M.Satisfies y c.alpha) := by
  constructor
  · rintro ⟨_, hboxes, hdiamonds⟩
    constructor
    · intro c hc
      constructor
      · intro β hβ
        apply hboxes β
        apply List.mem_append.mpr
        apply Or.inl
        exact List.mem_flatMap.mpr ⟨c, hc, hβ⟩
      · intro γ hγ
        exact hdiamonds γ (List.mem_flatMap.mpr ⟨c, hc, hγ⟩)
    · intro y hxy
      have hboxAlpha : M.Satisfies x (.box i (alphaOr selected)) :=
        hboxes (alphaOr selected) (List.mem_append.mpr
          (Or.inr (by simp)))
      exact (holds_alphaOr M y selected).mp (hboxAlpha y hxy)
  · rintro ⟨hmodal, halpha⟩
    refine ⟨M.satisfies_verum x, ?_, ?_⟩
    · intro β hβ
      rcases List.mem_append.mp hβ with hβ | hβ
      · obtain ⟨c, hc, hcβ⟩ := List.mem_flatMap.mp hβ
        exact (hmodal c hc).1 β hcβ
      · simp only [List.mem_singleton] at hβ
        subst β
        intro y hxy
        exact (holds_alphaOr M y selected).mpr (halpha y hxy)
    · intro γ hγ
      obtain ⟨c, hc, hcγ⟩ := List.mem_flatMap.mp hγ
      exact (hmodal c hc).2 γ hcγ

theorem holds_boxLift_iff_decomposedWeak [Inhabited Atom]
    {World : Type u} (M : Model World Atom Agent)
    (x : World) (i : Agent) (cs : List (Clause Atom Agent)) :
    HoldsDNF (boxLift cs) M x i ↔
      DecomposedWeak cs M x i := by
  classical
  constructor
  · rintro ⟨d, hd, hholds⟩
    obtain ⟨selected, hselected, rfl⟩ := List.mem_map.mp hd
    have hsub : List.Sublist selected cs := List.mem_sublists.mp hselected
    obtain ⟨hmodal, halpha⟩ :=
      (holds_boxLiftClause M x i selected).mp hholds
    exact ⟨selected,
      (fun c hc => ⟨hsub.subset hc, hmodal c hc⟩), halpha⟩
  · rintro ⟨selected, hselected, halpha⟩
    let picked := cs.filter (fun c => c ∈ selected)
    have hpicked : picked ∈ cs.sublists :=
      List.mem_sublists.mpr List.filter_sublist
    have hmemPicked : ∀ c, c ∈ picked ↔ c ∈ cs ∧ c ∈ selected := by
      intro c
      simp [picked]
    refine ⟨boxLiftClause picked,
      List.mem_map.mpr ⟨picked, hpicked, rfl⟩, ?_⟩
    apply (holds_boxLiftClause M x i picked).mpr
    constructor
    · intro c hc
      exact (hselected c ((hmemPicked c).mp hc).2).2
    · intro y hxy
      obtain ⟨c, hc, ha⟩ := halpha y hxy
      have hcs : c ∈ cs := (hselected c hc).1
      exact ⟨c, (hmemPicked c).mpr ⟨hcs, hc⟩, ha⟩

theorem isIDNF_boxLift [Inhabited Atom] (i : Agent)
    (cs : List (Clause Atom Agent)) (h : IsIDNF i cs) :
    IsIDNF i (boxLift cs) := by
  intro d hd
  obtain ⟨selected, hselected, rfl⟩ := List.mem_map.mp hd
  have hsub : List.Sublist selected cs := List.mem_sublists.mp hselected
  have hselectedClause : ∀ c ∈ selected,
      Objective i c.alpha ∧
        (∀ β ∈ c.boxes, Objective i β) ∧
        (∀ γ ∈ c.diamonds, Objective i γ) := by
    intro c hc
    exact h c (hsub.subset hc)
  refine ⟨objective_verum i, ?_, ?_⟩
  · intro β hβ
    rcases List.mem_append.mp hβ with hβ | hβ
    · obtain ⟨c, hc, hcβ⟩ := List.mem_flatMap.mp hβ
      exact (hselectedClause c hc).2.1 β hcβ
    · simp only [List.mem_singleton] at hβ
      subst β
      exact objective_alphaOr i selected
        (fun c hc => (hselectedClause c hc).1)
  · intro γ hγ
    obtain ⟨c, hc, hcγ⟩ := List.mem_flatMap.mp hγ
    exact (hselectedClause c hc).2.2 γ hcγ

theorem holds_boxLift [Inhabited Atom] {World : Type u}
    (M : Model World Atom Agent) (hM : IsK45 M)
    (x : World) (i : Agent) (cs : List (Clause Atom Agent)) :
    HoldsDNF (boxLift cs) M x i ↔
      ∀ y, M.rel i x y → HoldsDNF cs M y i := by
  exact (holds_boxLift_iff_decomposedWeak M x i cs).trans
    (box_iff_decomposedWeak cs hM x i).symm

theorem isIDNF_append (i : Agent) (xs ys : List (Clause Atom Agent))
    (hx : IsIDNF i xs) (hy : IsIDNF i ys) :
    IsIDNF i (xs ++ ys) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hx c hc
  · exact hy c hc

mutual

/-- Positive normal form relative to agent `i`. -/
def positive [Inhabited Atom] [DecidableEq Agent] (i : Agent) :
    Formula Atom Agent → List (Clause Atom Agent)
  | .atom p => [objectiveClause (.atom p)]
  | .neg φ => negative i φ
  | .conj φ ψ => conjunction (positive i φ) (positive i ψ)
  | .box j φ =>
      if j = i then boxLift (positive i φ)
      else [objectiveClause (.box j φ)]

/-- Negative normal form, equivalent to the negation of its input. -/
def negative [Inhabited Atom] [DecidableEq Agent] (i : Agent) :
    Formula Atom Agent → List (Clause Atom Agent)
  | .atom p => [objectiveClause (.neg (.atom p))]
  | .neg φ => positive i φ
  | .conj φ ψ => negative i φ ++ negative i ψ
  | .box j φ =>
      if j = i then diaLift (negative i φ)
      else [objectiveClause (.neg (.box j φ))]

end

/-- Both outputs satisfy Definition 13's syntactic side conditions. -/
theorem normalizers_are_iDNF [Inhabited Atom] [DecidableEq Agent]
    (i : Agent) (φ : Formula Atom Agent) :
    IsIDNF i (positive i φ) ∧ IsIDNF i (negative i φ) := by
  induction φ with
  | atom p =>
      constructor
      · simpa [positive] using
          (isIDNF_objectiveClause i (.atom p) trivial)
      · simpa [negative] using
          (isIDNF_objectiveClause i (.neg (.atom p)) trivial)
  | neg ψ ih =>
      simpa [positive, negative] using And.symm ih
  | conj ψ χ ihψ ihχ =>
      constructor
      · simpa [positive] using
          isIDNF_conjunction i (positive i ψ) (positive i χ)
            ihψ.1 ihχ.1
      · simpa [negative] using
          isIDNF_append i (negative i ψ) (negative i χ)
            ihψ.2 ihχ.2
  | box j ψ ih =>
      by_cases hji : j = i
      · subst j
        constructor
        · simpa [positive] using isIDNF_boxLift i (positive i ψ) ih.1
        · simpa [negative] using isIDNF_diaLift i (negative i ψ) ih.2
      · constructor
        · simpa [positive, hji] using
            (isIDNF_objectiveClause i (.box j ψ) (by exact hji))
        · simpa [negative, hji] using
            (isIDNF_objectiveClause i (.neg (.box j ψ)) (by exact hji))

/-- The positive and negative normal forms have the intended meanings on
every K45 model. The box step is precisely Lemma 7, while the diamond step
uses invariance of each clause's modal part along an accessibility edge. -/
theorem normalizers_correct [Inhabited Atom] [DecidableEq Agent]
    (i : Agent) (φ : Formula Atom Agent) :
    (∀ {World : Type u} (M : Model World Atom Agent) (_hM : IsK45 M)
      (x : World), HoldsDNF (positive i φ) M x i ↔ M.Satisfies x φ) ∧
    (∀ {World : Type u} (M : Model World Atom Agent) (_hM : IsK45 M)
      (x : World), HoldsDNF (negative i φ) M x i ↔ ¬ M.Satisfies x φ) := by
  classical
  induction φ with
  | atom p =>
      constructor
      · intro World M hM x
        simpa [positive] using
          (holds_singleton M x i (objectiveClause (.atom p))).trans
            (holds_objectiveClause M x i (.atom p))
      · intro World M hM x
        simpa [negative, Model.Satisfies] using
          (holds_singleton M x i (objectiveClause (.neg (.atom p)))).trans
            (holds_objectiveClause M x i (.neg (.atom p)))
  | neg ψ ih =>
      constructor
      · intro World M hM x
        simpa [positive, Model.Satisfies] using ih.2 M hM x
      · intro World M hM x
        simpa [negative, Model.Satisfies] using ih.1 M hM x
  | conj ψ χ ihψ ihχ =>
      constructor
      · intro World M hM x
        rw [positive, holds_conjunction, ihψ.1 M hM x, ihχ.1 M hM x]
        rfl
      · intro World M hM x
        rw [negative, holds_append, ihψ.2 M hM x, ihχ.2 M hM x]
        change (¬ M.Satisfies x ψ ∨ ¬ M.Satisfies x χ) ↔
          ¬ (M.Satisfies x ψ ∧ M.Satisfies x χ)
        constructor
        · intro h hboth
          rcases h with hψ | hχ
          · exact hψ hboth.1
          · exact hχ hboth.2
        · intro h
          by_cases hψ : M.Satisfies x ψ
          · exact Or.inr (fun hχ => h ⟨hψ, hχ⟩)
          · exact Or.inl hψ
  | box j ψ ih =>
      by_cases hji : j = i
      · subst j
        constructor
        · intro World M hM x
          calc
            HoldsDNF (positive i (.box i ψ)) M x i ↔
                ∀ y, M.rel i x y → HoldsDNF (positive i ψ) M y i := by
              simpa [positive] using
                (holds_boxLift M hM x i (positive i ψ))
            _ ↔ M.Satisfies x (.box i ψ) := by
              change (∀ y, M.rel i x y → HoldsDNF (positive i ψ) M y i) ↔
                (∀ y, M.rel i x y → M.Satisfies y ψ)
              exact forall_congr' (fun y =>
                imp_congr_right (fun _ => ih.1 M hM y))
        · intro World M hM x
          calc
            HoldsDNF (negative i (.box i ψ)) M x i ↔
                ∃ y, M.rel i x y ∧ HoldsDNF (negative i ψ) M y i := by
              simpa [negative] using
                (holds_diaLift M hM x i (negative i ψ))
            _ ↔ ¬ M.Satisfies x (.box i ψ) := by
              constructor
              · rintro ⟨y, hxy, hy⟩ hbox
                exact ((ih.2 M hM y).mp hy) (hbox y hxy)
              · intro hn
                by_contra hnone
                apply hn
                intro y hxy
                by_contra hnotψ
                apply hnone
                exact ⟨y, hxy, (ih.2 M hM y).mpr hnotψ⟩
      · constructor
        · intro World M hM x
          simpa [positive, hji] using
            (holds_singleton M x i (objectiveClause (.box j ψ))).trans
              (holds_objectiveClause M x i (.box j ψ))
        · intro World M hM x
          simpa [negative, hji, Model.Satisfies] using
            (holds_singleton M x i (objectiveClause (.neg (.box j ψ)))).trans
              (holds_objectiveClause M x i (.neg (.box j ψ)))

/-- Lemma 9: every multi-agent formula has a finite `i`-DNF, constructed
explicitly by `positive`, equivalent on all K45 frames. -/
theorem lemma9 [Inhabited Atom] [DecidableEq Agent]
    (i : Agent) (φ : Formula Atom Agent) :
    IsIDNF i (positive i φ) ∧
      (∀ {World : Type u} (M : Model World Atom Agent) (_hM : IsK45 M)
        (x : World),
        M.Satisfies x φ ↔ HoldsDNF (positive i φ) M x i) := by
  constructor
  · exact (normalizers_are_iDNF i φ).1
  · intro World M hM x
    exact ((normalizers_correct i φ).1 M hM x).symm

/-- Lemma 9 as an existential statement for any agent type. Classical
decidable equality is used only to compute which modal operators belong to
the distinguished agent. -/
theorem exists_iDNF [Inhabited Atom]
    (i : Agent) (φ : Formula Atom Agent) :
    ∃ clauses : List (Clause Atom Agent), IsIDNF i clauses ∧
      ∀ {World : Type u} (M : Model World Atom Agent) (_hM : IsK45 M)
        (x : World),
        M.Satisfies x φ ↔ HoldsDNF clauses M x i := by
  classical
  refine ⟨positive i φ, (normalizers_are_iDNF i φ).1, ?_⟩
  intro World M hM x
  exact ((normalizers_correct i φ).1 M hM x).symm

end SourcesOfUnknowability.AgentNormalization
