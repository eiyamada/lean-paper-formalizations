import ClassificationSigmaValidity.Frames

/-!
# Finite modal disjunctive normal forms

The paper separates each disjunct into a propositional part, a finite list of
box requirements, and a finite list of diamond requirements.  We keep that
structure explicit.  The semantic lemmas below apply to an arbitrary finite
list of such clauses; they do not assume that a normal form for every formula
has already been constructed.
-/

namespace SourcesOfUnknowability
namespace DNF

open ClassificationSigmaValidity

universe u u' v w

variable {Atom : Type v} {Agent : Type w}

/-- A disjunct `α ∧ ⋀□β ∧ ⋀◇γ`, with modal-free `α`. -/
structure Clause (Atom : Type v) (Agent : Type w) where
  alpha : Formula Atom Agent
  boxes : List (Formula Atom Agent)
  diamonds : List (Formula Atom Agent)
  alpha_modalFree : Formula.modalDepth alpha = 0

namespace Clause

/-- The modal part `δ^{□◇}` of a disjunct. -/
def ModalPart (c : Clause Atom Agent) {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent) : Prop :=
  (∀ β ∈ c.boxes, M.Satisfies x (.box i β)) ∧
    (∀ γ ∈ c.diamonds, M.Satisfies x (Formula.dia i γ))

/-- The semantic interpretation of one disjunct. -/
def Holds (c : Clause Atom Agent) {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent) : Prop :=
  M.Satisfies x c.alpha ∧ c.ModalPart M x i

theorem modalPart_agree (c : Clause Atom Agent) {World : Type u}
    {M : Model World Atom Agent} (hM : IsK45 M) {i : Agent} {x y : World}
    (hxy : M.rel i x y) :
    c.ModalPart M x i ↔ c.ModalPart M y i := by
  constructor
  · rintro ⟨hbox, hdia⟩
    constructor
    · intro β hβ
      exact (M.modalAgreement_box hM hxy β).mp (hbox β hβ)
    · intro γ hγ
      exact (M.modalAgreement_dia hM hxy γ).mp (hdia γ hγ)
  · rintro ⟨hbox, hdia⟩
    constructor
    · intro β hβ
      exact (M.modalAgreement_box hM hxy β).mpr (hbox β hβ)
    · intro γ hγ
      exact (M.modalAgreement_dia hM hxy γ).mpr (hdia γ hγ)

end Clause

/-- Semantic interpretation of a finite disjunction of clauses. -/
def Holds (clauses : List (Clause Atom Agent)) {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent) : Prop :=
  ∃ c ∈ clauses, c.Holds M x i

/-- Clauses whose modal requirements hold at the chosen state. -/
noncomputable def active (clauses : List (Clause Atom Agent)) {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent) :
    List (Clause Atom Agent) := by
  classical
  exact clauses.filter (fun c => decide (c.ModalPart M x i))

theorem mem_active_iff (clauses : List (Clause Atom Agent)) {World : Type u}
    (M : Model World Atom Agent) (x : World) (i : Agent)
    (c : Clause Atom Agent) :
    c ∈ active clauses M x i ↔ c ∈ clauses ∧ c.ModalPart M x i := by
  classical
  simp [active]

/-- Semantic form of the subset decomposition in Lemma 4.  On a K45 frame,
the modal part of every clause is constant across each accessibility cluster;
only its propositional part needs to be tested at individual successors. -/
theorem box_iff_active_alpha (clauses : List (Clause Atom Agent))
    {World : Type u} {M : Model World Atom Agent} (hM : IsK45 M)
    (x : World) (i : Agent) :
    (∀ y, M.rel i x y → Holds clauses M y i) ↔
      (∀ y, M.rel i x y →
        ∃ c ∈ active clauses M x i, M.Satisfies y c.alpha) := by
  constructor
  · intro h y hxy
    obtain ⟨c, hc, ha, hm⟩ := h y hxy
    exact ⟨c, (mem_active_iff clauses M x i c).2
      ⟨hc, (c.modalPart_agree hM hxy).2 hm⟩, ha⟩
  · intro h y hxy
    obtain ⟨c, hc, ha⟩ := h y hxy
    obtain ⟨hmem, hm⟩ := (mem_active_iff clauses M x i c).1 hc
    exact ⟨c, hmem, ha, (c.modalPart_agree hM hxy).1 hm⟩

/-- Existential subset formulation of the preceding K45 decomposition.
The chosen subfamily contains exactly the clauses whose modal parts hold at
the source state, including the requirement that omitted clauses fail there. -/
theorem box_iff_modal_subset (clauses : List (Clause Atom Agent))
    {World : Type u} {M : Model World Atom Agent} (hM : IsK45 M)
    (x : World) (i : Agent) :
    (∀ y, M.rel i x y → Holds clauses M y i) ↔
      (∃ selected : List (Clause Atom Agent),
        (∀ c, c ∈ selected ↔ c ∈ clauses ∧ c.ModalPart M x i) ∧
        ∀ y, M.rel i x y →
          ∃ c ∈ selected, M.Satisfies y c.alpha) := by
  rw [box_iff_active_alpha clauses hM x i]
  constructor
  · intro h
    exact ⟨active clauses M x i,
      fun c => mem_active_iff clauses M x i c, h⟩
  · rintro ⟨selected, hselected, h⟩ y hxy
    obtain ⟨c, hc, ha⟩ := h y hxy
    exact ⟨c, (mem_active_iff clauses M x i c).2
      ((hselected c).1 hc), ha⟩

/-- K-satisfiability at some pointed model. -/
def SatisfiableK (φ : Formula Atom Agent) : Prop :=
  ∃ (World : Type u) (M : Model World Atom Agent) (x : World), M.Satisfies x φ

/-- KD-satisfiability for the distinguished single agent. -/
def SatisfiableKD (i : Agent) (φ : Formula Atom Agent) : Prop :=
  ∃ (World : Type u) (M : Model World Atom Agent) (x : World),
    Frame.Serial (M.rel i) ∧ M.Satisfies x φ

/-- Joint K-satisfiability of all formulas in two finite lists. -/
def CompatibleK (B E : List (Formula Atom Agent)) : Prop :=
  ∃ (World : Type u) (M : Model World Atom Agent) (x : World),
    (∀ β ∈ B, M.Satisfies x β) ∧ (∀ ψ ∈ E, M.Satisfies x ψ)

/-- Joint KD-satisfiability of all formulas in two finite lists. -/
def CompatibleKD (i : Agent) (B E : List (Formula Atom Agent)) : Prop :=
  ∃ (World : Type u) (M : Model World Atom Agent) (x : World),
    Frame.Serial (M.rel i) ∧
    (∀ β ∈ B, M.Satisfies x β) ∧ (∀ ψ ∈ E, M.Satisfies x ψ)

/-- The necessary K criterion behind Theorem 2.  Equivalence of `φ` with the
specified normal form is an explicit hypothesis. -/
theorem necessary_K (clauses : List (Clause Atom Agent))
    (φ : Formula Atom Agent) (i : Agent)
    (hform : ∀ {World : Type u} (M : Model World Atom Agent) (x : World),
      M.Satisfies x φ ↔ Holds clauses M x i)
    (hknow : ∃ (World : Type u) (M : Model World Atom Agent) (x : World),
      M.Satisfies x φ ∧ M.Satisfies x (.box i φ)) :
    ∃ c ∈ clauses, SatisfiableK.{u} c.alpha ∧
      ∀ γ ∈ c.diamonds, CompatibleK.{u} c.boxes [φ, γ] := by
  obtain ⟨World, M, x, hφ, hbox⟩ := hknow
  obtain ⟨c, hc, ha, hmodal⟩ := (hform M x).1 hφ
  refine ⟨c, hc, ⟨World, M, x, ha⟩, ?_⟩
  intro γ hγ
  obtain ⟨y, hxy, hyγ⟩ := (M.satisfies_dia x i γ).1 (hmodal.2 γ hγ)
  refine ⟨World, M, y, ?_, ?_⟩
  · intro β hβ
    exact (hmodal.1 β hβ) y hxy
  · intro ψ hψ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl
    · exact hbox y hxy
    · exact hyγ

/-- The necessary KD criterion adds a successor even if the clause has no
diamond requirement, using seriality of the frame. -/
theorem necessary_KD (clauses : List (Clause Atom Agent))
    (φ : Formula Atom Agent) (i : Agent)
    (hform : ∀ {World : Type u} (M : Model World Atom Agent) (x : World),
      M.Satisfies x φ ↔ Holds clauses M x i)
    (hknow : ∃ (World : Type u) (M : Model World Atom Agent) (x : World),
      Frame.Serial (M.rel i) ∧
      M.Satisfies x φ ∧ M.Satisfies x (.box i φ)) :
    ∃ c ∈ clauses, SatisfiableKD.{u} i c.alpha ∧
      CompatibleKD.{u} i c.boxes [φ] ∧
      ∀ γ ∈ c.diamonds, CompatibleKD.{u} i c.boxes [φ, γ] := by
  obtain ⟨World, M, x, hserial, hφ, hbox⟩ := hknow
  obtain ⟨c, hc, ha, hmodal⟩ := (hform M x).1 hφ
  refine ⟨c, hc, ⟨World, M, x, hserial, ha⟩, ?_, ?_⟩
  · obtain ⟨y, hxy⟩ := hserial x
    refine ⟨World, M, y, hserial, ?_, ?_⟩
    · intro β hβ
      exact (hmodal.1 β hβ) y hxy
    · intro ψ hψ
      simp only [List.mem_singleton] at hψ
      subst ψ
      exact hbox y hxy
  · intro γ hγ
    obtain ⟨y, hxy, hyγ⟩ := (M.satisfies_dia x i γ).1 (hmodal.2 γ hγ)
    refine ⟨World, M, y, hserial, ?_, ?_⟩
    · intro β hβ
      exact (hmodal.1 β hβ) y hxy
    · intro ψ hψ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
      rcases hψ with rfl | rfl
      · exact hbox y hxy
      · exact hyγ

/-- Theorem 2, K direction that rules out knowledge from failure of every
clause's root or required successor conditions. -/
theorem unknowable_K_of_clause_obstructions
    (clauses : List (Clause Atom Agent)) (φ : Formula Atom Agent) (i : Agent)
    (hform : ∀ {World : Type u} (M : Model World Atom Agent) (x : World),
      M.Satisfies x φ ↔ Holds clauses M x i)
    (hobstruct : ∀ c ∈ clauses,
      ¬ SatisfiableK.{u} c.alpha ∨
        ∃ γ ∈ c.diamonds, ¬ CompatibleK.{u} c.boxes [φ, γ]) :
    ¬ ∃ (World : Type u) (M : Model World Atom Agent) (x : World),
      M.Satisfies x φ ∧ M.Satisfies x (.box i φ) := by
  intro hknow
  obtain ⟨c, hc, hα, hγ⟩ := necessary_K clauses φ i hform hknow
  rcases hobstruct c hc with hbadα | ⟨γ, hmem, hbadγ⟩
  · exact hbadα hα
  · exact hbadγ (hγ γ hmem)

/-- Theorem 2, KD direction; seriality supplies the additional unlabelled
successor condition. -/
theorem unknowable_KD_of_clause_obstructions
    (clauses : List (Clause Atom Agent)) (φ : Formula Atom Agent) (i : Agent)
    (hform : ∀ {World : Type u} (M : Model World Atom Agent) (x : World),
      M.Satisfies x φ ↔ Holds clauses M x i)
    (hobstruct : ∀ c ∈ clauses,
      ¬ SatisfiableKD.{u} i c.alpha ∨
        ¬ CompatibleKD.{u} i c.boxes [φ] ∨
        ∃ γ ∈ c.diamonds, ¬ CompatibleKD.{u} i c.boxes [φ, γ]) :
    ¬ ∃ (World : Type u) (M : Model World Atom Agent) (x : World),
      Frame.Serial (M.rel i) ∧
      M.Satisfies x φ ∧ M.Satisfies x (.box i φ) := by
  intro hknow
  obtain ⟨c, hc, hα, hbase, hγ⟩ := necessary_KD clauses φ i hform hknow
  rcases hobstruct c hc with hbadα | hbadbase | ⟨γ, hmem, hbadγ⟩
  · exact hbadα hα
  · exact hbadbase hbase
  · exact hbadγ (hγ γ hmem)

/-- A modal-free formula depends only on the valuation at the current state. -/
theorem modalFree_transfer {World₁ : Type u} {World₂ : Type u'}
    (M : Model World₁ Atom Agent) (N : Model World₂ Atom Agent)
    (x : World₁) (y : World₂) (φ : Formula Atom Agent)
    (hdepth : φ.modalDepth = 0)
    (hval : ∀ p, M.val p x ↔ N.val p y) :
    M.Satisfies x φ ↔ N.Satisfies y φ := by
  induction φ with
  | atom p => exact hval p
  | neg ψ ih =>
      simpa [Formula.modalDepth, Model.Satisfies] using
        not_congr (ih (by simpa [Formula.modalDepth] using hdepth))
  | conj ψ χ ihψ ihχ =>
      have hψ : ψ.modalDepth = 0 := by
        exact Nat.eq_zero_of_le_zero (by
          calc
            ψ.modalDepth ≤ max ψ.modalDepth χ.modalDepth := Nat.le_max_left _ _
            _ = 0 := hdepth)
      have hχ : χ.modalDepth = 0 := by
        exact Nat.eq_zero_of_le_zero (by
          calc
            χ.modalDepth ≤ max ψ.modalDepth χ.modalDepth := Nat.le_max_right _ _
            _ = 0 := hdepth)
      simpa [Model.Satisfies] using and_congr (ihψ hψ) (ihχ hχ)
  | box i ψ =>
      simp [Formula.modalDepth] at hdepth

/-- A pointed model on a fixed world type. -/
structure Pointed (World : Type u) (Atom : Type v) (Agent : Type w) where
  model : Model World Atom Agent
  point : World

variable {World : Type u}

namespace Pointed

def Satisfies (P : Pointed World Atom Agent) (φ : Formula Atom Agent) : Prop :=
  P.model.Satisfies P.point φ

end Pointed

/-- A disjoint family of copies of one world type, plus a new root.  The
`none` branch is reserved for the seriality witness in KD. -/
abbrev GluedWorld (World : Type u) (Atom : Type v) (Agent : Type w) :=
  Option (Option (Formula Atom Agent) × World)

/-- Rooted disjoint union of a family of pointed models. -/
def glue (root : Pointed World Atom Agent)
    (P : Option (Formula Atom Agent) → Pointed World Atom Agent)
    (i : Agent) (arrows : Option (Formula Atom Agent) → Prop) :
    Model (GluedWorld World Atom Agent) Atom Agent where
  rel a s t :=
    match s, t with
    | none, some (j, y) => a = i ∧ arrows j ∧ y = (P j).point
    | some (j, x), some (k, y) => j = k ∧ (P j).model.rel a x y
    | _, _ => False
  val p s :=
    match s with
    | none => root.model.val p root.point
    | some (j, x) => (P j).model.val p x

/-- Truth at an internal branch is unchanged by gluing. -/
theorem glue_branch_truth (root : Pointed World Atom Agent)
    (P : Option (Formula Atom Agent) → Pointed World Atom Agent)
    (i : Agent) (arrows : Option (Formula Atom Agent) → Prop)
    (φ : Formula Atom Agent) (j : Option (Formula Atom Agent)) (x : World) :
    (glue root P i arrows).Satisfies (some (j, x)) φ ↔
      (P j).model.Satisfies x φ := by
  induction φ generalizing j x with
  | atom p => rfl
  | neg ψ ih => simpa [Model.Satisfies] using not_congr (ih j x)
  | conj ψ χ ihψ ihχ =>
      simpa [Model.Satisfies] using and_congr (ihψ j x) (ihχ j x)
  | box a ψ ih =>
      constructor
      · intro h y hy
        apply (ih j y).1
        apply h (some (j, y))
        exact ⟨rfl, hy⟩
      · intro h z hz
        cases z with
        | none => cases hz
        | some pair =>
            rcases pair with ⟨k, y⟩
            obtain ⟨hjk, hrel⟩ := hz
            subst k
            exact (ih j y).2 (h y hrel)

/-- The new root sees exactly the selected branch points. -/
theorem glue_root_box (root : Pointed World Atom Agent)
    (P : Option (Formula Atom Agent) → Pointed World Atom Agent)
    (i : Agent) (arrows : Option (Formula Atom Agent) → Prop)
    (φ : Formula Atom Agent) :
    (glue root P i arrows).Satisfies none (.box i φ) ↔
      ∀ j, arrows j → (P j).Satisfies φ := by
  constructor
  · intro h j hj
    have hroot : (glue root P i arrows).Satisfies
        (some (j, (P j).point)) φ :=
      h (some (j, (P j).point)) ⟨rfl, hj, rfl⟩
    exact (glue_branch_truth root P i arrows φ j (P j).point).1 hroot
  · intro h z hz
    cases z with
    | none => cases hz
    | some pair =>
        rcases pair with ⟨j, y⟩
        obtain ⟨_, hj, hy⟩ := hz
        subst y
        exact (glue_branch_truth root P i arrows φ j (P j).point).2 (h j hj)

/-- Serial branch models and one selected base branch make the glued model
serial at the distinguished agent. -/
theorem glue_serial (root : Pointed World Atom Agent)
    (P : Option (Formula Atom Agent) → Pointed World Atom Agent)
    (i : Agent) (arrows : Option (Formula Atom Agent) → Prop)
    (hbase : arrows none)
    (hserial : ∀ j, Frame.Serial ((P j).model.rel i)) :
    Frame.Serial ((glue root P i arrows).rel i) := by
  intro s
  cases s with
  | none =>
      exact ⟨some (none, (P none).point), ⟨rfl, hbase, rfl⟩⟩
  | some pair =>
      rcases pair with ⟨j, x⟩
      obtain ⟨y, hy⟩ := hserial j x
      exact ⟨some (j, y), ⟨rfl, hy⟩⟩

/-- The root satisfies a chosen clause, and all its successors satisfy `φ`,
when the selected branches witness the box and diamond requirements. -/
theorem glue_realizes_clause (c : Clause Atom Agent)
    (φ : Formula Atom Agent) (root : Pointed World Atom Agent)
    (P : Option (Formula Atom Agent) → Pointed World Atom Agent)
    (i : Agent) (arrows : Option (Formula Atom Agent) → Prop)
    (hα : root.Satisfies c.alpha)
    (hboxes : ∀ j, arrows j → ∀ β ∈ c.boxes, (P j).Satisfies β)
    (hdiamonds : ∀ γ ∈ c.diamonds,
      arrows (some γ) ∧ (P (some γ)).Satisfies γ)
    (hφ : ∀ j, arrows j → (P j).Satisfies φ) :
    c.Holds (glue root P i arrows) none i ∧
      (glue root P i arrows).Satisfies none (.box i φ) := by
  constructor
  · constructor
    · exact (modalFree_transfer root.model (glue root P i arrows)
        root.point none c.alpha c.alpha_modalFree (fun _ => Iff.rfl)).1 hα
    · constructor
      · intro β hβ
        exact (glue_root_box root P i arrows β).2
          (fun j hj => hboxes j hj β hβ)
      · intro γ hγ
        obtain ⟨harr, hsat⟩ := hdiamonds γ hγ
        apply ((glue root P i arrows).satisfies_dia none i γ).2
        refine ⟨some (some γ, (P (some γ)).point), ?_, ?_⟩
        · exact ⟨rfl, harr, rfl⟩
        · exact (glue_branch_truth root P i arrows γ (some γ)
            (P (some γ)).point).2 hsat
  · exact (glue_root_box root P i arrows φ).2 hφ

/-- Converse witness construction for K when the separate satisfiability
witnesses have a common world type.  The tagged copies keep arbitrary modal
formulas true in their respective successor models. -/
theorem sufficient_K_commonWorld {A G W : Type u}
    (clauses : List (Clause A G)) (φ : Formula A G) (i : G)
    (hform : ∀ {V : Type u} (M : Model V A G) (x : V),
      M.Satisfies x φ ↔ Holds clauses M x i)
    (c : Clause A G) (hc : c ∈ clauses)
    (root : Pointed W A G) (hα : root.Satisfies c.alpha)
    (hγ : ∀ γ ∈ c.diamonds, ∃ Q : Pointed W A G,
      (∀ β ∈ c.boxes, Q.Satisfies β) ∧
      Q.Satisfies φ ∧ Q.Satisfies γ) :
    ∃ (V : Type u) (M : Model V A G) (x : V),
      M.Satisfies x φ ∧ M.Satisfies x (.box i φ) := by
  classical
  let P : Option (Formula A G) → Pointed W A G := fun j =>
    match j with
    | none => root
    | some γ => if h : γ ∈ c.diamonds then Classical.choose (hγ γ h) else root
  let arrows : Option (Formula A G) → Prop :=
    fun j => ∃ γ ∈ c.diamonds, j = some γ
  have hboxes : ∀ j, arrows j → ∀ β ∈ c.boxes, (P j).Satisfies β := by
    intro j hj β hβ
    obtain ⟨γ, hmem, rfl⟩ := hj
    have hs := Classical.choose_spec (hγ γ hmem)
    simpa [P, hmem] using hs.1 β hβ
  have hφ : ∀ j, arrows j → (P j).Satisfies φ := by
    intro j hj
    obtain ⟨γ, hmem, rfl⟩ := hj
    have hs := Classical.choose_spec (hγ γ hmem)
    simpa [P, hmem] using hs.2.1
  have hdiamonds : ∀ γ ∈ c.diamonds,
      arrows (some γ) ∧ (P (some γ)).Satisfies γ := by
    intro γ hmem
    have hs := Classical.choose_spec (hγ γ hmem)
    exact ⟨⟨γ, hmem, rfl⟩, by simpa [P, hmem] using hs.2.2⟩
  have hr := glue_realizes_clause c φ root P i arrows
    hα hboxes hdiamonds hφ
  exact ⟨GluedWorld W A G, glue root P i arrows, none,
    (hform (glue root P i arrows) none).2 ⟨c, hc, hr.1⟩, hr.2⟩

/-- The corresponding KD construction uses a separate base successor so that
the new root is serial even when there are no diamond requirements. -/
theorem sufficient_KD_commonWorld {A G W : Type u}
    (clauses : List (Clause A G)) (φ : Formula A G) (i : G)
    (hform : ∀ {V : Type u} (M : Model V A G) (x : V),
      M.Satisfies x φ ↔ Holds clauses M x i)
    (c : Clause A G) (hc : c ∈ clauses)
    (root base : Pointed W A G) (hα : root.Satisfies c.alpha)
    (hbase : Frame.Serial (base.model.rel i) ∧
      (∀ β ∈ c.boxes, base.Satisfies β) ∧ base.Satisfies φ)
    (hγ : ∀ γ ∈ c.diamonds, ∃ Q : Pointed W A G,
      Frame.Serial (Q.model.rel i) ∧
      (∀ β ∈ c.boxes, Q.Satisfies β) ∧
      Q.Satisfies φ ∧ Q.Satisfies γ) :
    ∃ (V : Type u) (M : Model V A G) (x : V),
      Frame.Serial (M.rel i) ∧
      M.Satisfies x φ ∧ M.Satisfies x (.box i φ) := by
  classical
  let P : Option (Formula A G) → Pointed W A G := fun j =>
    match j with
    | none => base
    | some γ => if h : γ ∈ c.diamonds then Classical.choose (hγ γ h) else base
  let arrows : Option (Formula A G) → Prop :=
    fun j => j = none ∨ ∃ γ ∈ c.diamonds, j = some γ
  have hboxes : ∀ j, arrows j → ∀ β ∈ c.boxes, (P j).Satisfies β := by
    intro j hj β hβ
    cases j with
    | none => exact hbase.2.1 β hβ
    | some γ =>
        rcases hj with hnone | ⟨δ, hmem, hEq⟩
        · cases hnone
        · have hγδ : γ = δ := Option.some.inj hEq
          subst δ
          have hs := Classical.choose_spec (hγ γ hmem)
          simpa [P, hmem] using hs.2.1 β hβ
  have hφ : ∀ j, arrows j → (P j).Satisfies φ := by
    intro j hj
    cases j with
    | none => exact hbase.2.2
    | some γ =>
        rcases hj with hnone | ⟨δ, hmem, hEq⟩
        · cases hnone
        · have hγδ : γ = δ := Option.some.inj hEq
          subst δ
          have hs := Classical.choose_spec (hγ γ hmem)
          simpa [P, hmem] using hs.2.2.1
  have hserial : ∀ j, Frame.Serial ((P j).model.rel i) := by
    intro j
    cases j with
    | none => exact hbase.1
    | some γ =>
        by_cases hmem : γ ∈ c.diamonds
        · have hs := Classical.choose_spec (hγ γ hmem)
          simpa [P, hmem] using hs.1
        · simpa [P, hmem] using hbase.1
  have hdiamonds : ∀ γ ∈ c.diamonds,
      arrows (some γ) ∧ (P (some γ)).Satisfies γ := by
    intro γ hmem
    have hs := Classical.choose_spec (hγ γ hmem)
    exact ⟨Or.inr ⟨γ, hmem, rfl⟩,
      by simpa [P, hmem] using hs.2.2.2⟩
  have hr := glue_realizes_clause c φ root P i arrows
    hα hboxes hdiamonds hφ
  exact ⟨GluedWorld W A G, glue root P i arrows, none,
    glue_serial root P i arrows (Or.inl rfl) hserial,
    (hform (glue root P i arrows) none).2 ⟨c, hc, hr.1⟩, hr.2⟩

/-- An existentially packaged pointed model. -/
structure AnyPointed (A G : Type u) where
  World : Type u
  model : Model World A G
  point : World

namespace AnyPointed

variable {A G : Type u}

def Satisfies (Q : AnyPointed A G) (φ : Formula A G) : Prop :=
  Q.model.Satisfies Q.point φ

end AnyPointed

/-- Lift one model of a heterogeneous family to the disjoint union of all
its world types.  Other components receive harmless self-loops, which makes
the lift serial whenever the selected model is serial. -/
def liftedModel {A G J : Type u} (Q : J → AnyPointed A G) (j : J) :
    Model (Σ k : J, (Q k).World) A G where
  rel a s t :=
    (∃ (x y : (Q j).World), s = ⟨j, x⟩ ∧ t = ⟨j, y⟩ ∧
      (Q j).model.rel a x y) ∨
    (s.1 ≠ j ∧ s = t)
  val p s :=
    ∃ x : (Q j).World, s = ⟨j, x⟩ ∧ (Q j).model.val p x

def liftedPointed {A G J : Type u} (Q : J → AnyPointed A G) (j : J) :
    Pointed (Σ k : J, (Q k).World) A G where
  model := liftedModel Q j
  point := ⟨j, (Q j).point⟩

theorem lifted_truth {A G J : Type u} (Q : J → AnyPointed A G)
    (j : J) (x : (Q j).World) (φ : Formula A G) :
    (liftedModel Q j).Satisfies ⟨j, x⟩ φ ↔
      (Q j).model.Satisfies x φ := by
  induction φ generalizing x with
  | atom p =>
      constructor
      · rintro ⟨y, hEq, hy⟩
        cases hEq
        exact hy
      · intro hx
        exact ⟨x, rfl, hx⟩
  | neg ψ ih => simpa [Model.Satisfies] using not_congr (ih x)
  | conj ψ χ ihψ ihχ =>
      simpa [Model.Satisfies] using and_congr (ihψ x) (ihχ x)
  | box a ψ ih =>
      constructor
      · intro h y hy
        apply (ih y).1
        apply h ⟨j, y⟩
        exact Or.inl ⟨x, y, rfl, rfl, hy⟩
      · intro h t ht
        rcases ht with ⟨x', y, hs, ht, hrel⟩ | ⟨hneq, _⟩
        · cases hs
          cases ht
          exact (ih y).2 (h y hrel)
        · exact (hneq rfl).elim

theorem lifted_serial {A G J : Type u} (Q : J → AnyPointed A G)
    (j : J) (i : G)
    (hserial : Frame.Serial ((Q j).model.rel i)) :
    Frame.Serial ((liftedModel Q j).rel i) := by
  intro s
  rcases s with ⟨k, x⟩
  by_cases hkj : k = j
  · subst k
    obtain ⟨y, hy⟩ := hserial x
    exact ⟨⟨j, y⟩, Or.inl ⟨x, y, rfl, rfl, hy⟩⟩
  · exact ⟨⟨k, x⟩, Or.inr ⟨hkj, rfl⟩⟩

theorem liftedPointed_truth {A G J : Type u} (Q : J → AnyPointed A G)
    (j : J) (φ : Formula A G) :
    (liftedPointed Q j).Satisfies φ ↔ (Q j).Satisfies φ :=
  lifted_truth Q j (Q j).point φ

/-- Full K converse to the clause criterion, allowing every successor
condition to be witnessed in a different Kripke model. -/
theorem sufficient_K {A G : Type u}
    (clauses : List (Clause A G)) (φ : Formula A G) (i : G)
    (hform : ∀ {V : Type u} (M : Model V A G) (x : V),
      M.Satisfies x φ ↔ Holds clauses M x i)
    (c : Clause A G) (hc : c ∈ clauses)
    (hα : SatisfiableK.{u} c.alpha)
    (hγ : ∀ γ ∈ c.diamonds, CompatibleK.{u} c.boxes [φ, γ]) :
    ∃ (V : Type u) (M : Model V A G) (x : V),
      M.Satisfies x φ ∧ M.Satisfies x (.box i φ) := by
  classical
  obtain ⟨Wα, Mα, xα, hxα⟩ := hα
  let Qα : AnyPointed A G := ⟨Wα, Mα, xα⟩
  have hγAny : ∀ γ ∈ c.diamonds, ∃ Q : AnyPointed A G,
      (∀ β ∈ c.boxes, Q.Satisfies β) ∧
      Q.Satisfies φ ∧ Q.Satisfies γ := by
    intro γ hmem
    obtain ⟨Wγ, Mγ, xγ, hB, hE⟩ := hγ γ hmem
    refine ⟨⟨Wγ, Mγ, xγ⟩, hB, ?_, ?_⟩
    · exact hE φ (by simp)
    · exact hE γ (by simp)
  let Q : Option (Formula A G) → AnyPointed A G := fun j =>
    match j with
    | none => Qα
    | some γ => if h : γ ∈ c.diamonds then Classical.choose (hγAny γ h) else Qα
  let V : Type u := Σ j : Option (Formula A G), (Q j).World
  let root : Pointed V A G := liftedPointed Q none
  have hroot : root.Satisfies c.alpha := by
    apply (liftedPointed_truth Q none c.alpha).2
    simpa [Q, Qα, AnyPointed.Satisfies] using hxα
  have hγCommon : ∀ γ ∈ c.diamonds, ∃ R : Pointed V A G,
      (∀ β ∈ c.boxes, R.Satisfies β) ∧
      R.Satisfies φ ∧ R.Satisfies γ := by
    intro γ hmem
    have hs := Classical.choose_spec (hγAny γ hmem)
    refine ⟨liftedPointed Q (some γ), ?_, ?_, ?_⟩
    · intro β hβ
      apply (liftedPointed_truth Q (some γ) β).2
      simpa [Q, hmem] using hs.1 β hβ
    · apply (liftedPointed_truth Q (some γ) φ).2
      simpa [Q, hmem] using hs.2.1
    · apply (liftedPointed_truth Q (some γ) γ).2
      simpa [Q, hmem] using hs.2.2
  exact sufficient_K_commonWorld clauses φ i hform c hc root hroot hγCommon

/-- Full KD converse to the clause criterion.  The extra base branch is the
serial successor required even when the disjunct has no diamonds. -/
theorem sufficient_KD {A G : Type u}
    (clauses : List (Clause A G)) (φ : Formula A G) (i : G)
    (hform : ∀ {V : Type u} (M : Model V A G) (x : V),
      M.Satisfies x φ ↔ Holds clauses M x i)
    (c : Clause A G) (hc : c ∈ clauses)
    (hα : SatisfiableKD.{u} i c.alpha)
    (hbase : CompatibleKD.{u} i c.boxes [φ])
    (hγ : ∀ γ ∈ c.diamonds, CompatibleKD.{u} i c.boxes [φ, γ]) :
    ∃ (V : Type u) (M : Model V A G) (x : V),
      Frame.Serial (M.rel i) ∧
      M.Satisfies x φ ∧ M.Satisfies x (.box i φ) := by
  classical
  obtain ⟨Wα, Mα, xα, _, hxα⟩ := hα
  let Qα : AnyPointed A G := ⟨Wα, Mα, xα⟩
  obtain ⟨Wbase, Mbase, xbase, hbserial, hBbase, hφbase⟩ := hbase
  let Qbase : AnyPointed A G := ⟨Wbase, Mbase, xbase⟩
  have hγAny : ∀ γ ∈ c.diamonds, ∃ Q : AnyPointed A G,
      Frame.Serial (Q.model.rel i) ∧
      (∀ β ∈ c.boxes, Q.Satisfies β) ∧
      Q.Satisfies φ ∧ Q.Satisfies γ := by
    intro γ hmem
    obtain ⟨Wγ, Mγ, xγ, hserial, hB, hE⟩ := hγ γ hmem
    refine ⟨⟨Wγ, Mγ, xγ⟩, hserial, hB, ?_, ?_⟩
    · exact hE φ (by simp)
    · exact hE γ (by simp)
  let Q : Option (Option (Formula A G)) → AnyPointed A G := fun j =>
    match j with
    | none => Qα
    | some none => Qbase
    | some (some γ) =>
        if h : γ ∈ c.diamonds then Classical.choose (hγAny γ h) else Qbase
  let V : Type u := Σ j : Option (Option (Formula A G)), (Q j).World
  let root : Pointed V A G := liftedPointed Q none
  let base : Pointed V A G := liftedPointed Q (some none)
  have hroot : root.Satisfies c.alpha := by
    apply (liftedPointed_truth Q none c.alpha).2
    simpa [Q, Qα, AnyPointed.Satisfies] using hxα
  have hbaseCommon : Frame.Serial (base.model.rel i) ∧
      (∀ β ∈ c.boxes, base.Satisfies β) ∧ base.Satisfies φ := by
    constructor
    · apply lifted_serial Q (some none) i
      simpa [Q, Qbase] using hbserial
    constructor
    · intro β hβ
      apply (liftedPointed_truth Q (some none) β).2
      simpa [Q, Qbase, AnyPointed.Satisfies] using hBbase β hβ
    · apply (liftedPointed_truth Q (some none) φ).2
      simpa [Q, Qbase, AnyPointed.Satisfies] using hφbase φ (by simp)
  have hγCommon : ∀ γ ∈ c.diamonds, ∃ R : Pointed V A G,
      Frame.Serial (R.model.rel i) ∧
      (∀ β ∈ c.boxes, R.Satisfies β) ∧
      R.Satisfies φ ∧ R.Satisfies γ := by
    intro γ hmem
    have hs := Classical.choose_spec (hγAny γ hmem)
    refine ⟨liftedPointed Q (some (some γ)), ?_, ?_, ?_, ?_⟩
    · apply lifted_serial Q (some (some γ)) i
      have hQ : Q (some (some γ)) = Classical.choose (hγAny γ hmem) := by
        dsimp [Q]
        exact dif_pos hmem
      rw [hQ]
      exact hs.1
    · intro β hβ
      apply (liftedPointed_truth Q (some (some γ)) β).2
      simpa [Q, hmem] using hs.2.1 β hβ
    · apply (liftedPointed_truth Q (some (some γ)) φ).2
      simpa [Q, hmem] using hs.2.2.1
    · apply (liftedPointed_truth Q (some (some γ)) γ).2
      simpa [Q, hmem] using hs.2.2.2
  exact sufficient_KD_commonWorld clauses φ i hform c hc root base
    hroot hbaseCommon hγCommon

/-- Theorem 2(1), stated as an exact K-knowability criterion for a given
finite DNF. -/
theorem knowable_K_iff {A G : Type u}
    (clauses : List (Clause A G)) (φ : Formula A G) (i : G)
    (hform : ∀ {V : Type u} (M : Model V A G) (x : V),
      M.Satisfies x φ ↔ Holds clauses M x i) :
    (∃ (V : Type u) (M : Model V A G) (x : V),
      M.Satisfies x φ ∧ M.Satisfies x (.box i φ)) ↔
    (∃ c ∈ clauses, SatisfiableK.{u} c.alpha ∧
      ∀ γ ∈ c.diamonds, CompatibleK.{u} c.boxes [φ, γ]) := by
  constructor
  · exact necessary_K clauses φ i hform
  · rintro ⟨c, hc, hα, hγ⟩
    exact sufficient_K clauses φ i hform c hc hα hγ

/-- Theorem 2(2), with seriality and its additional base-successor
condition. -/
theorem knowable_KD_iff {A G : Type u}
    (clauses : List (Clause A G)) (φ : Formula A G) (i : G)
    (hform : ∀ {V : Type u} (M : Model V A G) (x : V),
      M.Satisfies x φ ↔ Holds clauses M x i) :
    (∃ (V : Type u) (M : Model V A G) (x : V),
      Frame.Serial (M.rel i) ∧
      M.Satisfies x φ ∧ M.Satisfies x (.box i φ)) ↔
    (∃ c ∈ clauses, SatisfiableKD.{u} i c.alpha ∧
      CompatibleKD.{u} i c.boxes [φ] ∧
      ∀ γ ∈ c.diamonds, CompatibleKD.{u} i c.boxes [φ, γ]) := by
  constructor
  · exact necessary_KD clauses φ i hform
  · rintro ⟨c, hc, hα, hbase, hγ⟩
    exact sufficient_KD clauses φ i hform c hc hα hbase hγ

/-- Theorem 2(1) in the paper's negative, clause-by-clause form. -/
theorem unknowable_K_iff {A G : Type u}
    (clauses : List (Clause A G)) (φ : Formula A G) (i : G)
    (hform : ∀ {V : Type u} (M : Model V A G) (x : V),
      M.Satisfies x φ ↔ Holds clauses M x i) :
    (¬ ∃ (V : Type u) (M : Model V A G) (x : V),
      M.Satisfies x φ ∧ M.Satisfies x (.box i φ)) ↔
    (∀ c ∈ clauses, ¬ SatisfiableK.{u} c.alpha ∨
      ∃ γ ∈ c.diamonds, ¬ CompatibleK.{u} c.boxes [φ, γ]) := by
  classical
  rw [knowable_K_iff clauses φ i hform]
  constructor
  · intro h c hc
    by_cases hα : SatisfiableK.{u} c.alpha
    · right
      apply Classical.byContradiction
      intro hnone
      apply h
      refine ⟨c, hc, hα, ?_⟩
      intro γ hγ
      by_cases hgood : CompatibleK.{u} c.boxes [φ, γ]
      · exact hgood
      · exact False.elim (hnone ⟨γ, hγ, hgood⟩)
    · exact Or.inl hα
  · rintro h ⟨c, hc, hα, hγ⟩
    rcases h c hc with hbadα | ⟨γ, hmem, hbadγ⟩
    · exact hbadα hα
    · exact hbadγ (hγ γ hmem)

/-- Theorem 2(2) in the paper's negative, clause-by-clause form. -/
theorem unknowable_KD_iff {A G : Type u}
    (clauses : List (Clause A G)) (φ : Formula A G) (i : G)
    (hform : ∀ {V : Type u} (M : Model V A G) (x : V),
      M.Satisfies x φ ↔ Holds clauses M x i) :
    (¬ ∃ (V : Type u) (M : Model V A G) (x : V),
      Frame.Serial (M.rel i) ∧
      M.Satisfies x φ ∧ M.Satisfies x (.box i φ)) ↔
    (∀ c ∈ clauses, ¬ SatisfiableKD.{u} i c.alpha ∨
      ¬ CompatibleKD.{u} i c.boxes [φ] ∨
      ∃ γ ∈ c.diamonds, ¬ CompatibleKD.{u} i c.boxes [φ, γ]) := by
  classical
  rw [knowable_KD_iff clauses φ i hform]
  constructor
  · intro h c hc
    by_cases hα : SatisfiableKD.{u} i c.alpha
    · by_cases hbase : CompatibleKD.{u} i c.boxes [φ]
      · exact Or.inr (Or.inr (by
          apply Classical.byContradiction
          intro hnone
          apply h
          refine ⟨c, hc, hα, hbase, ?_⟩
          intro γ hγ
          by_cases hgood : CompatibleKD.{u} i c.boxes [φ, γ]
          · exact hgood
          · exact False.elim (hnone ⟨γ, hγ, hgood⟩)))
      · exact Or.inr (Or.inl hbase)
    · exact Or.inl hα
  · rintro h ⟨c, hc, hα, hbase, hγ⟩
    rcases h c hc with hbadα | hbadbase | ⟨γ, hmem, hbadγ⟩
    · exact hbadα hα
    · exact hbadbase hbase
    · exact hbadγ (hγ γ hmem)

end DNF
end SourcesOfUnknowability
