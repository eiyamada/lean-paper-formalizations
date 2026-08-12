import ClassificationSigmaValidity.Diagonal
import ClassificationSigmaValidity.FiniteModelProperty
import ClassificationSigmaValidity.Locality
import ClassificationSigmaValidity.NonexistenceK45S5
import ClassificationSigmaValidity.PatternLemmas
import ClassificationSigmaValidity.SingleAgentKD45
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Finset.Max
import Mathlib.Data.Prod.Lex

/-!
# Finite-depth KD45 unravelling

This file formalizes the finite cell unravelling used in the multi-agent KD45
part of the paper.  A world is a reverse history of agent-labelled transitions
in the original model.  Histories have length at most the chosen depth.  Below
maximum depth, changing agent creates a child cell while repeating the current
agent stays in the current cell.  At maximum depth all agents use the current
cell.  Thus related points have identical successor sets, which directly gives
transitivity and Euclideanness.

Three hypotheses which are implicit in the prose proof are explicit here:

* finiteness of the input countermodel (and of the finite agent group) is used
  to prove finiteness of the unravelling;
* depth zero is a separate singleton/universal-relation case;
* an inhabited agent group is required whenever a current cell has to be
  selected.
-/

namespace ClassificationSigmaValidity

universe u v w

namespace Unravelling

variable {BaseWorld : Type u} {Atom : Type v} {Agent : Type w}

/-- The original world named by a reverse history. -/
def label (root : BaseWorld) : List (Agent × BaseWorld) -> BaseWorld
  | [] => root
  | (_, x) :: _ => x

/-- A reverse history follows accessibility in the original model. -/
def PathValid (M : Model BaseWorld Atom Agent) (root : BaseWorld) :
    List (Agent × BaseWorld) -> Prop
  | [] => True
  | (i, x) :: tail => PathValid M root tail ∧ M.rel i (label root tail) x

/-- Histories of length at most `depth` which follow original arrows. -/
structure Path (M : Model BaseWorld Atom Agent) (root : BaseWorld)
    (depth : Nat) where
  history : List (Agent × BaseWorld)
  length_le : history.length ≤ depth
  valid : PathValid M root history

/-- The distinguished root history. -/
def rootPath (M : Model BaseWorld Atom Agent) (root : BaseWorld)
    (depth : Nat) : Path M root depth where
  history := []
  length_le := Nat.zero_le depth
  valid := trivial

/-- Rank is history length. -/
def Path.rank {M : Model BaseWorld Atom Agent} {root : BaseWorld}
    {depth : Nat} (x : Path M root depth) : Nat :=
  x.history.length

/-- Projection back to the original model. -/
def Path.label {M : Model BaseWorld Atom Agent} {root : BaseWorld}
    {depth : Nat} (x : Path M root depth) : BaseWorld :=
  Unravelling.label root x.history

@[simp] theorem rootPath_rank (M : Model BaseWorld Atom Agent)
    (root : BaseWorld) (depth : Nat) :
    (rootPath M root depth).rank = 0 := rfl

@[simp] theorem rootPath_label (M : Model BaseWorld Atom Agent)
    (root : BaseWorld) (depth : Nat) :
    (rootPath M root depth).label = root := rfl

theorem Path.rank_le {M : Model BaseWorld Atom Agent} {root : BaseWorld}
    {depth : Nat} (x : Path M root depth) : x.rank ≤ depth :=
  x.length_le

/-- The cell containing a nonroot history is determined by its last agent and
its parent history. -/
def Path.cell? {M : Model BaseWorld Atom Agent} {root : BaseWorld}
    {depth : Nat} (x : Path M root depth) :
    Option (Agent × List (Agent × BaseWorld)) :=
  match x.history with
  | [] => none
  | (i, _) :: tail => some (i, tail)

/-- The cell used by agent `i` at `x`.  This is called only at positive depth.
At the root it is the `i`-child cell.  At a nonterminal point it is the current
cell for the last agent and an `i`-child cell otherwise.  At terminal rank it
is always the current cell. -/
noncomputable def successorCell {M : Model BaseWorld Atom Agent} {root : BaseWorld}
    {depth : Nat} (i : Agent) (x : Path M root depth) :
    Agent × List (Agent × BaseWorld) := by
  classical
  exact match x.history with
    | [] => (i, [])
    | (j, y) :: tail =>
        if x.rank = depth then (j, tail)
        else if i = j then (j, tail)
        else (i, (j, y) :: tail)

/-- Accessibility of the finite-depth unravelling.  At depth zero there is
only the root and the universal relation supplies the required serial loop. -/
noncomputable def Related (M : Model BaseWorld Atom Agent) (root : BaseWorld)
    (depth : Nat) (i : Agent)
    (x y : Path M root depth) : Prop :=
  if depth = 0 then True else y.cell? = some (successorCell i x)

/-- The finite-depth unravelling model. -/
noncomputable def model (M : Model BaseWorld Atom Agent) (root : BaseWorld)
    (depth : Nat) :
    Model (Path M root depth) Atom Agent where
  rel := Related M root depth
  val p x := M.val p x.label

@[simp] theorem model_val (M : Model BaseWorld Atom Agent) (root : BaseWorld)
    (depth : Nat) (p : Atom) (x : Path M root depth) :
    (model M root depth).val p x ↔ M.val p x.label := Iff.rfl

@[simp] theorem model_rel (M : Model BaseWorld Atom Agent) (root : BaseWorld)
    (depth : Nat) (i : Agent) (x y : Path M root depth) :
    (model M root depth).rel i x y ↔ Related M root depth i x y := Iff.rfl

/-- With finite input worlds and agents, bounded histories form a finite type. -/
noncomputable instance instFinitePath [Finite BaseWorld] [Finite Agent]
    (M : Model BaseWorld Atom Agent) (root : BaseWorld) (depth : Nat) :
    Finite (Path M root depth) := by
  let bounded := {history : List (Agent × BaseWorld) // history.length ≤ depth}
  have hBounded : Finite bounded :=
    Set.finite_coe_iff.mpr (List.finite_length_le (Agent × BaseWorld) depth)
  letI : Finite bounded := hBounded
  exact Finite.of_injective
    (fun x : Path M root depth =>
      (⟨x.history, x.length_le⟩ : bounded))
    (by
      intro x y h
      cases x
      cases y
      simp only [Subtype.mk.injEq] at h
      subst h
      rfl)

/-- The depth-zero path type contains only the root. -/
theorem path_eq_root_of_depth_zero {M : Model BaseWorld Atom Agent}
    {root : BaseWorld} (x : Path M root 0) : x = rootPath M root 0 := by
  cases x with
  | mk history length_le valid =>
      have : history = [] := List.length_eq_zero_iff.mp
        (Nat.eq_zero_of_le_zero length_le)
      subst history
      rfl

@[simp] theorem related_depth_zero (M : Model BaseWorld Atom Agent)
    (root : BaseWorld) (i : Agent) (x y : Path M root 0) :
    Related M root 0 i x y := by
  simp [Related]

theorem related_iff_cell {M : Model BaseWorld Atom Agent}
    {root : BaseWorld} {depth : Nat} (hdepth : 0 < depth)
    (i : Agent) (x y : Path M root depth) :
    Related M root depth i x y ↔
      y.cell? = some (successorCell i x) := by
  simp [Related, Nat.ne_of_gt hdepth]

/-- Along an unravelling arrow, source and target select the same successor
cell for that agent. -/
theorem successorCell_eq_of_related {M : Model BaseWorld Atom Agent}
    {root : BaseWorld} {depth : Nat} (hdepth : 0 < depth)
    (i : Agent) {x y : Path M root depth}
    (hxy : Related M root depth i x y) :
    successorCell i y = successorCell i x := by
  classical
  rw [related_iff_cell hdepth] at hxy
  cases hx : x.history with
  | nil =>
      cases hy : y.history with
      | nil => simp [Path.cell?, hy] at hxy
      | cons head tail =>
          rcases head with ⟨j, z⟩
          simp [Path.cell?, successorCell, hx, hy] at hxy
          rcases hxy with ⟨rfl, rfl⟩
          simp [successorCell, hx, hy, Path.rank]
  | cons head tail =>
      rcases head with ⟨j, z⟩
      cases hy : y.history with
      | nil => simp [Path.cell?, hy] at hxy
      | cons head' tail' =>
          rcases head' with ⟨j', z'⟩
          simp only [Path.cell?, hy, Option.some.injEq] at hxy
          by_cases hterminal : x.rank = depth
          · have hkey : successorCell i x = (j, tail) := by
              simp [successorCell, hx, hterminal]
            rw [hkey] at hxy
            rcases hxy with ⟨rfl, rfl⟩
            have hyTerminal : y.rank = depth := by
              simpa [Path.rank, hx, hy] using hterminal
            simp [successorCell, hx, hy, hterminal, hyTerminal]
          · by_cases hij : i = j
            · have hkey : successorCell i x = (j, tail) := by
                simp [successorCell, hx, hterminal, hij]
              rw [hkey] at hxy
              rcases hxy with ⟨rfl, rfl⟩
              have hyNotTerminal : y.rank ≠ depth := by
                simpa [Path.rank, hx, hy] using hterminal
              simp [successorCell, hx, hy, hterminal, hyNotTerminal, hij]
            · have hkey : successorCell i x = (i, (j, z) :: tail) := by
                simp [successorCell, hx, hterminal, hij]
              rw [hkey] at hxy
              rcases hxy with ⟨rfl, rfl⟩
              rw [hkey]
              simp [successorCell, hy]

/-- The successor set selected by a cell is nonempty when the original model
is serial. -/
theorem exists_related {M : Model BaseWorld Atom Agent} (hM : IsKD45 M)
    (root : BaseWorld) (depth : Nat) (i : Agent)
    (x : Path M root depth) :
    ∃ y, Related M root depth i x y := by
  classical
  by_cases hdepth : depth = 0
  · subst depth
    exact ⟨rootPath M root 0, related_depth_zero M root i x _⟩
  have hdepthPos : 0 < depth := Nat.pos_of_ne_zero hdepth
  cases x with
  | mk history length_le valid =>
      cases history with
      | nil =>
          obtain ⟨y, hy⟩ := (hM i).1 root
          let next : Path M root depth :=
            ⟨[(i, y)], by simpa using hdepthPos, by simpa [PathValid] using hy⟩
          refine ⟨next, (related_iff_cell hdepthPos i _ next).mpr ?_⟩
          simp [next, Path.cell?, successorCell]
      | cons head tail =>
          rcases head with ⟨j, z⟩
          have hvalid : PathValid M root tail ∧ M.rel j (label root tail) z :=
            valid
          by_cases hterminal : tail.length + 1 = depth
          · obtain ⟨y, hy⟩ := (hM j).1 (label root tail)
            let next : Path M root depth :=
              ⟨(j, y) :: tail, by simpa using length_le,
                by exact ⟨hvalid.1, hy⟩⟩
            refine ⟨next, (related_iff_cell hdepthPos i _ next).mpr ?_⟩
            simp [next, Path.cell?, successorCell, Path.rank, hterminal]
          · by_cases hij : i = j
            · obtain ⟨y, hy⟩ := (hM j).1 (label root tail)
              let next : Path M root depth :=
                ⟨(j, y) :: tail, by simpa using length_le,
                  by exact ⟨hvalid.1, hy⟩⟩
              refine ⟨next, (related_iff_cell hdepthPos i _ next).mpr ?_⟩
              simp [next, Path.cell?, successorCell, Path.rank, hterminal, hij]
            · obtain ⟨y, hy⟩ := (hM i).1 z
              have hlt : tail.length + 1 < depth :=
                Nat.lt_of_le_of_ne length_le hterminal
              let next : Path M root depth :=
                ⟨(i, y) :: (j, z) :: tail, by simpa using hlt,
                  by exact ⟨hvalid, hy⟩⟩
              refine ⟨next, (related_iff_cell hdepthPos i _ next).mpr ?_⟩
              simp [next, Path.cell?, successorCell, Path.rank, hterminal, hij]

/-- The unravelling relation is serial. -/
theorem model_serial {M : Model BaseWorld Atom Agent} (hM : IsKD45 M)
    (root : BaseWorld) (depth : Nat) (i : Agent) :
    Frame.Serial ((model M root depth).rel i) := by
  intro x
  exact exists_related hM root depth i x

/-- Equal successor cells make the unravelling relation transitive. -/
theorem model_transitive (M : Model BaseWorld Atom Agent)
    (root : BaseWorld) (depth : Nat) (i : Agent) :
    Frame.Transitive ((model M root depth).rel i) := by
  intro x y z hxy hyz
  by_cases hdepth : depth = 0
  · subst depth
    exact related_depth_zero M root i x z
  have hdepthPos := Nat.pos_of_ne_zero hdepth
  have hcell := successorCell_eq_of_related hdepthPos i hxy
  rw [model_rel, related_iff_cell hdepthPos] at hxy hyz ⊢
  rw [hcell] at hyz
  exact hyz

/-- Equal successor cells make the unravelling relation Euclidean. -/
theorem model_euclidean (M : Model BaseWorld Atom Agent)
    (root : BaseWorld) (depth : Nat) (i : Agent) :
    Frame.Euclidean ((model M root depth).rel i) := by
  intro x y z hxy hxz
  by_cases hdepth : depth = 0
  · subst depth
    exact related_depth_zero M root i y z
  have hdepthPos := Nat.pos_of_ne_zero hdepth
  have hcell := successorCell_eq_of_related hdepthPos i hxy
  rw [model_rel, related_iff_cell hdepthPos] at hxy hxz ⊢
  rw [hcell]
  exact hxz

/-- The finite-depth unravelling of a KD45 model is KD45. -/
theorem model_isKD45 {M : Model BaseWorld Atom Agent} (hM : IsKD45 M)
    (root : BaseWorld) (depth : Nat) : IsKD45 (model M root depth) := by
  intro i
  exact ⟨model_serial hM root depth i,
    model_transitive M root depth i, model_euclidean M root depth i⟩

/-- The same construction preserves the K45 part without using seriality. -/
theorem model_isK45 (M : Model BaseWorld Atom Agent)
    (root : BaseWorld) (depth : Nat) : IsK45 (model M root depth) := by
  intro i
  exact ⟨model_transitive M root depth i, model_euclidean M root depth i⟩

/-- Before terminal rank, every unravelling arrow projects to an original
arrow with the same agent. -/
theorem related_projects {M : Model BaseWorld Atom Agent} (hM : IsK45 M)
    {root : BaseWorld} {depth : Nat} {i : Agent}
    {x y : Path M root depth} (hx : x.rank < depth)
    (hxy : Related M root depth i x y) :
    M.rel i x.label y.label := by
  classical
  have hdepth : 0 < depth := Nat.zero_lt_of_lt hx
  rw [related_iff_cell hdepth] at hxy
  cases hxhist : x.history with
  | nil =>
      cases hyhist : y.history with
      | nil => simp [Path.cell?, hyhist] at hxy
      | cons head tail =>
          rcases head with ⟨j, z⟩
          simp [Path.cell?, successorCell, hxhist, hyhist] at hxy
          rcases hxy with ⟨rfl, rfl⟩
          have hyValid := y.valid
          rw [hyhist] at hyValid
          simpa [Path.label, hxhist, hyhist] using hyValid.2
  | cons head tail =>
      rcases head with ⟨j, z⟩
      have hxNotTerminal : tail.length + 1 ≠ depth := by
        simpa [Path.rank, hxhist] using ne_of_lt hx
      cases hyhist : y.history with
      | nil => simp [Path.cell?, hyhist] at hxy
      | cons head' tail' =>
          rcases head' with ⟨j', z'⟩
          by_cases hij : i = j
          · simp [Path.cell?, successorCell, hxhist, hyhist,
              Path.rank, hxNotTerminal, hij] at hxy
            rcases hxy with ⟨rfl, rfl⟩
            have hxValid := x.valid
            have hyValid := y.valid
            rw [hxhist] at hxValid
            rw [hyhist] at hyValid
            have hxParent : M.rel i (label root tail') z := by
              simpa [hij] using hxValid.2
            have hyParent : M.rel i (label root tail') z' := by
              simpa [hij] using hyValid.2
            have hprofile := Frame.successor_eq_of_transitive_euclidean
              (R := M.rel i) (x := label root tail') (y := z)
              (hM i).1 (hM i).2 hxParent z'
            have hproject := hprofile.mp hyParent
            simpa [Path.label, hxhist, hyhist] using hproject
          · simp [Path.cell?, successorCell, hxhist, hyhist,
              Path.rank, hxNotTerminal, hij] at hxy
            rcases hxy with ⟨rfl, rfl⟩
            have hyValid := y.valid
            rw [hyhist] at hyValid
            simpa [Path.label, hxhist, hyhist] using hyValid.2

/-- An unravelling arrow increases rank by at most one. -/
theorem rank_le_succ_of_related {M : Model BaseWorld Atom Agent}
    {root : BaseWorld} {depth : Nat} {i : Agent}
    {x y : Path M root depth} (hxy : Related M root depth i x y) :
    y.rank ≤ x.rank + 1 := by
  classical
  by_cases hdepth : depth = 0
  · subst depth
    rw [path_eq_root_of_depth_zero x, path_eq_root_of_depth_zero y]
    simp
  have hdepthPos := Nat.pos_of_ne_zero hdepth
  rw [related_iff_cell hdepthPos] at hxy
  cases hx : x.history with
  | nil =>
      cases hy : y.history with
      | nil => simp [Path.cell?, hy] at hxy
      | cons head tail =>
          rcases head with ⟨j, z⟩
          simp [Path.cell?, successorCell, hx, hy] at hxy
          rcases hxy with ⟨rfl, rfl⟩
          simp [Path.rank, hx, hy]
  | cons head tail =>
      rcases head with ⟨j, z⟩
      cases hy : y.history with
      | nil => simp [Path.cell?, hy] at hxy
      | cons head' tail' =>
          rcases head' with ⟨j', z'⟩
          simp only [Path.cell?, hy, Option.some.injEq] at hxy
          by_cases hterminal : x.rank = depth
          · have hkey : successorCell i x = (j, tail) := by
              simp [successorCell, hx, hterminal]
            rw [hkey] at hxy
            rcases hxy with ⟨rfl, rfl⟩
            simp [Path.rank, hx, hy]
          · by_cases hij : i = j
            · have hkey : successorCell i x = (j, tail) := by
                simp [successorCell, hx, hterminal, hij]
              rw [hkey] at hxy
              rcases hxy with ⟨rfl, rfl⟩
              simp [Path.rank, hx, hy]
            · have hkey : successorCell i x = (i, (j, z) :: tail) := by
                simp [successorCell, hx, hterminal, hij]
              rw [hkey] at hxy
              rcases hxy with ⟨rfl, rfl⟩
              simp [Path.rank, hx, hy]

/-- Every original successor of a nonterminal history has a matching
unravelling successor with the same label. -/
theorem exists_related_label {M : Model BaseWorld Atom Agent} (hM : IsK45 M)
    {root : BaseWorld} {depth : Nat} (i : Agent)
    (x : Path M root depth) (hx : x.rank < depth)
    (y : BaseWorld) (hxy : M.rel i x.label y) :
    ∃ z : Path M root depth,
      Related M root depth i x z ∧ z.label = y := by
  classical
  have hdepth : 0 < depth := Nat.zero_lt_of_lt hx
  cases x with
  | mk history length_le valid =>
      cases history with
      | nil =>
          let z : Path M root depth :=
            ⟨[(i, y)], by simpa using hx, by simpa [PathValid] using hxy⟩
          refine ⟨z, (related_iff_cell hdepth i _ z).mpr ?_, rfl⟩
          simp [z, Path.cell?, successorCell]
      | cons head tail =>
          rcases head with ⟨j, v⟩
          have hvalid : PathValid M root tail ∧ M.rel j (label root tail) v :=
            valid
          have hnotTerminal : tail.length + 1 ≠ depth := by
            simpa [Path.rank] using ne_of_lt hx
          by_cases hij : i = j
          · subst i
            have hyParent : M.rel j (label root tail) y :=
              (hM j).1 hvalid.2 hxy
            let z : Path M root depth :=
              ⟨(j, y) :: tail, by simpa using length_le,
                by exact ⟨hvalid.1, hyParent⟩⟩
            refine ⟨z, (related_iff_cell hdepth j _ z).mpr ?_, rfl⟩
            simp [z, Path.cell?, successorCell, Path.rank, hnotTerminal]
          · let z : Path M root depth :=
              ⟨(i, y) :: (j, v) :: tail, by simpa using hx,
                by exact ⟨hvalid, hxy⟩⟩
            refine ⟨z, (related_iff_cell hdepth i _ z).mpr ?_, rfl⟩
            simp [z, Path.cell?, successorCell, Path.rank, hnotTerminal, hij]

/-- Bounded modal truth lemma.  A formula is preserved at a history whenever
its modal depth fits in the remaining unravelling depth. -/
theorem satisfies_iff (M : Model BaseWorld Atom Agent) (hM : IsK45 M)
    (root : BaseWorld) (depth : Nat) (x : Path M root depth)
    (psi : Formula Atom Agent)
    (hbudget : x.rank + psi.modalDepth ≤ depth) :
    (model M root depth).Satisfies x psi ↔ M.Satisfies x.label psi := by
  induction psi generalizing x with
  | atom p => rfl
  | neg psi ih =>
      exact not_congr (ih x hbudget)
  | conj psi chi ihPsi ihChi =>
      simp only [Formula.modalDepth] at hbudget
      have hPsi : x.rank + psi.modalDepth ≤ depth := by omega
      have hChi : x.rank + chi.modalDepth ≤ depth := by omega
      exact and_congr (ihPsi x hPsi) (ihChi x hChi)
  | box i psi ih =>
      simp only [Formula.modalDepth] at hbudget
      have hx : x.rank < depth := by omega
      simp only [Model.satisfies_box]
      constructor
      · intro h y hxy
        obtain ⟨z, hxz, rfl⟩ := exists_related_label hM i x hx y hxy
        have hzRank := rank_le_succ_of_related hxz
        have hzBudget : z.rank + psi.modalDepth ≤ depth := by omega
        exact (ih z hzBudget).mp (h z hxz)
      · intro h z hxz
        have hzRank := rank_le_succ_of_related hxz
        have hzBudget : z.rank + psi.modalDepth ≤ depth := by omega
        apply (ih z hzBudget).mpr
        exact h z.label (related_projects hM hx hxz)

/-- The distinguished root agrees with the source model on every formula of
modal depth at most the chosen unravelling depth. -/
theorem root_satisfies_iff (M : Model BaseWorld Atom Agent) (hM : IsK45 M)
    (root : BaseWorld) (depth : Nat) (psi : Formula Atom Agent)
    (hdepth : psi.modalDepth ≤ depth) :
    (model M root depth).Satisfies (rootPath M root depth) psi ↔
      M.Satisfies root psi := by
  exact satisfies_iff M hM root depth (rootPath M root depth) psi (by
    simpa using hdepth)

/-- In particular the unravelling at exactly the formula's modal depth
preserves that formula, including the modal-depth-zero case. -/
theorem root_satisfies_target_iff
    (M : Model BaseWorld Atom Agent) (hM : IsK45 M)
    (root : BaseWorld) (phi : Formula Atom Agent) :
    (model M root phi.modalDepth).Satisfies
        (rootPath M root phi.modalDepth) phi ↔
      M.Satisfies root phi := by
  exact root_satisfies_iff M hM root phi.modalDepth phi (by rfl)

/-! ## Terminal cells and diagonal behavior -/

/-- The terminal cell containing a positive-rank history. -/
def terminalCell {M : Model BaseWorld Atom Agent} {root : BaseWorld}
    {depth : Nat} (x : Path M root depth) : Set (Path M root depth) :=
  {y | y.cell? = x.cell?}

theorem terminalCell_cell {M : Model BaseWorld Atom Agent}
    {root : BaseWorld} {depth : Nat} {x y : Path M root depth}
    (hy : y ∈ terminalCell x) : y.cell? = x.cell? := hy

theorem rank_eq_of_same_cell {M : Model BaseWorld Atom Agent}
    {root : BaseWorld} {depth : Nat} {x y : Path M root depth}
    (hxNonroot : x.history ≠ []) (hy : y.cell? = x.cell?) :
    y.rank = x.rank := by
  cases hxHist : x.history with
  | nil => exact (hxNonroot hxHist).elim
  | cons head tail =>
      rcases head with ⟨j, v⟩
      cases hyHist : y.history with
      | nil =>
          simp [Path.cell?, hxHist, hyHist] at hy
      | cons head' tail' =>
          rcases head' with ⟨j', v'⟩
          simp [Path.cell?, hxHist, hyHist] at hy
          rcases hy with ⟨rfl, rfl⟩
          simp [Path.rank, hxHist, hyHist]

theorem successorCell_eq_cell_of_terminal
    {M : Model BaseWorld Atom Agent} {root : BaseWorld} {depth : Nat}
    (x y : Path M root depth) (hxTerminal : x.rank = depth)
    (hxNonroot : x.history ≠ []) (hy : y ∈ terminalCell x)
    (i : Agent) : some (successorCell i y) = x.cell? := by
  have hyCell : y.cell? = x.cell? := hy
  have hyRank : y.rank = depth :=
    (rank_eq_of_same_cell hxNonroot hyCell).trans hxTerminal
  cases hyHist : y.history with
  | nil =>
      have : y.cell? = none := by simp [Path.cell?, hyHist]
      rw [this] at hyCell
      cases hxHist : x.history with
      | nil => exact (hxNonroot hxHist).elim
      | cons head tail => simp [Path.cell?, hxHist] at hyCell
  | cons head tail =>
      rcases head with ⟨j, v⟩
      simp [successorCell, hyHist, hyRank]
      simpa [Path.cell?, hyHist] using hyCell

theorem terminalCell_forwardClosed {M : Model BaseWorld Atom Agent}
    {root : BaseWorld} {depth : Nat} (hdepth : 0 < depth)
    (x : Path M root depth) (hxTerminal : x.rank = depth)
    (hxNonroot : x.history ≠ []) :
    (model M root depth).ForwardClosed (terminalCell x) := by
  intro y hy i z hyz
  rw [model_rel, related_iff_cell hdepth] at hyz
  have hcell := successorCell_eq_cell_of_terminal
    x y hxTerminal hxNonroot hy i
  exact hyz.trans hcell

/-- At terminal rank, every agent's internal relation on the terminal cell is
the universal relation on that cell. -/
theorem terminalCell_rel_iff {M : Model BaseWorld Atom Agent}
    {root : BaseWorld} {depth : Nat} (hdepth : 0 < depth)
    (x : Path M root depth) (hxTerminal : x.rank = depth)
    (hxNonroot : x.history ≠ []) (i : Agent)
    (y z : Subtype (terminalCell x)) :
    ((model M root depth).restrict (terminalCell x)).rel i y z := by
  rw [Model.restrict_rel, model_rel, related_iff_cell hdepth]
  have hySucc := successorCell_eq_cell_of_terminal
    x y.1 hxTerminal hxNonroot y.2 i
  exact z.2.trans hySucc.symm

/-- The single-agent universal model carried by a terminal cell. -/
noncomputable def terminalDiagonal {M : Model BaseWorld Atom Agent}
    {root : BaseWorld} {depth : Nat} (x : Path M root depth) :
    Model (Subtype (terminalCell x)) Atom Unit where
  rel _ _ _ := True
  val p y := (model M root depth).val p y.1

theorem terminalDiagonal_isKD45 {M : Model BaseWorld Atom Agent}
    {root : BaseWorld} {depth : Nat} (x : Path M root depth) :
    IsKD45 (terminalDiagonal x) := by
  intro _
  exact ⟨fun y => ⟨y, trivial⟩,
    (by intro x y z hxy hyz; trivial),
    (by intro x y z hxy hxz; trivial)⟩

/-- The terminal-cell restriction is exactly the diagonal expansion of its
single-agent universal model. -/
theorem restrict_terminalCell_eq_diagonalExpansion
    {M : Model BaseWorld Atom Agent} {root : BaseWorld} {depth : Nat}
    (hdepth : 0 < depth) (x : Path M root depth)
    (hxTerminal : x.rank = depth) (hxNonroot : x.history ≠ []) :
    (model M root depth).restrict (terminalCell x) =
      (terminalDiagonal x).diagonalExpansion Agent := by
  apply Model.ext'
  · intro i y z
    constructor <;> intro _
    · trivial
    · exact terminalCell_rel_iff hdepth x hxTerminal hxNonroot i y z
  · intro p y
    rfl

/-- If the diagonal is valid on single-agent KD45, the formula is true at
every world of a terminal cell. -/
theorem terminalCell_satisfies_of_diagonal_valid
    {M : Model BaseWorld Atom Agent} {root : BaseWorld} {depth : Nat}
    (hdepth : 0 < depth) (x : Path M root depth)
    (hxTerminal : x.rank = depth) (hxNonroot : x.history ≠ [])
    (phi : Formula Atom Agent)
    (hvalid : ∀ {World : Type max u w} (P : Model World Atom Unit),
      IsKD45 P -> ∀ z, P.Satisfies z phi.diagonal) :
    ∀ y : Subtype (terminalCell x),
      ((model M root depth).restrict (terminalCell x)).Satisfies y phi := by
  intro y
  rw [restrict_terminalCell_eq_diagonalExpansion hdepth x hxTerminal hxNonroot]
  exact ((terminalDiagonal x).diagonalExpansion_satisfies_iff
    Agent y phi).mpr (hvalid (terminalDiagonal x)
      (terminalDiagonal_isKD45 x) y)

/-- Once the announcement is true throughout a forward-closed terminal cell,
all local arrows are retained and every further iterate is locally unchanged.
This is the update/locality form of paper Lemma
`lem:diagonal_model_equivalence` (2). -/
theorem terminal_satisfies_all_iterates_of_diagonal_valid
    {M : Model BaseWorld Atom Agent} {root : BaseWorld} {depth : Nat}
    (hdepth : 0 < depth) (x : Path M root depth)
    (hxTerminal : x.rank = depth) (hxNonroot : x.history ≠ [])
    (phi : Formula Atom Agent)
    (hvalid : ∀ {World : Type max u w} (P : Model World Atom Unit),
      IsKD45 P -> ∀ z, P.Satisfies z phi.diagonal) :
    ∀ n, ((model M root depth).iterateUpdate phi n).Satisfies x phi := by
  have hclosed : (model M root depth).ForwardClosed (terminalCell x) :=
    terminalCell_forwardClosed hdepth x hxTerminal hxNonroot
  let xCell : Subtype (terminalCell x) := ⟨x, rfl⟩
  have hall : ∀ y : Subtype (terminalCell x),
      ((model M root depth).restrict (terminalCell x)).Satisfies y phi :=
    terminalCell_satisfies_of_diagonal_valid
      hdepth x hxTerminal hxNonroot phi hvalid
  have hupdate : ((model M root depth).restrict (terminalCell x)).update phi =
      (model M root depth).restrict (terminalCell x) := by
    apply Model.ext'
    · intro i y z
      simp only [Model.update_rel]
      exact and_iff_left (hall z)
    · intro p y
      rfl
  intro n
  have hlocal :
      Model.Satisfies
        (((model M root depth).restrict (terminalCell x)).iterateUpdate phi n)
        xCell phi := by
    have hmodels : ∀ n,
        ((model M root depth).restrict (terminalCell x)).iterateUpdate phi n =
          (model M root depth).restrict (terminalCell x) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
          rw [Model.iterateUpdate_succ, ih, hupdate]
    rw [hmodels n]
    exact hall xCell
  have hcommute := (model M root depth).restrict_iterateUpdate_eq
    (terminalCell x) hclosed phi n
  have hrestricted :
      (((model M root depth).iterateUpdate phi n).restrict
        (terminalCell x)).Satisfies xCell phi := by
    exact (Model.satisfies_congr hcommute.symm xCell phi).mp hlocal
  have hclosedLater : ((model M root depth).iterateUpdate phi n).ForwardClosed
      (terminalCell x) :=
    Model.forwardClosed_iterateUpdate hclosed phi n
  exact (((model M root depth).iterateUpdate phi n).restrict_satisfies_iff
    (terminalCell x) hclosedLater xCell phi).mp hrestricted

/-! ## Validity transfer to the diagonal -/

/-- Multi-agent KD45 pattern-validity transfers to the diagonal single-agent
formula because expanding any single-agent KD45 model duplicates its sole
relation for all agents and preserves the entire update trace. -/
theorem diagonal_realizes_of_kd45_valid [Nonempty Agent]
    (phi : Formula Atom Agent) (sigma : Pattern)
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      phi sigma)
    {World : Type u} (P : Model World Atom Unit) (hP : IsKD45 P)
    (x : World) (hx : Pattern.HoldsBit sigma.first
      (P.trace x phi.diagonal 0)) :
    Sigma.Realizes P x phi.diagonal sigma := by
  have hExpanded := hvalid (P.diagonalExpansion Agent)
    (P.diagonalExpansion_isKD45 hP Agent) x
  have hxExpanded : Pattern.HoldsBit sigma.first
      ((P.diagonalExpansion Agent).trace x phi 0) := by
    cases hfirst : sigma.first <;>
      simpa [hfirst, Pattern.HoldsBit,
        P.diagonalExpansion_trace_iff Agent phi x 0] using hx
  have hreal := hExpanded hxExpanded
  cases sigma with
  | finite bits hlen =>
      intro n hn
      have hnBit := hreal n hn
      cases hbit : bits[n] <;>
        simpa [hbit, Pattern.HoldsBit,
          P.diagonalExpansion_trace_iff Agent phi x n] using hnBit
  | infinite bits =>
      intro n
      have hnBit := hreal n
      cases hbit : bits n <;>
        simpa [hbit, Pattern.HoldsBit,
          P.diagonalExpansion_trace_iff Agent phi x n] using hnBit

/-- `00` is a prefix of `0^k1` for `k ≥ 2`. -/
theorem zeroZero_prefix_zerosOne (k : Nat) (hk : 2 ≤ k) :
    Pattern.zeroZero.IsPrefix (Pattern.zerosOne k hk) := by
  change [false, false] <+: List.replicate k false ++ [true]
  cases k with
  | zero => omega
  | succ k =>
      cases k with
      | zero => omega
      | succ k => simp [List.replicate_succ]

/-- Multi-agent KD45 `0^k1` validity makes the diagonal formula valid on every
single-agent KD45 model.  Transfer gives `0^k1`; its `00` prefix collapses to
`0^ω`, while `0^k1` itself demands truth at time `k`. -/
theorem diagonal_true_of_kd45_valid_zerosOne [Nonempty Agent]
    (phi : Formula Atom Agent) (k : Nat) (hk : 2 ≤ k)
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      phi (Pattern.zerosOne k hk)) :
    ∀ {World : Type u} (P : Model World Atom Unit),
      IsKD45 P -> ∀ x, P.Satisfies x phi.diagonal := by
  have h00 : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Unit) : FrameClass.{u} Atom Unit)
      phi.diagonal Pattern.zeroZero := by
    intro World P hP x hx
    have hx' : Pattern.HoldsBit (Pattern.zerosOne k hk).first
        (P.trace x phi.diagonal 0) := by
      simpa only [Pattern.first_zerosOne, Pattern.zeroZero,
        Pattern.first_bits2] using hx
    exact Pattern.realizesTrace_mono_of_prefix
      (zeroZero_prefix_zerosOne k hk)
      (diagonal_realizes_of_kd45_valid phi (Pattern.zerosOne k hk)
        hvalid P hP x hx')
  intro World P hP x
  by_contra hxFalse
  have hstart : Pattern.HoldsBit (Pattern.zerosOne k hk).first
      (P.trace x phi.diagonal 0) := by
    simpa [Pattern.HoldsBit, Model.trace] using hxFalse
  have hfinite := diagonal_realizes_of_kd45_valid
    phi (Pattern.zerosOne k hk) hvalid P hP x hstart
  have hlastTrue := (Pattern.realizesTrace_zerosOne_last hk hfinite).2
  have hfalseAll : ∀ n, ¬(P.iterateUpdate phi.diagonal n).Satisfies x
      phi.diagonal := by
    intro n
    induction n with
    | zero => exact hxFalse
    | succ n ih =>
        exact (P.iterateUpdate phi.diagonal n).singleAgent_false_persists
          (P.iterateUpdate_isK45 hP.isK45 phi.diagonal n)
          phi.diagonal h00 x ih
  have hfalseK : ¬P.trace x phi.diagonal k := by
    simpa [Model.trace] using hfalseAll k
  exact hfalseK hlastTrue

/-- Multi-agent KD45 `01^k0` validity makes the diagonal formula valid, by the
single-agent KD45 nonexistence theorem. -/
theorem diagonal_true_of_kd45_valid_zeroOnesZero [Nonempty Agent]
    (phi : Formula Atom Agent) (k : Nat) (hk : 1 ≤ k)
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      phi (Pattern.zeroOnesZero k hk)) :
    ∀ {World : Type u} (P : Model World Atom Unit),
      IsKD45 P -> ∀ x, P.Satisfies x phi.diagonal := by
  intro World P hP x
  have hDiagonal : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Unit) : FrameClass.{u} Atom Unit)
      phi.diagonal (Pattern.zeroOnesZero k hk) := by
    intro World Q hQ y hy
    exact diagonal_realizes_of_kd45_valid
      phi (Pattern.zeroOnesZero k hk) hvalid Q hQ y hy
  exact Nonexistence.single_kd45_valid_zeroOnesZero_true
    phi.diagonal k hk hDiagonal P hP x

/-- Paper Lemma `lem:diagonal_model_equivalence` (2), specialized to a
`0^k1`-valid announcement. -/
theorem terminal_satisfies_all_iterates_of_valid_zerosOne
    [Nonempty Agent]
    {M : Model BaseWorld Atom Agent} {root : BaseWorld} {depth : Nat}
    (hdepth : 0 < depth) (x : Path M root depth)
    (hxTerminal : x.rank = depth) (hxNonroot : x.history ≠ [])
    (phi : Formula Atom Agent) (k : Nat) (hk : 2 ≤ k)
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) :
        FrameClass.{max u w} Atom Agent)
      phi (Pattern.zerosOne k hk)) :
    ∀ n, ((model M root depth).iterateUpdate phi n).Satisfies x phi := by
  apply terminal_satisfies_all_iterates_of_diagonal_valid
    hdepth x hxTerminal hxNonroot phi
  exact diagonal_true_of_kd45_valid_zerosOne
    phi k hk hvalid

/-- Paper Lemma `lem:diagonal_model_equivalence` (2), specialized to a
`01^k0`-valid announcement. -/
theorem terminal_satisfies_all_iterates_of_valid_zeroOnesZero
    [Nonempty Agent]
    {M : Model BaseWorld Atom Agent} {root : BaseWorld} {depth : Nat}
    (hdepth : 0 < depth) (x : Path M root depth)
    (hxTerminal : x.rank = depth) (hxNonroot : x.history ≠ [])
    (phi : Formula Atom Agent) (k : Nat) (hk : 1 ≤ k)
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) :
        FrameClass.{max u w} Atom Agent)
      phi (Pattern.zeroOnesZero k hk)) :
    ∀ n, ((model M root depth).iterateUpdate phi n).Satisfies x phi := by
  apply terminal_satisfies_all_iterates_of_diagonal_valid
    hdepth x hxTerminal hxNonroot phi
  exact diagonal_true_of_kd45_valid_zeroOnesZero
    phi k hk hvalid

/-! ## The finite KD45 descent -/

/-- A world which survives to time `n` belongs to the generated region at
itself at time `n`. -/
def generatedAtPoint (M : Model BaseWorld Atom Agent) (phi : Formula Atom Agent)
    (n : Nat) (x : BaseWorld) :
    Subtype ((M.iterateUpdate phi n).generatedSet x) :=
  (M.iterateUpdate phi n).generatedPoint x

/-- Local iteration in the generated model at time `n` agrees with the global
run at time `n + m`. -/
theorem generated_shift_satisfies_iff
    (M : Model BaseWorld Atom Agent) (phi : Formula Atom Agent)
    (n m : Nat) (x : BaseWorld) (psi : Formula Atom Agent) :
    (((M.iterateUpdate phi n).generatedSubmodel x).iterateUpdate phi m).Satisfies
        (generatedAtPoint M phi n x) psi ↔
      (M.iterateUpdate phi (n + m)).Satisfies x psi := by
  have hlocal := (M.iterateUpdate phi n).restrict_iterateUpdate_shift_satisfies_iff
    ((M.iterateUpdate phi n).generatedSet x) phi 0 m
    ((M.iterateUpdate phi n).generatedSet_forwardClosed x)
    (generatedAtPoint M phi n x) psi
  rw [Nat.zero_add] at hlocal
  exact hlocal.trans
    (Model.satisfies_congr (M.iterateUpdate_add phi n m).symm x psi)

/-- A successor in a nonterminal child cell has strictly larger rank unless it
lies in the source's current cell. -/
theorem rank_eq_or_rank_succ_of_related
    {M : Model BaseWorld Atom Agent} {root : BaseWorld} {depth : Nat}
    (hdepth : 0 < depth) {i : Agent} {x y : Path M root depth}
    (hx : x.rank < depth) (hxy : Related M root depth i x y) :
    y.rank = x.rank ∨ y.rank = x.rank + 1 := by
  classical
  rw [related_iff_cell hdepth] at hxy
  cases hxhist : x.history with
  | nil =>
      cases hyhist : y.history with
      | nil => simp [Path.cell?, hyhist] at hxy
      | cons head tail =>
          rcases head with ⟨j, z⟩
          simp [Path.cell?, successorCell, hxhist, hyhist] at hxy
          rcases hxy with ⟨rfl, rfl⟩
          right
          simp [Path.rank, hxhist, hyhist]
  | cons head tail =>
      rcases head with ⟨j, z⟩
      have hxNotTerminal : x.rank ≠ depth := ne_of_lt hx
      cases hyhist : y.history with
      | nil => simp [Path.cell?, hyhist] at hxy
      | cons head' tail' =>
          rcases head' with ⟨j', z'⟩
          by_cases hij : i = j
          · have hkey : successorCell i x = (j, tail) := by
              simp [successorCell, hxhist, hxNotTerminal, hij]
            rw [hkey] at hxy
            simp [Path.cell?, hyhist] at hxy
            rcases hxy with ⟨rfl, rfl⟩
            left
            simp [Path.rank, hxhist, hyhist]
          · have hkey : successorCell i x = (i, (j, z) :: tail) := by
              simp [successorCell, hxhist, hxNotTerminal, hij]
            rw [hkey] at hxy
            simp [Path.cell?, hyhist] at hxy
            rcases hxy with ⟨rfl, rfl⟩
            right
            simp [Path.rank, hxhist, hyhist]

/-- At a nonroot, nonterminal world, the only arrows which do not increase
rank are precisely the arrows into its current cell. -/
theorem rank_eq_iff_same_cell_of_related
    {M : Model BaseWorld Atom Agent} {root : BaseWorld} {depth : Nat}
    (hdepth : 0 < depth) {i : Agent} {x y : Path M root depth}
    (hxNonroot : x.history ≠ []) (hx : x.rank < depth)
    (hxy : Related M root depth i x y) :
    y.rank = x.rank ↔ y.cell? = x.cell? := by
  classical
  cases hxhist : x.history with
  | nil => exact (hxNonroot hxhist).elim
  | cons head tail =>
      rcases head with ⟨j, z⟩
      have hxNotTerminal : x.rank ≠ depth := ne_of_lt hx
      rw [related_iff_cell hdepth] at hxy
      cases hyhist : y.history with
      | nil => simp [Path.cell?, hyhist] at hxy
      | cons head' tail' =>
          rcases head' with ⟨j', z'⟩
          by_cases hij : i = j
          · have hkey : successorCell i x = (j, tail) := by
              simp [successorCell, hxhist, hxNotTerminal, hij]
            rw [hkey] at hxy
            simp [Path.cell?, hyhist] at hxy
            rcases hxy with ⟨rfl, rfl⟩
            simp [Path.rank, Path.cell?, hxhist, hyhist]
          · have hkey : successorCell i x = (i, (j, z) :: tail) := by
              simp [successorCell, hxhist, hxNotTerminal, hij]
            rw [hkey] at hxy
            simp [Path.cell?, hyhist] at hxy
            rcases hxy with ⟨rfl, rfl⟩
            simp [Path.rank, Path.cell?, hxhist, hyhist]

/-- Unravelling arrows never decrease rank. -/
theorem rank_le_of_related
    {M : Model BaseWorld Atom Agent} {root : BaseWorld} {depth : Nat}
    (hdepth : 0 < depth) {i : Agent} {x y : Path M root depth}
    (hxy : Related M root depth i x y) : x.rank ≤ y.rank := by
  by_cases hxTerminal : x.rank = depth
  · have hxNonroot : x.history ≠ [] := by
      intro hxRoot
      have : x.rank = 0 := by simp [Path.rank, hxRoot]
      omega
    have hyCell : y.cell? = x.cell? := by
      rw [related_iff_cell hdepth] at hxy
      exact hxy.trans (successorCell_eq_cell_of_terminal
        x x hxTerminal hxNonroot rfl i)
    exact (rank_eq_of_same_cell hxNonroot hyCell).ge
  · have hxLt : x.rank < depth := Nat.lt_of_le_of_ne x.rank_le hxTerminal
    rcases rank_eq_or_rank_succ_of_related hdepth hxLt hxy with h | h <;> omega
/-- Reachability from a nonroot, nonterminal point never decreases rank. -/
theorem rank_le_of_reachable
    {M : Model BaseWorld Atom Agent} {root : BaseWorld} {depth : Nat}
    (hdepth : 0 < depth) {x y : Path M root depth}
    (hreach : (model M root depth).Reachable x y) : x.rank ≤ y.rank := by
  have hAll : ∀ {z : Path M root depth},
      (model M root depth).Reachable x z → x.rank ≤ z.rank ∧ z.rank ≤ depth := by
    intro z hz
    induction hz with
    | refl => exact ⟨Nat.le_refl _, x.rank_le⟩
    | @tail a z hreach haz ih =>
        rcases haz with ⟨i, haz⟩
        change Related M root depth i a z at haz
        by_cases haTerminal : a.rank = depth
        · have hzRank : z.rank = depth := by
            rw [related_iff_cell hdepth] at haz
            cases haHist : a.history with
            | nil => simp [Path.rank, haHist] at haTerminal; omega
            | cons head tail =>
                rcases head with ⟨j, q⟩
                cases hzHist : z.history with
                | nil => simp [Path.cell?, hzHist] at haz
                | cons head' tail' =>
                    rcases head' with ⟨j', q'⟩
                    have hkey : successorCell i a = (j, tail) := by
                      simp [successorCell, haHist, haTerminal]
                    rw [hkey] at haz
                    simp [Path.cell?, hzHist] at haz
                    rcases haz with ⟨rfl, rfl⟩
                    simpa [Path.rank, haHist, hzHist] using haTerminal
          exact ⟨by omega, by omega⟩
        · have haLt : a.rank < depth :=
            Nat.lt_of_le_of_ne ih.2 haTerminal
          have hcases := rank_eq_or_rank_succ_of_related hdepth haLt haz
          exact ⟨by omega, z.rank_le⟩
  exact (hAll hreach).1

/-- `firstFalse N phi x` is the least stage at which `phi` is false at `x`.
It is only used together with a proof that such a stage exists. -/
noncomputable def firstFalse (N : Model BaseWorld Atom Agent)
    (phi : Formula Atom Agent) (x : BaseWorld) : Nat := by
  classical
  exact if h : ∃ n, ¬(N.iterateUpdate phi n).Satisfies x phi then Nat.find h else 0

theorem firstFalse_spec (N : Model BaseWorld Atom Agent)
    (phi : Formula Atom Agent) (x : BaseWorld)
    (h : ∃ n, ¬(N.iterateUpdate phi n).Satisfies x phi) :
    ¬(N.iterateUpdate phi (firstFalse N phi x)).Satisfies x phi := by
  classical
  simp only [firstFalse, dif_pos h]
  exact Nat.find_spec h

theorem satisfies_before_firstFalse (N : Model BaseWorld Atom Agent)
    (phi : Formula Atom Agent) (x : BaseWorld)
    (h : ∃ n, ¬(N.iterateUpdate phi n).Satisfies x phi)
    {m : Nat} (hm : m < firstFalse N phi x) :
    (N.iterateUpdate phi m).Satisfies x phi := by
  by_contra hfalse
  have hle : firstFalse N phi x ≤ m := by
    classical
    simp only [firstFalse, dif_pos h]
    exact Nat.find_min' h hfalse
  omega

theorem survives_firstFalse (N : Model BaseWorld Atom Agent)
    (phi : Formula Atom Agent) (x : BaseWorld)
    (h : ∃ n, ¬(N.iterateUpdate phi n).Satisfies x phi) :
    N.Survives phi (firstFalse N phi x) x := by
  intro m hm
  exact satisfies_before_firstFalse N phi x h hm

/-- Finite choice of a world whose `(rank, first-false time)` is
lexicographically maximal among all worlds that ever become false. -/
theorem exists_maximal_firstFalse [Finite BaseWorld]
    (N : Model BaseWorld Atom Agent) (phi : Formula Atom Agent)
    (rank : BaseWorld → Nat)
    (hne : ∃ x n, ¬(N.iterateUpdate phi n).Satisfies x phi) :
    ∃ x,
      (∃ n, ¬(N.iterateUpdate phi n).Satisfies x phi) ∧
      ∀ y, (∃ n, ¬(N.iterateUpdate phi n).Satisfies y phi) →
        toLex (rank y, firstFalse N phi y) ≤
          toLex (rank x, firstFalse N phi x) := by
  classical
  letI := Fintype.ofFinite BaseWorld
  let S : Finset BaseWorld := Finset.univ.filter fun x =>
    ∃ n, ¬(N.iterateUpdate phi n).Satisfies x phi
  have hS : S.Nonempty := by
    obtain ⟨x, n, hx⟩ := hne
    refine ⟨x, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨n, hx⟩
  obtain ⟨x, hxS, hxMax⟩ := Finset.exists_max_image S
    (fun y => toLex (rank y, firstFalse N phi y)) hS
  refine ⟨x, ?_, ?_⟩
  · simpa [S] using hxS
  · intro y hy
    exact hxMax y (by simpa [S] using hy)

/-- The lexicographic maximality criterion supplies both rank maximality and,
at equal rank, maximal first-false time. -/
theorem maximal_firstFalse_rank
    {N : Model BaseWorld Atom Agent} {phi : Formula Atom Agent}
    {rank : BaseWorld → Nat} {x : BaseWorld}
    (hmax : ∀ y, (∃ n, ¬(N.iterateUpdate phi n).Satisfies y phi) →
      toLex (rank y, firstFalse N phi y) ≤
        toLex (rank x, firstFalse N phi x))
    {y : BaseWorld} (hy : ∃ n, ¬(N.iterateUpdate phi n).Satisfies y phi) :
    rank y ≤ rank x := by
  have hlex := hmax y hy
  rw [Prod.Lex.toLex_le_toLex] at hlex
  omega

theorem maximal_firstFalse_time_of_rank_eq
    {N : Model BaseWorld Atom Agent} {phi : Formula Atom Agent}
    {rank : BaseWorld → Nat} {x : BaseWorld}
    (hmax : ∀ y, (∃ n, ¬(N.iterateUpdate phi n).Satisfies y phi) →
      toLex (rank y, firstFalse N phi y) ≤
        toLex (rank x, firstFalse N phi x))
    {y : BaseWorld} (hy : ∃ n, ¬(N.iterateUpdate phi n).Satisfies y phi)
    (hrank : rank y = rank x) :
    firstFalse N phi y ≤ firstFalse N phi x := by
  have hlex := hmax y hy
  rw [Prod.Lex.toLex_le_toLex] at hlex
  rcases hlex with hlt | ⟨heq, htime⟩
  · omega
  · exact htime

/-- A world strictly above the maximal ever-false rank is true at every
iterate, hence survives every update. -/
theorem survives_all_of_rank_gt_maximal
    {N : Model BaseWorld Atom Agent} {phi : Formula Atom Agent}
    {rank : BaseWorld → Nat} {x y : BaseWorld}
    (hmax : ∀ z, (∃ n, ¬(N.iterateUpdate phi n).Satisfies z phi) →
      toLex (rank z, firstFalse N phi z) ≤
        toLex (rank x, firstFalse N phi x))
    (hrank : rank x < rank y) : ∀ n, N.Survives phi n y := by
  intro n m hm
  by_contra hy
  have hle := maximal_firstFalse_rank hmax ⟨m, hy⟩
  omega

/-- Reachability can only decrease when arrows are removed by updates. -/
theorem reachable_of_iterateUpdate_reachable
    (N : Model BaseWorld Atom Agent) (phi : Formula Atom Agent) (q : Nat)
    {x y : BaseWorld}
    (hreach : (N.iterateUpdate phi q).Reachable x y) : N.Reachable x y := by
  induction hreach with
  | refl => exact N.reachable_refl x
  | @tail a y hreach hay ih =>
      rcases hay with ⟨i, hay⟩
      exact ih.tail i ((N.iterateUpdate_rel_iff phi q i a y).mp hay).1

/-- If a nonroot, nonterminal history reaches another history at the same rank,
the whole route stayed inside its current cell. -/
theorem cell_eq_of_reachable_of_rank_eq
    {M : Model BaseWorld Atom Agent} {root : BaseWorld} {depth : Nat}
    (hdepth : 0 < depth) {x y : Path M root depth}
    (hxNonroot : x.history ≠ []) (hxLt : x.rank < depth)
    (hreach : (model M root depth).Reachable x y)
    (hrank : y.rank = x.rank) : y.cell? = x.cell? := by
  induction hreach with
  | refl => rfl
  | @tail a y hreach hay ih =>
      rcases hay with ⟨i, hay⟩
      change Related M root depth i a y at hay
      have hxa : x.rank ≤ a.rank := rank_le_of_reachable hdepth hreach
      have hayReach : (model M root depth).Reachable a y :=
        (model M root depth).reachable_refl a |>.tail i hay
      have hayRank : a.rank ≤ y.rank :=
        rank_le_of_reachable hdepth hayReach
      have haRank : a.rank = x.rank := by omega
      have haNonroot : a.history ≠ [] := by
        intro ha
        have haZero : a.rank = 0 := by simp [Path.rank, ha]
        have hxZero : x.rank = 0 := by omega
        have : x.history = [] := List.length_eq_zero_iff.mp hxZero
        exact hxNonroot this
      have haLt : a.rank < depth := by omega
      have hcellAY : y.cell? = a.cell? :=
        (rank_eq_iff_same_cell_of_related hdepth haNonroot haLt hay).mp
          (by omega)
      exact hcellAY.trans (ih haRank)

/-- At a maximal-rank world which is about to become false, the generated
model at that stage is still KD45. -/
theorem generatedSubmodel_isKD45_at_maximal_rank
    {M : Model BaseWorld Atom Agent} (hM : IsKD45 M)
    {root : BaseWorld} {depth q : Nat} (hdepth : 0 < depth)
    (phi : Formula Atom Agent) {x : Path M root depth}
    (hxNonroot : x.history ≠ []) (hxLt : x.rank < depth)
    (hxSurvives : (model M root depth).Survives phi q x)
    (hxMax : ∀ y : Path M root depth,
      (∃ n, ¬((model M root depth).iterateUpdate phi n).Satisfies y phi) →
      y.rank ≤ x.rank) :
    IsKD45
      (((model M root depth).iterateUpdate phi q).generatedSubmodel x) := by
  let N := model M root depth
  have hK45 : IsK45 (N.iterateUpdate phi q) :=
    Model.iterateUpdate_isK45 (model_isK45 M root depth) phi q
  have hGeneratedK45 :
      IsK45 ((N.iterateUpdate phi q).generatedSubmodel x) :=
    (N.iterateUpdate phi q).generatedSubmodel_isK45 hK45 x
  intro i
  refine ⟨?_, (hGeneratedK45 i).1, (hGeneratedK45 i).2⟩
  intro y
  obtain ⟨z, hyz⟩ := exists_related hM root depth i y.1
  have hxyBase : N.Reachable x y.1 :=
    reachable_of_iterateUpdate_reachable N phi q y.property
  have hxzBase : N.Reachable x z := hxyBase.tail i hyz
  have hxleZ : x.rank ≤ z.rank := rank_le_of_reachable hdepth hxzBase
  by_cases hzRank : z.rank = x.rank
  · have hxyRank : y.1.rank = x.rank := by
      have hxleY : x.rank ≤ y.1.rank := rank_le_of_reachable hdepth hxyBase
      have hyzReach : N.Reachable y.1 z := N.reachable_refl y.1 |>.tail i hyz
      have hyleZ : y.1.rank ≤ z.rank := rank_le_of_reachable hdepth hyzReach
      omega
    have hyNonroot : y.1.history ≠ [] := by
      intro hy
      have hyZero : y.1.rank = 0 := by simp [Path.rank, hy]
      have hxZero : x.rank = 0 := by omega
      exact hxNonroot (List.length_eq_zero_iff.mp hxZero)
    have hyLt : y.1.rank < depth := by omega
    have hcellYX : y.1.cell? = x.cell? :=
      cell_eq_of_reachable_of_rank_eq hdepth hxNonroot hxLt hxyBase hxyRank
    have hcellZY : z.cell? = y.1.cell? :=
      (rank_eq_iff_same_cell_of_related hdepth hyNonroot hyLt hyz).mp
        (by omega)
    have hyx : N.rel i y.1 x := by
      change Related M root depth i y.1 x
      rw [related_iff_cell hdepth]
      exact hcellYX.symm.trans (hcellZY.symm.trans
        ((related_iff_cell hdepth i y.1 z).mp hyz))
    have hyxQ : (N.iterateUpdate phi q).rel i y.1 x :=
      (N.iterateUpdate_rel_iff phi q i y.1 x).mpr ⟨hyx, hxSurvives⟩
    let xG : Subtype ((N.iterateUpdate phi q).generatedSet x) :=
      (N.iterateUpdate phi q).generatedPoint x
    exact ⟨xG, hyxQ⟩
  · have hxltZ : x.rank < z.rank := lt_of_le_of_ne hxleZ (Ne.symm hzRank)
    have hzNever : ∀ n, (N.iterateUpdate phi n).Satisfies z phi := by
      intro n
      by_contra hzFalse
      have := hxMax z ⟨n, hzFalse⟩
      omega
    have hzSurvives : N.Survives phi q z := by
      intro n hn
      exact hzNever n
    have hyzQ : (N.iterateUpdate phi q).rel i y.1 z :=
      (N.iterateUpdate_rel_iff phi q i y.1 z).mpr ⟨hyz, hzSurvives⟩
    let zG : Subtype ((N.iterateUpdate phi q).generatedSet x) :=
      ⟨z, y.property.tail i hyzQ⟩
    exact ⟨zG, hyzQ⟩

/-- The distinguished root cannot be maximal among ever-false worlds: every
proper successor would then be true forever, leaving the root's generated
model unchanged after the first update. -/
theorem maximal_everFalse_nonroot
    [Nonempty Agent]
    {M : Model BaseWorld Atom Agent} (hM : IsKD45 M)
    {root : BaseWorld} {depth : Nat} (hdepth : 0 < depth)
    (phi : Formula Atom Agent) (x : Path M root depth)
    (hxFalse : ∃ n, ¬((model M root depth).iterateUpdate phi n).Satisfies x phi)
    (hxMax : ∀ y : Path M root depth,
      (∃ n, ¬((model M root depth).iterateUpdate phi n).Satisfies y phi) →
      y.rank ≤ x.rank)
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) :
        FrameClass.{max u w} Atom Agent)
      phi Pattern.zeroOne) : x.history ≠ [] := by
  intro hxRoot
  have hxRank : x.rank = 0 := by simp [Path.rank, hxRoot]
  let N := model M root depth
  have hproperNever : ∀ y : Path M root depth, y ≠ x →
      ∀ n, (N.iterateUpdate phi n).Satisfies y phi := by
    intro y hy n
    by_contra hyFalse
    have hyrank := hxMax y ⟨n, hyFalse⟩
    have hyZero : y.rank = 0 := by omega
    have hyHist : y.history = [] := List.length_eq_zero_iff.mp hyZero
    apply hy
    cases y
    cases x
    simp_all
  have hrelStable : N.update phi = N := by
    apply Model.ext'
    · intro i y z
      simp only [Model.update_rel]
      constructor
      · exact fun h => h.1
      · intro hyz
        refine ⟨hyz, ?_⟩
        have hzNe : z ≠ x := by
          intro hzx
          subst z
          change Related M root depth i y x at hyz
          rw [related_iff_cell hdepth] at hyz
          simp [Path.cell?, hxRoot] at hyz
        exact hproperNever z hzNe 0
    · intro p y
      rfl
  have hfalse0 : ¬N.Satisfies x phi := by
    by_contra htrue
    have hall : ∀ n, (N.iterateUpdate phi n).Satisfies x phi := by
      intro n
      have hiter : N.iterateUpdate phi n = N := by
        induction n with
        | zero => rfl
        | succ n ih => rw [Model.iterateUpdate_succ, ih, hrelStable]
      exact (Model.satisfies_congr hiter x phi).mpr htrue
    obtain ⟨n, hn⟩ := hxFalse
    exact hn (hall n)
  have hstart : Pattern.HoldsBit Pattern.zeroOne.first (N.trace x phi 0) := by
    simpa [Pattern.zeroOne, Pattern.HoldsBit, Model.trace] using hfalse0
  have hreal := hvalid N (model_isKD45 hM root depth) x hstart
  have htrue1 := (Pattern.realizesTrace_bits2.mp hreal).2
  have hfalse1 : ¬(N.update phi).Satisfies x phi := by
    exact fun ht => hfalse0 ((Model.satisfies_congr hrelStable x phi).mp ht)
  simpa [Model.trace] using hfalse1 htrue1

/-- A lexicographically maximal ever-false world is not terminal when the
announcement is `0^k1`-valid. -/
theorem maximal_everFalse_nonterminal_zerosOne
    [Nonempty Agent]
    {M : Model BaseWorld Atom Agent}
    {root : BaseWorld} {depth : Nat} (hdepth : 0 < depth)
    (phi : Formula Atom Agent) (k : Nat) (hk : 2 ≤ k)
    (x : Path M root depth)
    (hxFalse : ∃ n, ¬((model M root depth).iterateUpdate phi n).Satisfies x phi)
    (hxNonroot : x.history ≠ [])
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) :
        FrameClass.{max u w} Atom Agent)
      phi (Pattern.zerosOne k hk)) : x.rank < depth := by
  have hle := x.rank_le
  apply lt_of_le_of_ne hle
  intro hxTerminal
  have hall := terminal_satisfies_all_iterates_of_valid_zerosOne
    hdepth x hxTerminal hxNonroot phi k hk hvalid
  obtain ⟨n, hn⟩ := hxFalse
  exact hn (hall n)

/-- The analogous terminal exclusion for `01^k0`. -/
theorem maximal_everFalse_nonterminal_zeroOnesZero
    [Nonempty Agent]
    {M : Model BaseWorld Atom Agent}
    {root : BaseWorld} {depth : Nat} (hdepth : 0 < depth)
    (phi : Formula Atom Agent) (k : Nat) (hk : 1 ≤ k)
    (x : Path M root depth)
    (hxFalse : ∃ n, ¬((model M root depth).iterateUpdate phi n).Satisfies x phi)
    (hxNonroot : x.history ≠ [])
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) :
        FrameClass.{max u w} Atom Agent)
      phi (Pattern.zeroOnesZero k hk)) : x.rank < depth := by
  have hle := x.rank_le
  apply lt_of_le_of_ne hle
  intro hxTerminal
  have hall := terminal_satisfies_all_iterates_of_valid_zeroOnesZero
    hdepth x hxTerminal hxNonroot phi k hk hvalid
  obtain ⟨n, hn⟩ := hxFalse
  exact hn (hall n)

/-- Finite unravelling contradiction for a `0^k1`-valid announcement. -/
theorem finite_unravelling_valid_zerosOne_true
    [Finite BaseWorld] [Finite Agent] [Nonempty Agent]
    {M : Model BaseWorld Atom Agent} (hM : IsKD45 M)
    (root : BaseWorld) (phi : Formula Atom Agent)
    (k : Nat) (hk : 2 ≤ k)
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) :
        FrameClass.{max u w} Atom Agent)
      phi (Pattern.zerosOne k hk)) :
    (model M root phi.modalDepth).Satisfies
      (rootPath M root phi.modalDepth) phi := by
  by_cases hdepth0 : phi.modalDepth = 0
  · by_contra hfalse
    have hstable := (model M root phi.modalDepth).trace_iff_of_modalDepth_eq_zero
      (rootPath M root phi.modalDepth) phi hdepth0 k
    have hstart : Pattern.HoldsBit (Pattern.zerosOne k hk).first
        ((model M root phi.modalDepth).trace
          (rootPath M root phi.modalDepth) phi 0) := by
      simpa [Pattern.HoldsBit, Model.trace] using hfalse
    have hreal := hvalid (model M root phi.modalDepth)
      (model_isKD45 hM root phi.modalDepth) _ hstart
    have htrueK := (Pattern.realizesTrace_zerosOne_last hk hreal).2
    exact hfalse (by
      change (model M root phi.modalDepth).trace
        (rootPath M root phi.modalDepth) phi 0
      exact hstable.mp htrueK)
  · let N := model M root phi.modalDepth
    let r := rootPath M root phi.modalDepth
    by_contra hrFalse
    have hdepth : 0 < phi.modalDepth := Nat.pos_of_ne_zero hdepth0
    have hne : ∃ y n, ¬(N.iterateUpdate phi n).Satisfies y phi :=
      ⟨r, 0, by simpa [N, r] using hrFalse⟩
    obtain ⟨x, hxFalse, hmax⟩ := exists_maximal_firstFalse
      N phi (fun y => y.rank) hne
    let q := firstFalse N phi x
    have hxRankMax : ∀ y, (∃ n, ¬(N.iterateUpdate phi n).Satisfies y phi) →
        y.rank ≤ x.rank := fun y hy => maximal_firstFalse_rank hmax hy
    have hxNonroot : x.history ≠ [] := by
      intro hxRoot
      have hxRank : x.rank = 0 := by simp [Path.rank, hxRoot]
      have hproperNever : ∀ y : Path M root phi.modalDepth, y ≠ x →
          ∀ n, (N.iterateUpdate phi n).Satisfies y phi := by
        intro y hy n
        by_contra hyFalse
        have hyrank := hxRankMax y ⟨n, hyFalse⟩
        have hyZero : y.rank = 0 := by omega
        have hyHist : y.history = [] := List.length_eq_zero_iff.mp hyZero
        apply hy
        cases y
        cases x
        simp_all
      have hrelStable : N.update phi = N := by
        apply Model.ext'
        · intro i y z
          simp only [Model.update_rel]
          constructor
          · exact fun h => h.1
          · intro hyz
            refine ⟨hyz, ?_⟩
            have hzNe : z ≠ x := by
              intro hzx
              subst z
              change Related M root phi.modalDepth i y x at hyz
              rw [related_iff_cell hdepth] at hyz
              simp [Path.cell?, hxRoot] at hyz
            exact hproperNever z hzNe 0
        · intro p y; rfl
      have hfalse0 : ¬N.Satisfies x phi := by
        by_contra htrue
        have hall : ∀ n, (N.iterateUpdate phi n).Satisfies x phi := by
          intro n
          have hiter : N.iterateUpdate phi n = N := by
            induction n with
            | zero => rfl
            | succ n ih => rw [Model.iterateUpdate_succ, ih, hrelStable]
          exact (Model.satisfies_congr hiter x phi).mpr htrue
        obtain ⟨n, hn⟩ := hxFalse
        exact hn (hall n)
      have hstartRoot : Pattern.HoldsBit (Pattern.zerosOne k hk).first
          (N.trace x phi 0) := by
        simpa [Pattern.HoldsBit, Model.trace] using hfalse0
      have hrealRoot := hvalid N (model_isKD45 hM root phi.modalDepth)
        x hstartRoot
      have htrueK := (Pattern.realizesTrace_zerosOne_last hk hrealRoot).2
      have hfalseK : ¬N.trace x phi k := by
        have hiter : N.iterateUpdate phi k = N := by
          have hallIter : ∀ m, N.iterateUpdate phi m = N := by
            intro m
            induction m with
            | zero => rfl
            | succ n ih => rw [Model.iterateUpdate_succ, ih, hrelStable]
          exact hallIter k
        exact fun ht => hfalse0 ((Model.satisfies_congr hiter x phi).mp ht)
      exact hfalseK htrueK
    have hxLt : x.rank < phi.modalDepth :=
      maximal_everFalse_nonterminal_zerosOne hdepth phi k hk x hxFalse
        hxNonroot hvalid
    have hxSurv : N.Survives phi q x :=
      survives_firstFalse N phi x hxFalse
    have hlocalKD45 : IsKD45 ((N.iterateUpdate phi q).generatedSubmodel x) :=
      generatedSubmodel_isKD45_at_maximal_rank hM hdepth phi hxNonroot hxLt
        hxSurv hxRankMax
    have hxFalseQ : ¬(N.iterateUpdate phi q).Satisfies x phi :=
      firstFalse_spec N phi x hxFalse
    let xG := (N.iterateUpdate phi q).generatedPoint x
    have hxLocalFalse : ¬((N.iterateUpdate phi q).generatedSubmodel x).Satisfies
        xG phi := by
      exact fun ht => hxFalseQ
        (((N.iterateUpdate phi q).generatedSubmodel_root_satisfies_iff x phi).mp ht)
    have hstart : Pattern.HoldsBit (Pattern.zerosOne k hk).first
        (((N.iterateUpdate phi q).generatedSubmodel x).trace xG phi 0) := by
      simpa [Pattern.HoldsBit, Model.trace] using hxLocalFalse
    have hrealQ := hvalid ((N.iterateUpdate phi q).generatedSubmodel x)
      hlocalKD45 xG hstart
    have hendsQ := Pattern.realizesTrace_zerosOne_last hk hrealQ
    have hfalseQ1 : ¬(N.iterateUpdate phi (q + 1)).Satisfies x phi := by
      have hlocal := hrealQ 1 (by simp; omega)
      have hlocalFalse :
          ¬Model.Satisfies
            (((N.iterateUpdate phi q).generatedSubmodel x).iterateUpdate phi 1)
            xG phi := by
        have hnot : ¬k ≤ 1 := by omega
        simpa [Pattern.HoldsBit, List.getElem_append,
          List.getElem_replicate, hnot] using hlocal
      exact fun ht => hlocalFalse
        ((generated_shift_satisfies_iff N phi q 1 x phi).mpr (by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht))
    let G1 := (N.iterateUpdate phi (q + 1)).generatedSubmodel x
    let xG1 := (N.iterateUpdate phi (q + 1)).generatedPoint x
    have htargetsTrue : ∀ (i : Agent) (y z : Subtype
        ((N.iterateUpdate phi (q + 1)).generatedSet x)),
        G1.rel i y z → G1.Satisfies z phi := by
      intro i y z hyz
      apply ((N.iterateUpdate phi (q + 1)).generatedSubmodel_satisfies_iff
        x z phi).mpr
      have hzReachNow : (N.iterateUpdate phi (q + 1)).Reachable x z.1 := z.2
      have hzReach : N.Reachable x z.1 :=
        reachable_of_iterateUpdate_reachable N phi (q + 1) hzReachNow
      have hxle : x.rank ≤ z.1.rank := rank_le_of_reachable hdepth hzReach
      by_cases hzEver : ∃ n, ¬(N.iterateUpdate phi n).Satisfies z.1 phi
      · have hzRankLe := hxRankMax z.1 hzEver
        have hzRank : z.1.rank = x.rank := by omega
        have hzTime := maximal_firstFalse_time_of_rank_eq hmax hzEver hzRank
        have hzSurvQ1 : N.Survives phi (q + 1) z.1 :=
          (N.iterateUpdate_rel_iff phi (q + 1) i y.1 z.1).mp hyz |>.2
        have hzTrueAtFirst :
            (N.iterateUpdate phi (firstFalse N phi z.1)).Satisfies z.1 phi :=
          hzSurvQ1 _ (by dsimp [q] at hzTime ⊢; omega)
        exact (firstFalse_spec N phi z.1 hzEver hzTrueAtFirst).elim
      · push_neg at hzEver
        exact hzEver (q + 1)
    have hG1Update : G1.update phi = G1 := by
      apply Model.ext'
      · intro i y z
        simp only [Model.update_rel]
        constructor
        · exact fun h => h.1
        · intro hyz
          exact ⟨hyz, htargetsTrue i y z hyz⟩
      · intro p y; rfl
    have hG1Iter : ∀ n, G1.iterateUpdate phi n = G1 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          calc
            G1.iterateUpdate phi (n + 1) =
                (G1.iterateUpdate phi n).update phi := rfl
            _ = G1.update phi := congrArg (fun P => P.update phi) ih
            _ = G1 := hG1Update
    have hxLocalFalse1 : ¬G1.Satisfies xG1 phi := by
      exact fun ht => hfalseQ1
        (((N.iterateUpdate phi (q + 1)).generatedSubmodel_root_satisfies_iff
          x phi).mp ht)
    have hfalseAtQK : ¬(N.iterateUpdate phi (q + k)).Satisfies x phi := by
      have hlocalFalse : ¬(G1.iterateUpdate phi (k - 1)).Satisfies xG1 phi := by
        rw [hG1Iter (k - 1)]
        exact hxLocalFalse1
      have hshift := (generated_shift_satisfies_iff N phi (q + 1)
        (k - 1) x phi).not.mp hlocalFalse
      simpa only [Nat.add_assoc, Nat.add_sub_of_le (by omega : 1 ≤ k)] using hshift
    exact hfalseAtQK
      ((generated_shift_satisfies_iff N phi q k x phi).mp hendsQ.2)

/-- Finite unravelling contradiction for a `01^k0`-valid announcement. -/
theorem finite_unravelling_valid_zeroOnesZero_true
    [Finite BaseWorld] [Finite Agent] [Nonempty Agent]
    {M : Model BaseWorld Atom Agent} (hM : IsKD45 M)
    (root : BaseWorld) (phi : Formula Atom Agent)
    (k : Nat) (hk : 1 ≤ k)
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) :
        FrameClass.{max u w} Atom Agent)
      phi (Pattern.zeroOnesZero k hk)) :
    (model M root phi.modalDepth).Satisfies
      (rootPath M root phi.modalDepth) phi := by
  by_cases hdepth0 : phi.modalDepth = 0
  · by_contra hfalse
    have hstable := (model M root phi.modalDepth).trace_iff_of_modalDepth_eq_zero
      (rootPath M root phi.modalDepth) phi hdepth0 1
    have hstart : Pattern.HoldsBit (Pattern.zeroOnesZero k hk).first
        ((model M root phi.modalDepth).trace
          (rootPath M root phi.modalDepth) phi 0) := by
      simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit, Model.trace]
        using hfalse
    have hreal := hvalid (model M root phi.modalDepth)
      (model_isKD45 hM root phi.modalDepth) _ hstart
    have htrue1 := Pattern.realizesTrace_zeroOnesZero_one hk hreal
    exact hfalse (by
      change (model M root phi.modalDepth).trace
        (rootPath M root phi.modalDepth) phi 0
      exact hstable.mp htrue1)
  · let N := model M root phi.modalDepth
    let r := rootPath M root phi.modalDepth
    by_contra hrFalse
    have hdepth : 0 < phi.modalDepth := Nat.pos_of_ne_zero hdepth0
    have hne : ∃ y n, ¬(N.iterateUpdate phi n).Satisfies y phi :=
      ⟨r, 0, by simpa [N, r] using hrFalse⟩
    obtain ⟨x, hxFalse, hmax⟩ := exists_maximal_firstFalse
      N phi (fun y => y.rank) hne
    let q := firstFalse N phi x
    have hxRankMax : ∀ y, (∃ n, ¬(N.iterateUpdate phi n).Satisfies y phi) →
        y.rank ≤ x.rank := fun y hy => maximal_firstFalse_rank hmax hy
    have hzeroOne : Sigma.Valid
        (Classes.KD45 (Atom := Atom) (Agent := Agent) :
          FrameClass.{max u w} Atom Agent) phi Pattern.zeroOne := by
      have hp : Pattern.zeroOne.IsPrefix (Pattern.zeroOnesZero k hk) := by
        change [false, true] <+: false :: List.replicate k true ++ [false]
        cases k with
        | zero => omega
        | succ k => simp [List.replicate_succ]
      intro World P hP y hy
      have hy' : Pattern.HoldsBit (Pattern.zeroOnesZero k hk).first
          (P.trace y phi 0) := by
        simpa [Pattern.zeroOne, Pattern.zeroOnesZero, Pattern.first] using hy
      exact Pattern.realizesTrace_mono_of_prefix hp (hvalid P hP y hy')
    have hxNonroot : x.history ≠ [] :=
      maximal_everFalse_nonroot hM hdepth phi x hxFalse hxRankMax hzeroOne
    have hxLt : x.rank < phi.modalDepth :=
      maximal_everFalse_nonterminal_zeroOnesZero hdepth phi k hk x hxFalse
        hxNonroot hvalid
    have hxSurv : N.Survives phi q x :=
      survives_firstFalse N phi x hxFalse
    have hlocalKD45 : IsKD45 ((N.iterateUpdate phi q).generatedSubmodel x) :=
      generatedSubmodel_isKD45_at_maximal_rank hM hdepth phi hxNonroot hxLt
        hxSurv hxRankMax
    have hxFalseQ : ¬(N.iterateUpdate phi q).Satisfies x phi :=
      firstFalse_spec N phi x hxFalse
    let xG := (N.iterateUpdate phi q).generatedPoint x
    have hxLocalFalse : ¬((N.iterateUpdate phi q).generatedSubmodel x).Satisfies
        xG phi := by
      exact fun ht => hxFalseQ
        (((N.iterateUpdate phi q).generatedSubmodel_root_satisfies_iff x phi).mp ht)
    have hstart : Pattern.HoldsBit (Pattern.zeroOnesZero k hk).first
        (((N.iterateUpdate phi q).generatedSubmodel x).trace xG phi 0) := by
      simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit, Model.trace]
        using hxLocalFalse
    have hrealQ := hvalid ((N.iterateUpdate phi q).generatedSubmodel x)
      hlocalKD45 xG hstart
    have hendsQ := Pattern.realizesTrace_zeroOnesZero_ends hk hrealQ
    have htrueQ1 : (N.iterateUpdate phi (q + 1)).Satisfies x phi := by
      have hlocalTrue := Pattern.realizesTrace_zeroOnesZero_one hk hrealQ
      exact (generated_shift_satisfies_iff N phi q 1 x phi).mp hlocalTrue
    let G1 := (N.iterateUpdate phi (q + 1)).generatedSubmodel x
    let xG1 := (N.iterateUpdate phi (q + 1)).generatedPoint x
    have htargetsTrue : ∀ (i : Agent) (y z : Subtype
        ((N.iterateUpdate phi (q + 1)).generatedSet x)),
        G1.rel i y z → G1.Satisfies z phi := by
      intro i y z hyz
      apply ((N.iterateUpdate phi (q + 1)).generatedSubmodel_satisfies_iff
        x z phi).mpr
      have hzReachNow : (N.iterateUpdate phi (q + 1)).Reachable x z.1 := z.2
      have hzReach : N.Reachable x z.1 :=
        reachable_of_iterateUpdate_reachable N phi (q + 1) hzReachNow
      have hxle : x.rank ≤ z.1.rank := rank_le_of_reachable hdepth hzReach
      by_cases hzEver : ∃ n, ¬(N.iterateUpdate phi n).Satisfies z.1 phi
      · have hzRankLe := hxRankMax z.1 hzEver
        have hzRank : z.1.rank = x.rank := by omega
        have hzTime := maximal_firstFalse_time_of_rank_eq hmax hzEver hzRank
        have hzSurvQ1 : N.Survives phi (q + 1) z.1 :=
          (N.iterateUpdate_rel_iff phi (q + 1) i y.1 z.1).mp hyz |>.2
        have hzTrueAtFirst :
            (N.iterateUpdate phi (firstFalse N phi z.1)).Satisfies z.1 phi :=
          hzSurvQ1 _ (by dsimp [q] at hzTime ⊢; omega)
        exact (firstFalse_spec N phi z.1 hzEver hzTrueAtFirst).elim
      · push_neg at hzEver
        exact hzEver (q + 1)
    have hG1Update : G1.update phi = G1 := by
      apply Model.ext'
      · intro i y z
        simp only [Model.update_rel]
        constructor
        · exact fun h => h.1
        · intro hyz
          exact ⟨hyz, htargetsTrue i y z hyz⟩
      · intro p y; rfl
    have hG1Iter : ∀ n, G1.iterateUpdate phi n = G1 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          calc
            G1.iterateUpdate phi (n + 1) =
                (G1.iterateUpdate phi n).update phi := rfl
            _ = G1.update phi := congrArg (fun P => P.update phi) ih
            _ = G1 := hG1Update
    have hxLocalTrue1 : G1.Satisfies xG1 phi :=
      ((N.iterateUpdate phi (q + 1)).generatedSubmodel_root_satisfies_iff
        x phi).mpr htrueQ1
    have htrueAtQK1 : (N.iterateUpdate phi (q + k + 1)).Satisfies x phi := by
      have hlocalTrue : (G1.iterateUpdate phi k).Satisfies xG1 phi := by
        rw [hG1Iter k]
        exact hxLocalTrue1
      have hshift := (generated_shift_satisfies_iff N phi (q + 1) k x phi).mp
        hlocalTrue
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hshift
    have hfalseAtQK1 : ¬(N.iterateUpdate phi (q + k + 1)).Satisfies x phi := by
      have hlocalFalse := hendsQ.2.2
      have hshift := (generated_shift_satisfies_iff N phi q (k + 1) x phi).not.mp
        hlocalFalse
      simpa only [Nat.add_assoc] using hshift
    exact hfalseAtQK1 htrueAtQK1

/-! ## Global multi-agent KD45 transfers -/

/-- On finite agent types, `0^k1`-validity over multi-agent KD45 forces plain
validity.  The finite-model property supplies the finite source countermodel
required by the unravelling construction. -/
theorem finiteAgent_kd45_valid_zerosOne_true
    [Finite Agent] [Nonempty Agent]
    (phi : Formula Atom Agent) (k : Nat) (hk : 2 ≤ k)
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) :
        FrameClass.{max u w} Atom Agent)
      phi (Pattern.zerosOne k hk)) :
    ∀ {World : Type max u w} (M : Model World Atom Agent),
      IsKD45 M → ∀ x, M.Satisfies x phi := by
  intro World M hM x
  by_contra hx
  obtain ⟨FiniteWorld, hFinite, P, hP, z, hz⟩ :=
    Filtration.exists_finite_countermodel_isKD45 M hM phi x hx
  letI : Finite FiniteWorld := hFinite
  have hUnravel := finite_unravelling_valid_zerosOne_true
    hP z phi k hk hvalid
  have hzTrue := (root_satisfies_target_iff P hP.isK45 z phi).mp hUnravel
  exact hz hzTrue

/-- On finite agent types, `01^k0`-validity over multi-agent KD45 likewise
forces plain validity. -/
theorem finiteAgent_kd45_valid_zeroOnesZero_true
    [Finite Agent] [Nonempty Agent]
    (phi : Formula Atom Agent) (k : Nat) (hk : 1 ≤ k)
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) :
        FrameClass.{max u w} Atom Agent)
      phi (Pattern.zeroOnesZero k hk)) :
    ∀ {World : Type max u w} (M : Model World Atom Agent),
      IsKD45 M → ∀ x, M.Satisfies x phi := by
  intro World M hM x
  by_contra hx
  obtain ⟨FiniteWorld, hFinite, P, hP, z, hz⟩ :=
    Filtration.exists_finite_countermodel_isKD45 M hM phi x hx
  letI : Finite FiniteWorld := hFinite
  have hUnravel := finite_unravelling_valid_zeroOnesZero_true
    hP z phi k hk hvalid
  have hzTrue := (root_satisfies_target_iff P hP.isK45 z phi).mp hUnravel
  exact hz hzTrue

/-- Paper Lemma `lem:nonexistence_of_0k1-validity_multi_kd45`, with the
finite-agent hypothesis made explicit. -/
theorem finiteAgent_kd45_not_nontriviallyValid_zerosOne
    [Finite Agent] [Nonempty Agent]
    (phi : Formula Atom Agent) (k : Nat) (hk : 2 ≤ k) :
    ¬Sigma.NontriviallyValid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) :
        FrameClass.{max u w} Atom Agent)
      phi (Pattern.zerosOne k hk) := by
  rintro ⟨hvalid, World, M, hM, x, hreal⟩
  have htrue := finiteAgent_kd45_valid_zerosOne_true
    phi k hk hvalid M hM x
  have hfirst := Pattern.realizesTrace_first hreal
  have hfalse : ¬M.Satisfies x phi := by
    simpa [Pattern.HoldsBit, Model.trace] using hfirst
  exact hfalse htrue

/-- Paper Lemma `lem:nonexistence_of_01k0-validity_multi_kd45`, with finite
agents explicit. -/
theorem finiteAgent_kd45_not_nontriviallyValid_zeroOnesZero
    [Finite Agent] [Nonempty Agent]
    (phi : Formula Atom Agent) (k : Nat) (hk : 1 ≤ k) :
    ¬Sigma.NontriviallyValid
      (Classes.KD45 (Atom := Atom) (Agent := Agent) :
        FrameClass.{max u w} Atom Agent)
      phi (Pattern.zeroOnesZero k hk) := by
  rintro ⟨hvalid, World, M, hM, x, hreal⟩
  have htrue := finiteAgent_kd45_valid_zeroOnesZero_true
    phi k hk hvalid M hM x
  have hfirst := Pattern.realizesTrace_first hreal
  have hfalse : ¬M.Satisfies x phi := by
    simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit, Model.trace]
      using hfirst
  exact hfalse htrue

/-- Pattern-level finite-agent KD45 nonadmissibility of `0^k1`. -/
theorem finiteAgent_kd45_zerosOne_not_admissible
    [Finite Agent] [Nonempty Agent] (k : Nat) (hk : 2 ≤ k) :
    ¬Sigma.Admissible
      (Classes.KD45 (Atom := Atom) (Agent := Agent) :
        FrameClass.{max u w} Atom Agent)
      (Pattern.zerosOne k hk) := by
  rintro ⟨phi, hphi⟩
  exact finiteAgent_kd45_not_nontriviallyValid_zerosOne phi k hk hphi

/-- Pattern-level finite-agent KD45 nonadmissibility of `01^k0`. -/
theorem finiteAgent_kd45_zeroOnesZero_not_admissible
    [Finite Agent] [Nonempty Agent] (k : Nat) (hk : 1 ≤ k) :
    ¬Sigma.Admissible
      (Classes.KD45 (Atom := Atom) (Agent := Agent) :
        FrameClass.{max u w} Atom Agent)
      (Pattern.zeroOnesZero k hk) := by
  rintro ⟨phi, hphi⟩
  exact finiteAgent_kd45_not_nontriviallyValid_zeroOnesZero phi k hk hphi



end Unravelling

end ClassificationSigmaValidity
