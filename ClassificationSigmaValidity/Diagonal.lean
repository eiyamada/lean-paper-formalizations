import ClassificationSigmaValidity.Frames

/-!
# Diagonal formulas and duplicated-agent models

For maps of atoms and agents, a Kripke model can be pulled back by using the
mapped atom in its valuation and the mapped agent in its accessibility
relation.  Satisfaction in the pulled-back model is exactly satisfaction of
the mapped formula in the original model.

The paper's model `P^I` is the special case in which a single-agent model is
pulled back along the unique map from `I` to `Unit`.  Besides proving part (1)
of Lemma `lem:diagonal_model_equivalence`, this file records that believed
updates and their iterations commute with pullback.  Consequently the entire
truth trace of a multi-agent formula in `P^I` agrees with the trace of its
diagonal in `P`.
-/

namespace ClassificationSigmaValidity

universe u v w v' w'

namespace Model

variable {World : Type u}
variable {Atom : Type v} {Agent : Type w}
variable {Atom' : Type v'} {Agent' : Type w'}

/-- Pull a model back along a map of proposition letters and a map of agents. -/
def reindex (M : Model World Atom' Agent') (atomMap : Atom -> Atom')
    (agentMap : Agent -> Agent') : Model World Atom Agent where
  rel i := M.rel (agentMap i)
  val p := M.val (atomMap p)

@[simp] theorem reindex_rel (M : Model World Atom' Agent')
    (atomMap : Atom -> Atom') (agentMap : Agent -> Agent')
    (i : Agent) (x y : World) :
    (M.reindex atomMap agentMap).rel i x y <->
      M.rel (agentMap i) x y := Iff.rfl

@[simp] theorem reindex_val (M : Model World Atom' Agent')
    (atomMap : Atom -> Atom') (agentMap : Agent -> Agent')
    (p : Atom) (x : World) :
    (M.reindex atomMap agentMap).val p x <->
      M.val (atomMap p) x := Iff.rfl

/-- The semantic renaming lemma: formula maps are interpreted by pulling the
model back along the same maps. -/
theorem reindex_satisfies_map (M : Model World Atom' Agent')
    (atomMap : Atom -> Atom') (agentMap : Agent -> Agent')
    (x : World) (phi : Formula Atom Agent) :
    (M.reindex atomMap agentMap).Satisfies x phi <->
      M.Satisfies x (Formula.map atomMap agentMap phi) := by
  induction phi generalizing x with
  | atom p => rfl
  | neg phi ih =>
      simp only [Formula.map, satisfies_neg, ih]
  | conj phi psi ihPhi ihPsi =>
      simp only [Formula.map, satisfies_and, ihPhi, ihPsi]
  | box i phi ih =>
      simp only [Formula.map, satisfies_box, reindex_rel]
      constructor
      · intro h y hxy
        exact (ih y).mp (h y hxy)
      · intro h y hxy
        exact (ih y).mpr (h y hxy)

/-- Pullback commutes with a believed public-announcement update. -/
theorem reindex_update (M : Model World Atom' Agent')
    (atomMap : Atom -> Atom') (agentMap : Agent -> Agent')
    (phi : Formula Atom Agent) :
    (M.reindex atomMap agentMap).update phi =
      (M.update (Formula.map atomMap agentMap phi)).reindex atomMap agentMap := by
  apply Model.ext'
  · intro i x y
    simp only [update_rel, reindex_rel, reindex_satisfies_map]
  · intro p x
    simp only [update_val, reindex_val]

/-- Pullback commutes with every finite iteration of the same announcement. -/
theorem reindex_iterateUpdate (M : Model World Atom' Agent')
    (atomMap : Atom -> Atom') (agentMap : Agent -> Agent')
    (phi : Formula Atom Agent) : forall n : Nat,
    (M.reindex atomMap agentMap).iterateUpdate phi n =
      (M.iterateUpdate (Formula.map atomMap agentMap phi) n).reindex
        atomMap agentMap
  | 0 => rfl
  | n + 1 => by
      rw [iterateUpdate_succ, iterateUpdate_succ,
        reindex_iterateUpdate M atomMap agentMap phi n]
      exact reindex_update
        (M.iterateUpdate (Formula.map atomMap agentMap phi) n)
        atomMap agentMap phi

/-- Truth of an arbitrary mapped formula also commutes with every iterated
update. -/
theorem reindex_iterateUpdate_satisfies_map
    (M : Model World Atom' Agent')
    (atomMap : Atom -> Atom') (agentMap : Agent -> Agent')
    (phi psi : Formula Atom Agent) (n : Nat) (x : World) :
    ((M.reindex atomMap agentMap).iterateUpdate phi n).Satisfies x psi <->
      (M.iterateUpdate (Formula.map atomMap agentMap phi) n).Satisfies x
        (Formula.map atomMap agentMap psi) := by
  rw [reindex_iterateUpdate M atomMap agentMap phi n]
  exact reindex_satisfies_map
    (M.iterateUpdate (Formula.map atomMap agentMap phi) n)
    atomMap agentMap x psi

/-- In particular, the complete truth trace commutes with pullback. -/
theorem reindex_trace (M : Model World Atom' Agent')
    (atomMap : Atom -> Atom') (agentMap : Agent -> Agent')
    (phi : Formula Atom Agent) (x : World) (n : Nat) :
    (M.reindex atomMap agentMap).trace x phi n <->
      M.trace x (Formula.map atomMap agentMap phi) n := by
  exact reindex_iterateUpdate_satisfies_map
    M atomMap agentMap phi phi n x

/-- Reindexing preserves K45 because each new accessibility relation is one of
the old model's accessibility relations. -/
theorem reindex_isK45 {M : Model World Atom' Agent'} (hM : IsK45 M)
    (atomMap : Atom -> Atom') (agentMap : Agent -> Agent') :
    IsK45 (M.reindex atomMap agentMap) := by
  intro i
  exact hM (agentMap i)

/-- Reindexing preserves KD45. -/
theorem reindex_isKD45 {M : Model World Atom' Agent'} (hM : IsKD45 M)
    (atomMap : Atom -> Atom') (agentMap : Agent -> Agent') :
    IsKD45 (M.reindex atomMap agentMap) := by
  intro i
  exact hM (agentMap i)

/-- Reindexing preserves S5. -/
theorem reindex_isS5 {M : Model World Atom' Agent'} (hM : IsS5 M)
    (atomMap : Atom -> Atom') (agentMap : Agent -> Agent') :
    IsS5 (M.reindex atomMap agentMap) := by
  intro i
  exact hM (agentMap i)

/-- The paper's multi-agent model `P^I`: every agent uses the sole relation of
the single-agent model `P`. -/
def diagonalExpansion (P : Model World Atom Unit) (Agent : Type w) :
    Model World Atom Agent :=
  P.reindex id (fun _ => ())

@[simp] theorem diagonalExpansion_rel (P : Model World Atom Unit)
    (Agent : Type w) (i : Agent) (x y : World) :
    (P.diagonalExpansion Agent).rel i x y <-> P.rel () x y := Iff.rfl

@[simp] theorem diagonalExpansion_val (P : Model World Atom Unit)
    (Agent : Type w) (p : Atom) (x : World) :
    (P.diagonalExpansion Agent).val p x <-> P.val p x := Iff.rfl

/-- Paper Lemma `lem:diagonal_model_equivalence` (1), oriented from the
multi-agent model to the single-agent model. -/
theorem diagonalExpansion_satisfies_iff (P : Model World Atom Unit)
    (Agent : Type w) (x : World) (phi : Formula Atom Agent) :
    (P.diagonalExpansion Agent).Satisfies x phi <->
      P.Satisfies x (Formula.diagonal phi) := by
  simpa only [diagonalExpansion, Formula.diagonal] using
    reindex_satisfies_map P (fun p : Atom => p) (fun _ : Agent => ()) x phi

/-- Paper Lemma `lem:diagonal_model_equivalence` (1), in the orientation used
in the displayed equivalence in the paper. -/
theorem satisfies_diagonal_iff_diagonalExpansion
    (P : Model World Atom Unit) (Agent : Type w)
    (x : World) (phi : Formula Atom Agent) :
    P.Satisfies x (Formula.diagonal phi) <->
      (P.diagonalExpansion Agent).Satisfies x phi :=
  (P.diagonalExpansion_satisfies_iff Agent x phi).symm

/-- One diagonal announcement commutes with expansion to all agents. -/
theorem diagonalExpansion_update (P : Model World Atom Unit)
    (Agent : Type w) (phi : Formula Atom Agent) :
    (P.diagonalExpansion Agent).update phi =
      (P.update (Formula.diagonal phi)).diagonalExpansion Agent := by
  simpa only [diagonalExpansion, Formula.diagonal] using
    reindex_update P (fun p : Atom => p) (fun _ : Agent => ()) phi

/-- Every finite iteration of a diagonal announcement commutes with expansion
to all agents. -/
theorem diagonalExpansion_iterateUpdate (P : Model World Atom Unit)
    (Agent : Type w) (phi : Formula Atom Agent) (n : Nat) :
    (P.diagonalExpansion Agent).iterateUpdate phi n =
      (P.iterateUpdate (Formula.diagonal phi) n).diagonalExpansion Agent := by
  simpa only [diagonalExpansion, Formula.diagonal] using
    reindex_iterateUpdate P (fun p : Atom => p) (fun _ : Agent => ()) phi n

/-- At every update stage, arbitrary formulas have the same truth value in the
expanded multi-agent model and, after diagonalization, in the single-agent
model. -/
theorem diagonalExpansion_iterateUpdate_satisfies_iff
    (P : Model World Atom Unit) (Agent : Type w)
    (phi psi : Formula Atom Agent) (n : Nat) (x : World) :
    ((P.diagonalExpansion Agent).iterateUpdate phi n).Satisfies x psi <->
      (P.iterateUpdate (Formula.diagonal phi) n).Satisfies x
        (Formula.diagonal psi) := by
  simpa only [diagonalExpansion, Formula.diagonal] using
    reindex_iterateUpdate_satisfies_map P
      (fun p : Atom => p) (fun _ : Agent => ()) phi psi n x

/-- The trace-level form needed to transfer sigma-validity between a formula
and its diagonal. -/
theorem diagonalExpansion_trace_iff (P : Model World Atom Unit)
    (Agent : Type w) (phi : Formula Atom Agent) (x : World) (n : Nat) :
    (P.diagonalExpansion Agent).trace x phi n <->
      P.trace x (Formula.diagonal phi) n := by
  exact diagonalExpansion_iterateUpdate_satisfies_iff
    P Agent phi phi n x

/-- Duplicating the sole relation of a single-agent K45 model preserves K45. -/
theorem diagonalExpansion_isK45 {P : Model World Atom Unit} (hP : IsK45 P)
    (Agent : Type w) : IsK45 (P.diagonalExpansion Agent) := by
  exact reindex_isK45 hP (fun p : Atom => p) (fun _ : Agent => ())

/-- Duplicating the sole relation of a single-agent KD45 model preserves
KD45, as required for the paper's model `P^I`. -/
theorem diagonalExpansion_isKD45 {P : Model World Atom Unit} (hP : IsKD45 P)
    (Agent : Type w) : IsKD45 (P.diagonalExpansion Agent) := by
  exact reindex_isKD45 hP (fun p : Atom => p) (fun _ : Agent => ())

/-- Duplicating the sole relation of a single-agent S5 model preserves S5. -/
theorem diagonalExpansion_isS5 {P : Model World Atom Unit} (hP : IsS5 P)
    (Agent : Type w) : IsS5 (P.diagonalExpansion Agent) := by
  exact reindex_isS5 hP (fun p : Atom => p) (fun _ : Agent => ())

end Model

end ClassificationSigmaValidity
