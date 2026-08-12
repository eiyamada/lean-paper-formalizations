import Mathlib.Data.Finset.Basic

/-!
# Modal and public-announcement syntax

The paper's classification concerns formulas of the basic multi-agent modal
language.  We also record the two dynamic languages used in its introductory
definitions.
-/

namespace ClassificationSigmaValidity

universe u v
universe u' v'

/-- Formulas of multi-agent epistemic logic. -/
inductive Formula (Atom : Type u) (Agent : Type v) where
  | atom : Atom -> Formula Atom Agent
  | neg : Formula Atom Agent -> Formula Atom Agent
  | conj : Formula Atom Agent -> Formula Atom Agent -> Formula Atom Agent
  | box : Agent -> Formula Atom Agent -> Formula Atom Agent
  deriving DecidableEq, Repr

namespace Formula

variable {Atom : Type u} {Agent : Type v}

/-- Disjunction, as the usual Boolean abbreviation. -/
def or (phi psi : Formula Atom Agent) : Formula Atom Agent :=
  neg (conj (neg phi) (neg psi))

/-- Implication, as the usual Boolean abbreviation. -/
def imp (phi psi : Formula Atom Agent) : Formula Atom Agent :=
  or (neg phi) psi

/-- Possibility, dual to `box`. -/
def dia (i : Agent) (phi : Formula Atom Agent) : Formula Atom Agent :=
  neg (box i (neg phi))

/-- Falsity.  The paper assumes an infinite, hence inhabited, atom type. -/
def falsum [Inhabited Atom] : Formula Atom Agent :=
  conj (atom default) (neg (atom default))

/-- Truth. -/
def verum [Inhabited Atom] : Formula Atom Agent :=
  neg falsum

/-- Modal depth. -/
def modalDepth : Formula Atom Agent -> Nat
  | atom _ => 0
  | neg phi => modalDepth phi
  | conj phi psi => max (modalDepth phi) (modalDepth psi)
  | box _ phi => modalDepth phi + 1

/-- Proposition letters occurring in a formula. -/
def atoms [DecidableEq Atom] : Formula Atom Agent -> Finset Atom
  | atom p => {p}
  | neg phi => atoms phi
  | conj phi psi => atoms phi ∪ atoms psi
  | box _ phi => atoms phi

/-- Agents occurring in a formula. -/
def agents [DecidableEq Agent] : Formula Atom Agent -> Finset Agent
  | atom _ => ∅
  | neg phi => agents phi
  | conj phi psi => agents phi ∪ agents psi
  | box i phi => insert i (agents phi)

/-- Rename proposition letters and agents in a formula. -/
def map {Atom' : Type u'} {Agent' : Type v'} (f : Atom -> Atom') (g : Agent -> Agent') :
    Formula Atom Agent -> Formula Atom' Agent'
  | atom p => atom (f p)
  | neg phi => neg (map f g phi)
  | conj phi psi => conj (map f g phi) (map f g psi)
  | box i phi => box (g i) (map f g phi)

/-- Collapse every modality to a single agent, the paper's `phi^Delta`. -/
def diagonal (phi : Formula Atom Agent) : Formula Atom Unit :=
  map id (fun _ => ()) phi

@[simp] theorem modalDepth_or (phi psi : Formula Atom Agent) :
    modalDepth (or phi psi) = max (modalDepth phi) (modalDepth psi) := by
  simp [or, modalDepth]

@[simp] theorem modalDepth_imp (phi psi : Formula Atom Agent) :
    modalDepth (imp phi psi) = max (modalDepth phi) (modalDepth psi) := by
  simp [imp, modalDepth]

@[simp] theorem modalDepth_dia (i : Agent) (phi : Formula Atom Agent) :
    modalDepth (dia i phi) = modalDepth phi + 1 := by
  simp [dia, modalDepth]

end Formula

/-- Formulas of public announcement logic (PAL). -/
inductive PALFormula (Atom : Type u) (Agent : Type v) where
  | atom : Atom -> PALFormula Atom Agent
  | neg : PALFormula Atom Agent -> PALFormula Atom Agent
  | conj : PALFormula Atom Agent -> PALFormula Atom Agent -> PALFormula Atom Agent
  | box : Agent -> PALFormula Atom Agent -> PALFormula Atom Agent
  | announce : PALFormula Atom Agent -> PALFormula Atom Agent -> PALFormula Atom Agent
  deriving DecidableEq, Repr

/-- Formulas of believed public announcement logic (BPAL). -/
inductive BPALFormula (Atom : Type u) (Agent : Type v) where
  | atom : Atom -> BPALFormula Atom Agent
  | neg : BPALFormula Atom Agent -> BPALFormula Atom Agent
  | conj : BPALFormula Atom Agent -> BPALFormula Atom Agent -> BPALFormula Atom Agent
  | box : Agent -> BPALFormula Atom Agent -> BPALFormula Atom Agent
  | announce : BPALFormula Atom Agent -> BPALFormula Atom Agent -> BPALFormula Atom Agent
  deriving DecidableEq, Repr

end ClassificationSigmaValidity
