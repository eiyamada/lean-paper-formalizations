import Mathlib.ModelTheory.Satisfiability
import ClassificationSigmaValidity.Frames

/-!
# First-order semantics of K45

The standard translation, including a constant for the distinguished world,
allows first-order compactness to be applied to arbitrary sets of modal formulas.
The countable language of the manuscript is covered by `Atom Agent : Type`.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements
namespace FirstOrderEncoding

open ClassificationSigmaValidity
open FirstOrder.Language
open FirstOrder.Language.Structure

variable (Atom Agent : Type)

inductive RelationSymbol : Nat → Type
  | atom : Atom → RelationSymbol 1
  | agent : Agent → RelationSymbol 2

inductive FunctionSymbol : Nat → Type
  | point : FunctionSymbol 0

def language : FirstOrder.Language where
  Functions := FunctionSymbol
  Relations := RelationSymbol Atom Agent

variable {Atom Agent}

abbrev L := language Atom Agent

def pointTerm {n : Nat} : (L (Atom := Atom) (Agent := Agent)).Term (Empty ⊕ Fin n) :=
  .func FunctionSymbol.point Fin.elim0

def liftTerm {n : Nat} (t : (L (Atom := Atom) (Agent := Agent)).Term (Empty ⊕ Fin n)) :
    (L (Atom := Atom) (Agent := Agent)).Term (Empty ⊕ Fin (n + 1)) :=
  t.relabel (Sum.map id Fin.castSucc)

/-- Standard translation at a designated term, with bound variables appended. -/
def translate (φ : ClassificationSigmaValidity.Formula Atom Agent) {n : Nat}
    (t : (L (Atom := Atom) (Agent := Agent)).Term (Empty ⊕ Fin n)) :
    (L (Atom := Atom) (Agent := Agent)).BoundedFormula Empty n :=
  match φ with
  | .atom p => Relations.boundedFormula₁ (L := language Atom Agent) (RelationSymbol.atom p) t
  | .neg ψ => (translate ψ t).not
  | .conj ψ χ => translate ψ t ⊓ translate χ t
  | .box a ψ =>
      ((Relations.boundedFormula₂ (L := language Atom Agent) (RelationSymbol.agent a) (liftTerm t)
        (.var (.inr (Fin.last n)))).imp
          (translate ψ (.var (.inr (Fin.last n))))).all

def atPoint (φ : ClassificationSigmaValidity.Formula Atom Agent) :
    (L (Atom := Atom) (Agent := Agent)).Sentence := translate φ pointTerm

variable {World : Type*}

/-- Turn a first-order structure into its underlying Kripke model. -/
def toModel (World : Type*) [(L (Atom := Atom) (Agent := Agent)).Structure World] :
    Model World Atom Agent where
  rel a x y := RelMap (L := language Atom Agent) (RelationSymbol.agent a) ![x, y]
  val p x := RelMap (L := language Atom Agent) (RelationSymbol.atom p) ![x]

def point (World : Type*) [(L (Atom := Atom) (Agent := Agent)).Structure World] : World :=
  funMap (L := language Atom Agent) (FunctionSymbol.point : (L (Atom := Atom) (Agent := Agent)).Functions 0) Fin.elim0

/-- The first-order expansion of a pointed Kripke model. -/
def structureOf (M : Model World Atom Agent) (x : World) :
    (L (Atom := Atom) (Agent := Agent)).Structure World where
  funMap := fun f _ => match f with | .point => x
  RelMap := fun r v => match r with
    | .atom p => M.val p (v 0)
    | .agent a => M.rel a (v 0) (v 1)

variable [(L (Atom := Atom) (Agent := Agent)).Structure World]

@[simp] theorem realize_liftTerm {n : Nat}
    (t : (L (Atom := Atom) (Agent := Agent)).Term (Empty ⊕ Fin n))
    (xs : Fin n → World) (x : World) :
    (liftTerm t).realize (Sum.elim Empty.elim (Fin.snoc xs x)) =
      t.realize (Sum.elim Empty.elim xs) := by
  simp only [liftTerm, Term.realize_relabel]
  congr 1
  funext i
  cases i with
  | inl e => exact e.elim
  | inr i => simp

@[simp] theorem realize_translate (φ : ClassificationSigmaValidity.Formula Atom Agent)
    {n : Nat} (t : (L (Atom := Atom) (Agent := Agent)).Term (Empty ⊕ Fin n))
    (xs : Fin n → World) :
    (translate φ t).Realize Empty.elim xs ↔
      (toModel (Atom := Atom) (Agent := Agent) World).Satisfies (t.realize (Sum.elim Empty.elim xs)) φ := by
  induction φ generalizing n with
  | atom p => simp [translate, Model.Satisfies, toModel]
  | neg ψ ih => simp [translate, Model.Satisfies, ih]
  | conj ψ χ ihψ ihχ => simp [translate, Model.Satisfies, ihψ, ihχ]
  | box a ψ ih => simp [translate, Model.Satisfies, toModel, ih]

@[simp] theorem realize_atPoint (φ : ClassificationSigmaValidity.Formula Atom Agent) :
    Sentence.Realize World (atPoint φ) ↔
      (toModel (Atom := Atom) (Agent := Agent) World).Satisfies (point (Atom := Atom) (Agent := Agent) World) φ := by
  change (translate φ pointTerm).Realize (default : Empty → World)
    (default : Fin 0 → World) ↔ _
  rw [Subsingleton.elim (default : Empty → World) Empty.elim, realize_translate]
  have ht : (pointTerm : (L (Atom := Atom) (Agent := Agent)).Term (Empty ⊕ Fin 0)).realize
      (Sum.elim Empty.elim (default : Fin 0 → World)) =
      point (Atom := Atom) (Agent := Agent) World := by
    simp only [pointTerm, Term.realize_func, point]
    congr 1
    exact Subsingleton.elim _ _
  rw [ht]

def edge {n : Nat} (a : Agent) (i j : Fin n) :
    (L (Atom := Atom) (Agent := Agent)).BoundedFormula Empty n :=
  Relations.boundedFormula₂ (L := language Atom Agent) (RelationSymbol.agent a) (.var (.inr i)) (.var (.inr j))

def transitiveSentence (a : Agent) : (L (Atom := Atom) (Agent := Agent)).Sentence :=
  ((edge a (0 : Fin 3) 1).imp ((edge a 1 2).imp (edge a 0 2))).all.all.all

def euclideanSentence (a : Agent) : (L (Atom := Atom) (Agent := Agent)).Sentence :=
  ((edge a (0 : Fin 3) 1).imp ((edge a 0 2).imp (edge a 1 2))).all.all.all

@[simp] theorem realize_transitiveSentence (a : Agent) :
    Sentence.Realize World (transitiveSentence (Atom := Atom) a) ↔
      Frame.Transitive ((toModel (Atom := Atom) (Agent := Agent) World).rel a) := by
  simp [transitiveSentence, edge, Sentence.Realize, Formula.Realize, toModel,
    Frame.Transitive, Fin.snoc]

@[simp] theorem realize_euclideanSentence (a : Agent) :
    Sentence.Realize World (euclideanSentence (Atom := Atom) a) ↔
      Frame.Euclidean ((toModel (Atom := Atom) (Agent := Agent) World).rel a) := by
  simp [euclideanSentence, edge, Sentence.Realize, Formula.Realize, toModel,
    Frame.Euclidean, Fin.snoc]

/-- K45 axioms together with a set of formulas true at the point. -/
def theory (Γ : Set (ClassificationSigmaValidity.Formula Atom Agent)) :
    (L (Atom := Atom) (Agent := Agent)).Theory :=
  Set.range transitiveSentence ∪ Set.range euclideanSentence ∪ atPoint '' Γ

omit [(L (Atom := Atom) (Agent := Agent)).Structure World] in
@[simp] theorem toModel_structureOf (M : Model World Atom Agent) (x : World) :
    @toModel Atom Agent World (structureOf M x) = M := rfl

omit [(L (Atom := Atom) (Agent := Agent)).Structure World] in
@[simp] theorem point_structureOf (M : Model World Atom Agent) (x : World) :
    @point Atom Agent World (structureOf M x) = x := rfl

omit [(L (Atom := Atom) (Agent := Agent)).Structure World] in
 theorem theory_satisfiable {Γ : Set (ClassificationSigmaValidity.Formula Atom Agent)}
    (M : Model World Atom Agent) (hM : IsK45 M) (x : World)
    (hΓ : ∀ φ ∈ Γ, M.Satisfies x φ) : (theory Γ).IsSatisfiable := by
  letI := structureOf M x
  letI : Nonempty World := ⟨x⟩
  haveI : (theory Γ).Model World := by
    constructor
    intro φ hφ
    rcases hφ with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨ψ, hψ, rfl⟩
    · apply (realize_transitiveSentence (Atom := Atom) (World := World) a).mpr
      change Frame.Transitive (M.rel a)
      exact (hM a).1
    · apply (realize_euclideanSentence (Atom := Atom) (World := World) a).mpr
      change Frame.Euclidean (M.rel a)
      exact (hM a).2
    · simpa using hΓ ψ hψ
  exact Theory.Model.isSatisfiable World

/-- Modal K45 compactness for an increasing sequence of finite prefixes. -/
theorem compactness_sequence (φ : Nat → ClassificationSigmaValidity.Formula Atom Agent)
    (h : ∀ N : Nat, ∃ (World : Type) (M : Model World Atom Agent),
      IsK45 M ∧ ∃ x, ∀ n, n ≤ N → M.Satisfies x (φ n)) :
    ∃ (World : Type) (M : Model World Atom Agent),
      IsK45 M ∧ ∃ x, ∀ n, M.Satisfies x (φ n) := by
  let T : Nat → (L (Atom := Atom) (Agent := Agent)).Theory :=
    fun N => theory (φ '' {n | n ≤ N})
  have hmono : Monotone T := by
    intro N K hNK ψ hψ
    rcases hψ with hψ | ⟨χ, ⟨n, hn, rfl⟩, rfl⟩
    · exact Or.inl hψ
    · exact Or.inr ⟨φ n, ⟨n, le_trans hn hNK, rfl⟩, rfl⟩
  have hsat : ∀ N, (T N).IsSatisfiable := by
    intro N
    obtain ⟨World, M, hM, x, hx⟩ := h N
    exact theory_satisfiable M hM x (by rintro ψ ⟨n, hn, rfl⟩; exact hx n hn)
  have hs : Theory.IsSatisfiable (⋃ N, T N) :=
    (Theory.isSatisfiable_directed_union_iff hmono.directed_le).mpr hsat
  let A := hs.some
  refine ⟨A, toModel (Atom := Atom) (Agent := Agent) A, ?_,
    point (Atom := Atom) (Agent := Agent) A, ?_⟩
  · intro a
    constructor
    · apply (realize_transitiveSentence (Atom := Atom) (World := A) a).mp
      exact Theory.realize_sentence_of_mem (⋃ N, T N)
        (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inl ⟨a, rfl⟩)⟩)
    · apply (realize_euclideanSentence (Atom := Atom) (World := A) a).mp
      exact Theory.realize_sentence_of_mem (⋃ N, T N)
        (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr ⟨a, rfl⟩)⟩)
  · intro n
    apply (realize_atPoint (φ n)).mp
    exact Theory.realize_sentence_of_mem (⋃ N, T N)
      (Set.mem_iUnion.mpr ⟨n, Or.inr ⟨φ n, ⟨n, by simp, rfl⟩, rfl⟩⟩)

end FirstOrderEncoding
end EventualAndStrongEventualNotionsInPublicAnnouncements
