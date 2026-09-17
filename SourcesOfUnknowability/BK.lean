/-!
# The Brandenburger–Keisler paradox

This file formalizes Definition 14 and Propositions 1–2 of *The Sources of
Unknowability and Self-refutation in Epistemic and Dynamic Epistemic Logic*.
The distinguished atom `D` is interpreted by the diagonal valuation specified
in the propositions. The finite list `prefix` represents agents `1, …, n-1`;
`last` represents agent `n`.
-/

namespace SourcesOfUnknowability.BK

universe u v t

/-- Modal formulas with the additional assumption operator `assume`. -/
inductive Formula (Atom : Type v) (Agent : Type t) where
  | atom : Atom → Formula Atom Agent
  | neg : Formula Atom Agent → Formula Atom Agent
  | conj : Formula Atom Agent → Formula Atom Agent → Formula Atom Agent
  | box : Agent → Formula Atom Agent → Formula Atom Agent
  | assume : Agent → Formula Atom Agent → Formula Atom Agent
  deriving DecidableEq

/-- A multi-agent Kripke model with an ordinary propositional valuation. -/
structure Model (World : Type u) (Atom : Type v) (Agent : Type t) where
  rel : Agent → World → World → Prop
  val : Atom → World → Prop

namespace Model

variable {World : Type u} {Atom : Type v} {Agent : Type t}

/-- The assumption operator says that the entire successor set is exactly
the truth set of its argument. -/
def Satisfies (M : Model World Atom Agent) (w : World) : Formula Atom Agent → Prop
  | .atom p => M.val p w
  | .neg φ => ¬ M.Satisfies w φ
  | .conj φ ψ => M.Satisfies w φ ∧ M.Satisfies w ψ
  | .box i φ => ∀ v, M.rel i w v → M.Satisfies v φ
  | .assume i φ => ∀ v, M.rel i w v ↔ M.Satisfies v φ

@[simp] theorem satisfies_atom (M : Model World Atom Agent) (w : World) (p : Atom) :
    M.Satisfies w (.atom p) ↔ M.val p w := Iff.rfl

@[simp] theorem satisfies_neg (M : Model World Atom Agent) (w : World)
    (φ : Formula Atom Agent) :
    M.Satisfies w (.neg φ) ↔ ¬ M.Satisfies w φ := Iff.rfl

@[simp] theorem satisfies_conj (M : Model World Atom Agent) (w : World)
    (φ ψ : Formula Atom Agent) :
    M.Satisfies w (.conj φ ψ) ↔ M.Satisfies w φ ∧ M.Satisfies w ψ := Iff.rfl

@[simp] theorem satisfies_box (M : Model World Atom Agent) (w : World)
    (i : Agent) (φ : Formula Atom Agent) :
    M.Satisfies w (.box i φ) ↔
      ∀ v, M.rel i w v → M.Satisfies v φ := Iff.rfl

@[simp] theorem satisfies_assume (M : Model World Atom Agent) (w : World)
    (i : Agent) (φ : Formula Atom Agent) :
    M.Satisfies w (.assume i φ) ↔
      ∀ v, M.rel i w v ↔ M.Satisfies v φ := Iff.rfl

end Model

/-- `Path M agents x y` means that `y` is reached from `x` by following the
listed agents' accessibility relations in order. -/
def Path {World : Type u} {Atom : Type v} {Agent : Type t}
    (M : Model World Atom Agent) : List Agent → World → World → Prop
  | [], x, y => x = y
  | i :: is, x, y => ∃ z, M.rel i x z ∧ Path M is z y

/-- The chain of belief operators from Proposition 2. -/
def boxes {Atom : Type v} {Agent : Type t}
    (agents : List Agent) (φ : Formula Atom Agent) : Formula Atom Agent :=
  agents.foldr Formula.box φ

theorem satisfies_boxes_iff {World : Type u} {Atom : Type v} {Agent : Type t}
    (M : Model World Atom Agent) (agents : List Agent)
    (φ : Formula Atom Agent) (w : World) :
    M.Satisfies w (boxes agents φ) ↔
      ∀ v, Path M agents w v → M.Satisfies v φ := by
  induction agents generalizing w with
  | nil =>
      simp [boxes, Path]
  | cons i is ih =>
      constructor
      · intro h v ⟨z, hxz, hzv⟩
        exact (ih z).mp (h z hxz) v hzv
      · intro h z hxz
        apply (ih z).mpr
        intro v hzv
        exact h v ⟨z, hxz, hzv⟩

/-- The diagonal valuation: `D` holds exactly if no last-agent edge returns
to the starting point after traversing the preceding agents' relations. -/
def Wrong {World : Type u} {Atom : Type v} {Agent : Type t}
    (M : Model World Atom Agent) (chain : List Agent) (last : Agent)
    (w : World) : Prop :=
  ∀ v, Path M chain w v → ¬ M.rel last v w

theorem path_exists_of_serial {World : Type u} {Atom : Type v} {Agent : Type t}
    (M : Model World Atom Agent) (chain : List Agent)
    (hserial : ∀ i ∈ chain, ∀ w, ∃ v, M.rel i w v) (w : World) :
    ∃ v, Path M chain w v := by
  induction chain generalizing w with
  | nil => exact ⟨w, rfl⟩
  | cons i is ih =>
      obtain ⟨z, hxz⟩ := hserial i (by simp) w
      obtain ⟨v, hzv⟩ := ih (by
        intro j hj x
        exact hserial j (by simp [hj]) x) z
      exact ⟨v, z, hxz, hzv⟩

/-- Proposition 2: no state satisfies the chain of beliefs followed by the
assumption of `D`, provided `D` has the prescribed diagonal valuation.
Seriality is needed only for the agents before the final assumption. -/
theorem bk_paradox_many {World : Type u} {Atom : Type v} {Agent : Type t}
    (M : Model World Atom Agent) (chain : List Agent) (last : Agent) (D : Atom)
    (hserial : ∀ i ∈ chain, ∀ w, ∃ v, M.rel i w v)
    (hD : ∀ w, M.val D w ↔ Wrong M chain last w) (w : World) :
    ¬ M.Satisfies w (boxes chain (.assume last (.atom D))) := by
  intro h
  have hchain : ∀ v, Path M chain w v →
      (M.rel last v w ↔ M.val D w) := by
    intro v hp
    exact ((satisfies_boxes_iff M chain (.assume last (.atom D)) w).mp h v hp) w
  by_cases hd : M.val D w
  · obtain ⟨v, hp⟩ := path_exists_of_serial M chain hserial w
    exact ((hD w).mp hd v hp) ((hchain v hp).mpr hd)
  · apply hd
    apply (hD w).mpr
    intro v hp hvw
    exact hd ((hchain v hp).mp hvw)

/-- The diagonal valuation for the two-agent statement in Proposition 1. -/
theorem wrong_two_iff {World : Type u} {Atom : Type v} {Agent : Type t}
    (M : Model World Atom Agent) (a b : Agent) (w : World) :
    Wrong M [a] b w ↔
      ∀ v, M.rel a w v → ¬ M.rel b v w := by
  constructor
  · intro h v hav hbv
    exact h v ⟨v, hav, rfl⟩ hbv
  · intro h v ⟨z, haz, hzv⟩
    subst v
    exact h z haz

/-- Proposition 1, stated with the paper's two serial accessibility relations. -/
theorem bk_paradox_two {World : Type u} {Atom : Type v} {Agent : Type t}
    (M : Model World Atom Agent) (a b : Agent) (D : Atom)
    (ha : ∀ w, ∃ v, M.rel a w v)
    (_hb : ∀ w, ∃ v, M.rel b w v)
    (hD : ∀ w, M.val D w ↔
      ∀ v, M.rel a w v → ¬ M.rel b v w) (w : World) :
    ¬ M.Satisfies w (.box a (.assume b (.atom D))) := by
  have hD' : ∀ x, M.val D x ↔ Wrong M [a] b x := by
    intro x
    exact (hD x).trans (wrong_two_iff M a b x).symm
  exact bk_paradox_many M [a] b D (by
    intro i hi x
    simp only [List.mem_singleton] at hi
    subst i
    exact ha x) hD' w

/-- The BK formula is a fixed point of the Moore function for Ann whenever
the diagonal valuation holds: the additional `¬□ₐ` conjunct is automatic. -/
theorem bk_moore_fixed_point {World : Type u} {Atom : Type v} {Agent : Type t}
    (M : Model World Atom Agent) (a b : Agent) (D : Atom)
    (ha : ∀ w, ∃ v, M.rel a w v)
    (hb : ∀ w, ∃ v, M.rel b w v)
    (hD : ∀ w, M.val D w ↔
      ∀ v, M.rel a w v → ¬ M.rel b v w) (w : World) :
    M.Satisfies w (.assume b (.atom D)) ↔
      M.Satisfies w (.conj (.assume b (.atom D))
        (.neg (.box a (.assume b (.atom D))))) := by
  constructor
  · intro hφ
    exact ⟨hφ, bk_paradox_two M a b D ha hb hD w⟩
  · exact And.left

/-- A serial two-world model in which Bob's assumption about `D` is true,
although Ann cannot believe that assumption by Proposition 1.  Ann always
accesses `true`; Bob accesses only his current world.  The diagonal atom is
true precisely at `false`. -/
def assumptionWitness : Model Bool Unit Bool where
  rel i x y := if i then y = x else y = true
  val _ x := x = false

theorem assumptionWitness_serial (i : Bool) (x : Bool) :
    ∃ y, assumptionWitness.rel i x y := by
  cases i
  · exact ⟨true, rfl⟩
  · exact ⟨x, rfl⟩

theorem assumptionWitness_diagonal (w : Bool) :
    assumptionWitness.val () w ↔
      ∀ v, assumptionWitness.rel false w v →
        ¬ assumptionWitness.rel true v w := by
  cases w <;> simp [assumptionWitness]

theorem assumption_satisfiable_in_serial_model :
    ∃ M : Model Bool Unit Bool,
      (∀ i x, ∃ y, M.rel i x y) ∧
      (∀ w, M.val () w ↔
        ∀ v, M.rel false w v → ¬ M.rel true v w) ∧
      M.Satisfies false (.assume true (.atom ())) := by
  refine ⟨assumptionWitness, assumptionWitness_serial,
    assumptionWitness_diagonal, ?_⟩
  intro v
  cases v <;> simp [assumptionWitness, Model.Satisfies]

end SourcesOfUnknowability.BK
