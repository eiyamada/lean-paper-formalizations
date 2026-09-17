import EventualAndStrongEventualNotionsInPublicAnnouncements.Definitions

/-!
# One-peeling models

A common head cluster feeds finite alternating branches of every positive
length. An optional persistent target supplies the variant used by Lemma 12.
The branch indexed by `m` has length `m + 1`; thus indices start at zero here,
whereas the manuscript indexes these branches by their positive lengths.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements
namespace OnePeeling

open ClassificationSigmaValidity

/-- The extra state is inaccessible when `keep = false`, so it does not belong
to the root-generated standard one-peeling model. -/
inductive World where
  | root
  | persistent
  | node (m : Nat) (j : Fin (m + 2))
  deriving DecidableEq

/-- Agents `false` and `true` are the manuscript's `a` and `b`. -/
def block : Bool → World → Nat × Nat
  | false, .root => (0, 0)
  | false, .persistent => (0, 0)
  | false, .node m j => if j.val = 0 then (0, 0) else (m + 1, (j.val + 1) / 2)
  | true, .root => (0, 0)
  | true, .persistent => (0, 0)
  | true, .node m j => (m + 1, j.val / 2)

def target (keep : Bool) : Bool → World → Prop
  | _, .root => False
  | false, .persistent => keep = true
  | true, .persistent => False
  | false, .node _ j => j.val % 2 = 0
  | true, .node _ j => j.val % 2 = 1

/-- Branch targets are removed from their ends, one position per update. -/
def alive (n : Nat) : World → Prop
  | .root => True
  | .persistent => True
  | .node m j => n ≤ m + 1 - j.val

/-- Atoms 0,1,2,3 represent r,t,s,p respectively. -/
def valuation : Nat → World → Prop
  | 0, .root => True
  | 2, .node _ j => j.val % 2 = 1
  | 3, .node m j => j.val = 0 ∧ (m + 1) % 2 = 0
  | 1, .persistent => True
  | _, _ => False

def modelAt (keep : Bool) (n : Nat) : Model World Nat Bool where
  rel a x y := block a x = block a y ∧ target keep a y ∧ alive n y
  val := valuation

/-- Every stage is K45: all sources in a block share the surviving targets. -/
theorem modelAt_isK45 (keep : Bool) (n : Nat) : IsK45 (modelAt keep n) := by
  intro a
  constructor
  · rintro x y z ⟨hxy, _⟩ ⟨hyz, hz⟩
    exact ⟨hxy.trans hyz, hz⟩
  · rintro x y z ⟨hxy, _⟩ ⟨hxz, hz⟩
    exact ⟨hxy.symm.trans hxz, hz⟩

theorem rel_antitone (keep : Bool) {n k : Nat} (hnk : n ≤ k)
    {a : Bool} {x y : World} :
    (modelAt keep k).rel a x y → (modelAt keep n).rel a x y := by
  rintro ⟨hblock, htarget, halive⟩
  refine ⟨hblock, htarget, ?_⟩
  cases y with
  | root => trivial
  | persistent => trivial
  | node m j => exact hnk.trans halive

@[simp] theorem no_root_target (keep : Bool) (n : Nat) (a : Bool) (x : World) :
    ¬ (modelAt keep n).rel a x .root := by
  simp [modelAt, target]

@[simp] theorem root_b_empty (keep : Bool) (n : Nat) (y : World) :
    ¬ (modelAt keep n).rel true .root y := by
  cases y <;> simp [modelAt, block, target]

@[simp] theorem persistent_b_empty (keep : Bool) (n : Nat) (y : World) :
    ¬ (modelAt keep n).rel true .persistent y := by
  cases y <;> simp [modelAt, block, target]

/-- The root sees exactly the surviving branch heads through agent a. -/
theorem root_head_iff (keep : Bool) (n m : Nat) (j : Fin (m + 2)) :
    (modelAt keep n).rel false .root (.node m j) ↔
      j.val = 0 ∧ n ≤ m + 1 := by
  by_cases hj : j.val = 0
  · have hj' : j = 0 := Fin.ext hj
    simp [modelAt, block, target, alive, hj']
  · have hj' : j ≠ 0 := fun h => hj (congrArg Fin.val h)
    simp [modelAt, block, target, alive, hj']

@[simp] theorem root_persistent_iff (keep : Bool) (n : Nat) :
    (modelAt keep n).rel false .root .persistent ↔ keep = true := by
  simp [modelAt, block, target, alive]

/-- At an odd position the forward a-edge leads to the next even position. -/
theorem node_a_forward_iff (keep : Bool) (n m k : Nat)
    (j : Fin (m + 2)) (l : Fin (k + 2)) (hj : j.val % 2 = 1) :
    (modelAt keep n).rel false (.node m j) (.node k l) ↔
      k = m ∧ l.val = j.val + 1 ∧ n ≤ k + 1 - l.val := by
  have hj0 : j.val ≠ 0 := by omega
  by_cases hl0 : l.val = 0
  · simp only [modelAt, block, hj0, hl0, ↓reduceIte, target, alive]
    simp only [Prod.mk.injEq]
    omega
  · simp only [modelAt, block, hj0, hl0, ↓reduceIte, target, alive]
    simp only [Prod.mk.injEq]
    omega

/-- At an even position the forward b-edge leads to the next odd position. -/
theorem node_b_forward_iff (keep : Bool) (n m k : Nat)
    (j : Fin (m + 2)) (l : Fin (k + 2)) (hj : j.val % 2 = 0) :
    (modelAt keep n).rel true (.node m j) (.node k l) ↔
      k = m ∧ l.val = j.val + 1 ∧ n ≤ k + 1 - l.val := by
  simp only [modelAt, block, target, alive, Prod.mk.injEq]
  omega

/-- Neither exceptional state is a forward target from an odd branch position. -/
theorem node_a_no_persistent (keep : Bool) (n m : Nat)
    (j : Fin (m + 2)) (hj : j.val % 2 = 1) :
    ¬ (modelAt keep n).rel false (.node m j) .persistent := by
  have hj0 : j.val ≠ 0 := by omega
  have hj' : j ≠ 0 := fun h => hj0 (congrArg Fin.val h)
  simp [modelAt, block, target, alive, hj']

/-- The agent that follows a branch away from its head. -/
def activeAgent (j : Nat) : Bool := decide (j % 2 = 0)

theorem node_active_forward_iff (keep : Bool) (n m k : Nat)
    (j : Fin (m + 2)) (l : Fin (k + 2)) :
    (modelAt keep n).rel (activeAgent j.val) (.node m j) (.node k l) ↔
      k = m ∧ l.val = j.val + 1 ∧ n ≤ k + 1 - l.val := by
  by_cases hj : j.val % 2 = 0
  · simpa [activeAgent, hj] using node_b_forward_iff keep n m k j l hj
  · have hj' : j.val % 2 = 1 := by omega
    simpa [activeAgent, hj] using node_a_forward_iff keep n m k j l hj'

theorem node_active_no_persistent (keep : Bool) (n m : Nat)
    (j : Fin (m + 2)) :
    ¬ (modelAt keep n).rel (activeAgent j.val) (.node m j) .persistent := by
  by_cases hj : j.val % 2 = 0
  · simp [activeAgent, hj, modelAt, target]
  · have hj' : j.val % 2 = 1 := by omega
    simpa [activeAgent, hj] using node_a_no_persistent keep n m j hj'

/-- A forward diamond at a branch state tests just its next surviving position. -/
theorem node_forward_dia_iff (keep : Bool) (n m : Nat)
    (j : Fin (m + 2)) (χ : Formula Nat Bool) :
    (modelAt keep n).Satisfies (.node m j) (Formula.dia (activeAgent j.val) χ) ↔
      ∃ l : Fin (m + 2), l.val = j.val + 1 ∧ n ≤ m + 1 - l.val ∧
        (modelAt keep n).Satisfies (.node m l) χ := by
  classical
  rw [Model.satisfies_dia]
  constructor
  · rintro ⟨y, hy, hχ⟩
    cases y with
    | root => exact (no_root_target keep n _ _ hy).elim
    | persistent => exact (node_active_no_persistent keep n m j hy).elim
    | node k l =>
        obtain ⟨hkm, hl, hn⟩ := (node_active_forward_iff keep n m k j l).mp hy
        subst k
        exact ⟨l, hl, hn, hχ⟩
  · rintro ⟨l, hl, hn, hχ⟩
    exact ⟨.node m l, (node_active_forward_iff keep n m m j l).mpr ⟨rfl, hl, hn⟩, hχ⟩

/-- Forward accessibility disappears exactly when the remaining rank is reached. -/
theorem node_forward_nonempty_iff (keep : Bool) (n m : Nat)
    (j : Fin (m + 2)) :
    (∃ y, (modelAt keep n).rel (activeAgent j.val) (.node m j) y) ↔
      n < m + 1 - j.val := by
  constructor
  · rintro ⟨y, hy⟩
    cases y with
    | root => exact (no_root_target keep n _ _ hy).elim
    | persistent => exact (node_active_no_persistent keep n m j hy).elim
    | node k l =>
        obtain ⟨hkm, hl, hn⟩ := (node_active_forward_iff keep n m k j l).mp hy
        have hjbound := j.isLt
        omega
  · intro hn
    let l : Fin (m + 2) := ⟨j.val + 1, by omega⟩
    refine ⟨.node m l, (node_active_forward_iff keep n m m j l).mpr ?_⟩
    refine ⟨rfl, rfl, ?_⟩
    dsimp [l]
    omega

/-- The alternating path operator used in the one-peeling witnesses. -/
def L (χ : Formula Nat Bool) : Formula Nat Bool :=
  Formula.or
    (.conj (.atom 2) (Formula.dia false
      (.conj (.neg (.atom 0)) (.conj (.neg (.atom 2)) χ))))
    (.conj (.neg (.atom 2)) (Formula.dia true
      (.conj (.neg (.atom 0)) (.conj (.atom 2) χ))))

def D : Formula Nat Bool := L Formula.verum

@[simp] theorem root_L_false (keep : Bool) (n : Nat) (χ : Formula Nat Bool) :
    ¬ (modelAt keep n).Satisfies .root (L χ) := by
  classical
  have hs : ¬ (modelAt keep n).Satisfies .root (.atom 2) := by
    simp [Model.Satisfies, modelAt, valuation]
  simp only [L, Model.satisfies_or, Model.satisfies_and, Model.satisfies_neg, hs,
    false_and, not_false_eq_true, true_and, false_or, Model.satisfies_dia]
  rintro ⟨y, hy, _⟩
  exact root_b_empty keep n y hy

@[simp] theorem persistent_L_false (keep : Bool) (n : Nat) (χ : Formula Nat Bool) :
    ¬ (modelAt keep n).Satisfies .persistent (L χ) := by
  classical
  have hs : ¬ (modelAt keep n).Satisfies .persistent (.atom 2) := by
    simp [Model.Satisfies, modelAt, valuation]
  simp only [L, Model.satisfies_or, Model.satisfies_and, Model.satisfies_neg, hs,
    false_and, not_false_eq_true, true_and, false_or, Model.satisfies_dia]
  rintro ⟨y, hy, _⟩
  exact persistent_b_empty keep n y hy

/-- At a branch position, L has exactly the intended next-position semantics. -/
theorem node_L_iff (keep : Bool) (n m : Nat)
    (j : Fin (m + 2)) (χ : Formula Nat Bool) :
    (modelAt keep n).Satisfies (.node m j) (L χ) ↔
      ∃ l : Fin (m + 2), l.val = j.val + 1 ∧ n ≤ m + 1 - l.val ∧
        (modelAt keep n).Satisfies (.node m l) χ := by
  classical
  by_cases hj : j.val % 2 = 0
  · have hs : ¬ (modelAt keep n).Satisfies (.node m j) (.atom 2) := by
      simp [Model.Satisfies, modelAt, valuation, hj]
    simp only [L, Model.satisfies_or, Model.satisfies_and, Model.satisfies_neg, hs,
      false_and, not_false_eq_true, true_and, false_or]
    have hactive : activeAgent j.val = true := by simp [activeAgent, hj]
    rw [← hactive, node_forward_dia_iff]
    apply exists_congr
    intro l
    constructor
    · rintro ⟨hl, hn, hχ⟩
      exact ⟨hl, hn, hχ.2.2⟩
    · rintro ⟨hl, hn, hχ⟩
      refine ⟨hl, hn, ?_, ?_, hχ⟩
      · simp [Model.Satisfies, modelAt, valuation]
      · change l.val % 2 = 1
        omega
  · have hj' : j.val % 2 = 1 := by omega
    have hs : (modelAt keep n).Satisfies (.node m j) (.atom 2) := by
      simp [Model.Satisfies, modelAt, valuation, hj']
    simp only [L, Model.satisfies_or, Model.satisfies_and, Model.satisfies_neg, hs,
      true_and, not_true_eq_false, false_and, or_false]
    have hactive : activeAgent j.val = false := by simp [activeAgent, hj]
    rw [← hactive, node_forward_dia_iff]
    apply exists_congr
    intro l
    constructor
    · rintro ⟨hl, hn, hχ⟩
      exact ⟨hl, hn, hχ.2.2⟩
    · rintro ⟨hl, hn, hχ⟩
      refine ⟨hl, hn, ?_, ?_, hχ⟩
      · simp [Model.Satisfies, modelAt, valuation]
      · change ¬ l.val % 2 = 1
        omega

/-- The path-existence formula has the exact finite rank behavior of the paper. -/
theorem node_D_iff (keep : Bool) (n m : Nat) (j : Fin (m + 2)) :
    (modelAt keep n).Satisfies (.node m j) D ↔ n < m + 1 - j.val := by
  rw [D, node_L_iff]
  simp only [Model.satisfies_verum, and_true]
  constructor
  · rintro ⟨l, hl, hn⟩
    have hbound := j.isLt
    omega
  · intro hn
    refine ⟨⟨j.val + 1, by omega⟩, rfl, ?_⟩
    change n ≤ m + 1 - (j.val + 1)
    omega

/-- A formula with the indicated truth values at targets realizes one step of
this exact peeling sequence. The root's truth value is unrestricted. -/
theorem update_eq_next (keep : Bool) (n : Nat) (φ : Formula Nat Bool)
    (hnode : ∀ m (j : Fin (m + 2)),
      (modelAt keep n).Satisfies (.node m j) φ ↔ n < m + 1 - j.val)
    (hpersistent : keep = true → (modelAt keep n).Satisfies .persistent φ) :
    (modelAt keep n).update φ = modelAt keep (n + 1) := by
  apply Model.ext'
  · intro a x y
    cases y with
    | root => simp [Model.update_rel, modelAt, target]
    | persistent =>
        cases a <;> simp only [Model.update_rel, modelAt, target, alive]
        · constructor
          · rintro ⟨h, _⟩
            exact h
          · intro h
            exact ⟨h, hpersistent h.2.1⟩
        · simp
    | node m j =>
        rw [Model.update_rel, hnode]
        change
          ((block a x = block a (.node m j) ∧ target keep a (.node m j) ∧
            n ≤ m + 1 - j.val) ∧ n < m + 1 - j.val) ↔
          (block a x = block a (.node m j) ∧ target keep a (.node m j) ∧
            n + 1 ≤ m + 1 - j.val)
        constructor
        · rintro ⟨⟨hb, ht, hn⟩, hl⟩
          exact ⟨hb, ht, by omega⟩
        · rintro ⟨hb, ht, hn⟩
          exact ⟨⟨hb, ht, by omega⟩, by omega⟩
  · intro p x
    rfl

/-- The recurrence needs the truth description only for still-surviving
branch targets; this form also applies to completion formulas. -/
theorem update_eq_next_of_alive (keep : Bool) (n : Nat) (φ : Formula Nat Bool)
    (hnode : ∀ m (j : Fin (m + 2)), n ≤ m + 1 - j.val →
      ((modelAt keep n).Satisfies (.node m j) φ ↔ n < m + 1 - j.val))
    (hpersistent : keep = true → (modelAt keep n).Satisfies .persistent φ) :
    (modelAt keep n).update φ = modelAt keep (n + 1) := by
  apply Model.ext'
  · intro a x y
    cases y with
    | root => simp [Model.update_rel, modelAt, target]
    | persistent =>
        cases a <;> simp only [Model.update_rel, modelAt, target, alive]
        · exact ⟨And.left, fun h => ⟨h, hpersistent h.2.1⟩⟩
        · simp
    | node m j =>
        by_cases hn : n ≤ m + 1 - j.val
        · rw [Model.update_rel, hnode m j hn]
          change
            ((block a x = block a (.node m j) ∧ target keep a (.node m j) ∧
              n ≤ m + 1 - j.val) ∧ n < m + 1 - j.val) ↔
            (block a x = block a (.node m j) ∧ target keep a (.node m j) ∧
              n + 1 ≤ m + 1 - j.val)
          constructor
          · rintro ⟨⟨hb, ht, hn⟩, hl⟩
            exact ⟨hb, ht, by omega⟩
          · rintro ⟨hb, ht, hn⟩
            exact ⟨⟨hb, ht, by omega⟩, by omega⟩
        · have hn' : ¬ n + 1 ≤ m + 1 - j.val := by omega
          simp [Model.update_rel, modelAt, alive, hn, hn']
  · intro p x
    rfl

theorem iterate_eq_of_alive (keep : Bool) (φ : Formula Nat Bool)
    (hnode : ∀ n m (j : Fin (m + 2)), n ≤ m + 1 - j.val →
      ((modelAt keep n).Satisfies (.node m j) φ ↔ n < m + 1 - j.val))
    (hpersistent : ∀ n, keep = true → (modelAt keep n).Satisfies .persistent φ) :
    ∀ n, (modelAt keep 0).iterateUpdate φ n = modelAt keep n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Model.iterateUpdate_succ, ih,
        update_eq_next_of_alive keep n φ (hnode n) (hpersistent n)]

/-- The preceding target-wise condition identifies all actual finite iterates. -/
theorem iterate_eq (keep : Bool) (φ : Formula Nat Bool)
    (hnode : ∀ n m (j : Fin (m + 2)),
      (modelAt keep n).Satisfies (.node m j) φ ↔ n < m + 1 - j.val)
    (hpersistent : ∀ n, keep = true → (modelAt keep n).Satisfies .persistent φ) :
    ∀ n, (modelAt keep 0).iterateUpdate φ n = modelAt keep n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Model.iterateUpdate_succ, ih, update_eq_next keep n φ (hnode n) (hpersistent n)]

/-- The intersection at omega retains only the optional persistent target. -/
def modelLimit (keep : Bool) : Model World Nat Bool where
  rel a x y := block a x = block a y ∧ target keep a y ∧ y = .persistent
  val := valuation

theorem modelLimit_isK45 (keep : Bool) : IsK45 (modelLimit keep) := by
  intro a
  constructor
  · rintro x y z ⟨hxy, _⟩ ⟨hyz, hz⟩
    exact ⟨hxy.trans hyz, hz⟩
  · rintro x y z ⟨hxy, _⟩ ⟨hxz, hz⟩
    exact ⟨hxy.symm.trans hxz, hz⟩

theorem rel_allStages_iff_limit (keep : Bool) (a : Bool) (x y : World) :
    (∀ n, (modelAt keep n).rel a x y) ↔ (modelLimit keep).rel a x y := by
  cases y with
  | root => simp [modelAt, modelLimit, target]
  | persistent => simp [modelAt, modelLimit, alive]
  | node m j =>
      constructor
      · intro h
        have hn := (h (m + 2)).2.2
        change m + 2 ≤ m + 1 - j.val at hn
        omega
      · intro h
        exact (World.noConfusion h.2.2)

@[simp] theorem modelLimit_false_rel (a : Bool) (x y : World) :
    ¬ (modelLimit false).rel a x y := by
  rintro ⟨_, ht, rfl⟩
  cases a <;> simp [target] at ht

theorem modelLimit_update_eq (keep : Bool) (φ : Formula Nat Bool)
    (hpersistent : keep = true → (modelLimit keep).Satisfies .persistent φ) :
    (modelLimit keep).update φ = modelLimit keep := by
  apply Model.ext'
  · intro a x y
    rw [Model.update_rel]
    constructor
    · exact And.left
    · intro h
      refine ⟨h, ?_⟩
      obtain ⟨_, ht, rfl⟩ := h
      cases a with
      | false => exact hpersistent ht
      | true => exact ht.elim
  · intro p x
    rfl

end OnePeeling
end EventualAndStrongEventualNotionsInPublicAnnouncements
