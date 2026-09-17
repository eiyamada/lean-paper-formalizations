import EventualAndStrongEventualNotionsInPublicAnnouncements.RichLocality

/-! Model operations for formulas containing common belief and announcements. -/

namespace ClassificationSigmaValidity.Model

open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

abbrev rSatisfies (M : Model World Atom Agent) (x : World)
    (φ : BPALCFormula Atom Agent) : Prop := BPALC.InitiallySatisfies M x φ

abbrev rUpdate (M : Model World Atom Agent) (φ : BPALCFormula Atom Agent) :=
  BPALC.update M φ

abbrev rIterateUpdate (M : Model World Atom Agent) (φ : BPALCFormula Atom Agent) :=
  BPALC.iterate M φ

def rTrace (M : Model World Atom Agent) (x : World)
    (φ : BPALCFormula Atom Agent) (n : Nat) : Prop :=
  (M.rIterateUpdate φ n).rSatisfies x φ

@[simp] theorem rUpdate_rel (M : Model World Atom Agent) (φ : BPALCFormula Atom Agent)
    (a : Agent) (x y : World) :
    (M.rUpdate φ).rel a x y ↔ M.rel a x y ∧ M.rSatisfies y φ := Iff.rfl

@[simp] theorem rUpdate_val (M : Model World Atom Agent) (φ : BPALCFormula Atom Agent)
    (p : Atom) (x : World) : (M.rUpdate φ).val p x ↔ M.val p x := Iff.rfl

@[simp] theorem rIterateUpdate_zero (M : Model World Atom Agent) (φ : BPALCFormula Atom Agent) :
    M.rIterateUpdate φ 0 = M := rfl

@[simp] theorem rIterateUpdate_succ (M : Model World Atom Agent)
    (φ : BPALCFormula Atom Agent) (n : Nat) :
    M.rIterateUpdate φ (n + 1) = (M.rIterateUpdate φ n).rUpdate φ := rfl

@[simp] theorem rIterateUpdate_val (M : Model World Atom Agent)
    (φ : BPALCFormula Atom Agent) (n : Nat) (p : Atom) (x : World) :
    (M.rIterateUpdate φ n).val p x ↔ M.val p x := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [rIterateUpdate_succ, rUpdate_val] using ih

@[simp] theorem rTrace_zero (M : Model World Atom Agent) (x : World)
    (φ : BPALCFormula Atom Agent) : M.rTrace x φ 0 ↔ M.rSatisfies x φ := Iff.rfl

theorem rIterateUpdate_add (M : Model World Atom Agent) (φ : BPALCFormula Atom Agent)
    (n m : Nat) : M.rIterateUpdate φ (n + m) = (M.rIterateUpdate φ n).rIterateUpdate φ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Nat.add_succ, rIterateUpdate_succ, rIterateUpdate_succ, ih]

theorem rUpdate_isK45 {M : Model World Atom Agent} (hM : IsK45 M)
    (φ : BPALCFormula Atom Agent) : IsK45 (M.rUpdate φ) := BPALC.update_isK45 M hM φ

theorem rIterateUpdate_isK45 {M : Model World Atom Agent} (hM : IsK45 M)
    (φ : BPALCFormula Atom Agent) (n : Nat) : IsK45 (M.rIterateUpdate φ n) :=
  BPALC.iterate_isK45 M hM φ n

def rSurvives (M : Model World Atom Agent) (φ : BPALCFormula Atom Agent)
    (n : Nat) (y : World) : Prop := ∀ m, m < n → (M.rIterateUpdate φ m).rSatisfies y φ

@[simp] theorem rSurvives_zero (M : Model World Atom Agent) (φ : BPALCFormula Atom Agent)
    (y : World) : M.rSurvives φ 0 y := by simp [rSurvives]

theorem rSurvives_succ_iff (M : Model World Atom Agent) (φ : BPALCFormula Atom Agent)
    (n : Nat) (y : World) : M.rSurvives φ (n + 1) y ↔
      M.rSurvives φ n y ∧ (M.rIterateUpdate φ n).rSatisfies y φ := by
  constructor
  · intro h
    exact ⟨fun m hm => h m (Nat.lt.step hm), h n (Nat.lt_succ_self n)⟩
  · rintro ⟨h, hn⟩ m hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
    · exact h m hm
    · exact hn

theorem rIterateUpdate_rel_iff (M : Model World Atom Agent) (φ : BPALCFormula Atom Agent)
    (n : Nat) (a : Agent) (x y : World) :
    (M.rIterateUpdate φ n).rel a x y ↔ M.rel a x y ∧ M.rSurvives φ n y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [rIterateUpdate_succ, rUpdate_rel, ih, rSurvives_succ_iff]
      exact and_assoc

theorem rIterateUpdate_rel_antitone (M : Model World Atom Agent)
    (φ : BPALCFormula Atom Agent) {m n : Nat} (hmn : m ≤ n)
    {a : Agent} {x y : World} (h : (M.rIterateUpdate φ n).rel a x y) :
    (M.rIterateUpdate φ m).rel a x y := by
  rw [rIterateUpdate_rel_iff] at h ⊢
  exact ⟨h.1, fun k hk => h.2 k (Nat.lt_of_lt_of_le hk hmn)⟩

theorem rSatisfies_congr {M N : Model World Atom Agent} (h : M = N)
    (x : World) (φ : BPALCFormula Atom Agent) :
    M.rSatisfies x φ ↔ N.rSatisfies x φ := by rw [h]

theorem rForwardClosed_iterateUpdate {M : Model World Atom Agent} {U : Set World}
    (hU : M.ForwardClosed U) (φ : BPALCFormula Atom Agent) (n : Nat) :
    (M.rIterateUpdate φ n).ForwardClosed U := by
  intro x hx a y hxy
  exact hU hx a ((M.rIterateUpdate_rel_iff φ n a x y).mp hxy).1

end ClassificationSigmaValidity.Model
