import EventualAndStrongEventualNotionsInPublicAnnouncements.RichDefinitions

/-!
# Finite eventuality for the richer language

The trace arguments in Lemma `lem:finite-eventual-facts` and Theorem
`thm:finite-classification`. `CofinalValue true` is the binary limsup-one
condition, `CofinalValue false` the binary liminf-zero condition, and
`ConvergesTo` expresses convergence of a binary sequence without choosing an
embedding into the real numbers. Uniform boundedness is kept separate from
eventuality. No converse from eventuality to a uniform bound is asserted for
this richer language, which need not be compact.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements.Rich

open ClassificationSigmaValidity

universe u v w

variable {Atom : Type v} {Agent : Type w}
variable {φ : BPALCFormula Atom Agent} {i j : Bool}

/-- Restarting announcements at stage `m` shifts the trace by `m`. -/
theorem trace_shift {World : Type u} (M : Model World Atom Agent)
    (x : World) (φ : BPALCFormula Atom Agent) (m n : Nat) :
    (M.rIterateUpdate φ m).rTrace x φ n ↔ M.rTrace x φ (m + n) := by
  unfold Model.rTrace
  rw [Model.rIterateUpdate_add]

theorem strongEventual_implies_eventual (h : StrongEventual.{u} i j φ) :
    Eventual.{u} i j φ := by
  intro World M hM x hx
  obtain ⟨N, hN, htail⟩ := h M hM x hx
  exact ⟨N, hN, htail N le_rfl⟩

/-- Allowing threshold zero does not change strong eventuality. -/
theorem strongEventual_iff_conditional_convergence :
    StrongEventual.{u} i j φ ↔
      ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
        HoldsBit i (M.rSatisfies x φ) → ConvergesTo j (M.rTrace x φ) := by
  constructor
  · intro h World M hM x hx
    obtain ⟨N, _, htail⟩ := h M hM x hx
    exact ⟨N, htail⟩
  · intro h World M hM x hx
    obtain ⟨N, htail⟩ := h M hM x hx
    exact ⟨max N 1, le_max_right _ _, fun n hn =>
      htail n (le_trans (le_max_left _ _) hn)⟩

/-- Every occurrence of the initial value produces a strictly later one. -/
theorem eventual_same_iff_cofinal :
    Eventual.{u} i i φ ↔
      ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
        HoldsBit i (M.rSatisfies x φ) → CofinalValue i (M.rTrace x φ) := by
  constructor
  · intro h World M hM x hx N
    induction N with
    | zero => exact ⟨0, Nat.zero_le _, hx⟩
    | succ N ih =>
      obtain ⟨m, hm, hvalue⟩ := ih
      obtain ⟨n, hn, hnext⟩ := h (M.rIterateUpdate φ m)
        (M.rIterateUpdate_isK45 hM φ m) x hvalue
      refine ⟨m + n, by omega, ?_⟩
      exact (holdsBit_congr i (trace_shift M x φ m n)).mp hnext
  · intro h World M hM x hx
    obtain ⟨n, hn, hvalue⟩ := h M hM x hx 1
    exact ⟨n, hn, hvalue⟩

/-- Reversal eventuality removes the condition on the initial truth value. -/
theorem eventual_reversal_iff_cofinal :
    Eventual.{u} (!j) j φ ↔
      ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
        CofinalValue j (M.rTrace x φ) := by
  classical
  constructor
  · intro h World M hM x N
    by_cases hv : HoldsBit j (M.rTrace x φ N)
    · exact ⟨N, le_rfl, hv⟩
    · have hstart : HoldsBit (!j) ((M.rIterateUpdate φ N).rSatisfies x φ) :=
        (holdsBit_not_iff j _).mpr hv
      obtain ⟨n, hn, hnext⟩ := h (M.rIterateUpdate φ N)
        (M.rIterateUpdate_isK45 hM φ N) x hstart
      exact ⟨N + n, by omega,
        (holdsBit_congr j (trace_shift M x φ N n)).mp hnext⟩
  · intro h World M hM x _
    obtain ⟨n, hn, hvalue⟩ := h M hM x 1
    exact ⟨n, hn, hvalue⟩

/-- For reversals, strong eventuality is unconditional trace convergence. -/
theorem strongEventual_reversal_iff_convergence :
    StrongEventual.{u} (!j) j φ ↔
      ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
        ConvergesTo j (M.rTrace x φ) := by
  classical
  constructor
  · intro h World M hM x
    by_cases hex : ∃ m, HoldsBit (!j) (M.rTrace x φ m)
    · obtain ⟨m, hm⟩ := hex
      obtain ⟨N, _, htail⟩ := h (M.rIterateUpdate φ m)
        (M.rIterateUpdate_isK45 hM φ m) x hm
      refine ⟨m + N, fun n hn => ?_⟩
      have hmle : m ≤ n := by omega
      have hNle : N ≤ n - m := by omega
      have hvalue := (holdsBit_congr j (trace_shift M x φ m (n - m))).mp
        (htail (n - m) hNle)
      simpa only [Nat.add_sub_of_le hmle] using hvalue
    · refine ⟨0, fun n _ => ?_⟩
      have hn : ¬ HoldsBit (!j) (M.rTrace x φ n) := fun hn => hex ⟨n, hn⟩
      simpa only [holdsBit_not_iff, not_not] using hn
  · intro h
    apply strongEventual_iff_conditional_convergence.mpr
    intro World M hM x _
    exact h M hM x

/-- A common form of the four cofinal-value characterizations. -/
theorem eventual_iff_conditional_cofinal :
    Eventual.{u} i j φ ↔
      ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
        HoldsBit i (M.rSatisfies x φ) → CofinalValue j (M.rTrace x φ) := by
  constructor
  · intro h
    by_cases hij : i = j
    · subst j
      exact eventual_same_iff_cofinal.mp h
    · have hi : i = !j := by cases i <;> cases j <;> simp_all
      subst i
      exact fun M hM x _ => (eventual_reversal_iff_cofinal (j := j)).mp h M hM x
  · intro h World M hM x hx
    obtain ⟨n, hn, hvalue⟩ := h M hM x hx 1
    exact ⟨n, hn, hvalue⟩

/-- On a trace that becomes constant, eventuality determines its final value. -/
theorem eventual_value_at_stable_stage (h : Eventual.{u} i j φ)
    {World : Type u} (M : Model World Atom Agent) (hM : IsK45 M)
    (x : World) (hx : HoldsBit i (M.rSatisfies x φ)) (N : Nat)
    (hstable : ∀ n, N ≤ n → (M.rTrace x φ n ↔ M.rTrace x φ N)) :
    HoldsBit j (M.rTrace x φ N) := by
  obtain ⟨n, hn, hvalue⟩ := eventual_iff_conditional_cofinal.mp h M hM x hx N
  exact (holdsBit_congr j (hstable n hn)).mp hvalue

theorem eventual_true_lie_iff_cofinal_true :
    Eventual.{u} false true φ ↔
      ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
        CofinalValue true (M.rTrace x φ) :=
  eventual_reversal_iff_cofinal (j := true) (φ := φ)

theorem eventual_self_refuting_iff_cofinal_false :
    Eventual.{u} true false φ ↔
      ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
        CofinalValue false (M.rTrace x φ) :=
  eventual_reversal_iff_cofinal (j := false) (φ := φ)

theorem strongEventual_true_lie_iff_convergence_true :
    StrongEventual.{u} false true φ ↔
      ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
        ConvergesTo true (M.rTrace x φ) :=
  strongEventual_reversal_iff_convergence (j := true) (φ := φ)

theorem strongEventual_self_refuting_iff_convergence_false :
    StrongEventual.{u} true false φ ↔
      ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
        ConvergesTo false (M.rTrace x φ) :=
  strongEventual_reversal_iff_convergence (j := false) (φ := φ)

theorem uniformBound_implies_eventual (h : UniformBound.{u} i j φ) :
    Eventual.{u} i j φ := by
  obtain ⟨N, _, hbound⟩ := h
  intro World M hM x hx
  obtain ⟨n, hn, _, hvalue⟩ := hbound M hM x hx
  exact ⟨n, hn, hvalue⟩

/-- The unconditional uniform bound in Theorem 13(3). -/
def UnconditionalUniformBound (j : Bool) (φ : BPALCFormula Atom Agent) : Prop :=
  ∃ N : Nat, 1 ≤ N ∧
    ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M → ∀ x,
      ∃ n : Nat, 1 ≤ n ∧ n ≤ N ∧ HoldsBit j (M.rTrace x φ n)

theorem uniformBound_reversal_iff_unconditional :
    UniformBound.{u} (!j) j φ ↔ UnconditionalUniformBound.{u} j φ := by
  classical
  constructor
  · rintro ⟨N, hN, hbound⟩
    refine ⟨N + 1, by omega, fun {World} M hM x => ?_⟩
    by_cases hv : HoldsBit j (M.rTrace x φ 1)
    · exact ⟨1, le_rfl, by omega, hv⟩
    · obtain ⟨n, hn, hnN, hvalue⟩ := hbound (M.rIterateUpdate φ 1)
        (M.rIterateUpdate_isK45 hM φ 1) x ((holdsBit_not_iff j _).mpr hv)
      exact ⟨1 + n, by omega, by omega,
        (holdsBit_congr j (trace_shift M x φ 1 n)).mp hvalue⟩
  · rintro ⟨N, hN, hbound⟩
    exact ⟨N, hN, fun M hM x _ => hbound M hM x⟩

/-- A uniform stage destroys all arrows and makes the formula false everywhere. -/
def UniformExtinction (φ : BPALCFormula Atom Agent) : Prop :=
  ∃ N : Nat, 1 ≤ N ∧
    ∀ {World : Type u} (M : Model World Atom Agent), IsK45 M →
      (∀ x, ¬ M.rTrace x φ N) ∧ Edgeless (M.rIterateUpdate φ N)

theorem edgeless_update_eq {World : Type u} (M : Model World Atom Agent)
    (hM : Edgeless M) (φ : BPALCFormula Atom Agent) : M.rUpdate φ = M := by
  apply Model.ext'
  · intro a x y
    simp only [Model.rUpdate_rel]
    exact ⟨And.left, fun h => False.elim (hM a x y h)⟩
  · intro p x
    rfl

theorem edgeless_iterateUpdate_eq {World : Type u} (M : Model World Atom Agent)
    (hM : Edgeless M) (φ : BPALCFormula Atom Agent) (n : Nat) :
    M.rIterateUpdate φ n = M := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Model.rIterateUpdate_succ, ih, edgeless_update_eq M hM]

/-- An edge surviving `N+1` updates has a target true at stages `0,…,N`,
contradicting the uniform self-refutation bound. -/
theorem uniformBound_self_refuting_implies_extinction
    (h : UniformBound.{u} true false φ) : UniformExtinction.{u} φ := by
  obtain ⟨N, hN, hbound⟩ := h
  have hE : Eventual.{u} true false φ :=
    uniformBound_implies_eventual ⟨N, hN, hbound⟩
  refine ⟨N + 1, by omega, fun {World} M hM => ?_⟩
  have hedge : Edgeless (M.rIterateUpdate φ (N + 1)) := by
    intro a x y hxy
    have hsurv := (M.rIterateUpdate_rel_iff φ (N + 1) a x y).mp hxy |>.2
    have hy : HoldsBit true (M.rSatisfies y φ) := hsurv 0 (by omega)
    obtain ⟨n, _, hnN, hn⟩ := hbound M hM y hy
    exact hn (hsurv n (by omega))
  refine ⟨fun x hx => ?_, hedge⟩
  obtain ⟨n, _, hn⟩ := hE (M.rIterateUpdate φ (N + 1))
    (M.rIterateUpdate_isK45 hM φ (N + 1)) x hx
  have heq := edgeless_iterateUpdate_eq (M.rIterateUpdate φ (N + 1)) hedge φ n
  exact hn (by simpa only [Model.rTrace, heq] using hx)

theorem uniformExtinction_implies_strongEventual
    (h : UniformExtinction.{u} φ) : StrongEventual.{u} true false φ := by
  obtain ⟨N, hN, hbound⟩ := h
  intro World M hM x _
  obtain ⟨hfalse, hedge⟩ := hbound M hM
  refine ⟨N, hN, fun n hn => ?_⟩
  have heq : M.rIterateUpdate φ n = M.rIterateUpdate φ N := by
    rw [← Nat.add_sub_of_le hn, M.rIterateUpdate_add]
    exact edgeless_iterateUpdate_eq _ hedge φ _
  simpa only [HoldsBit, Pattern.HoldsBit, Bool.false_eq_true, ↓reduceIte,
    Model.rTrace, heq] using hfalse x

theorem uniformExtinction_implies_uniformBound
    (h : UniformExtinction.{u} φ) : UniformBound.{u} true false φ := by
  obtain ⟨N, hN, hbound⟩ := h
  refine ⟨N, hN, fun {World} M hM x _ => ?_⟩
  exact ⟨N, hN, le_rfl, (hbound M hM).1 x⟩

theorem uniformBound_self_refuting_iff_extinction :
    UniformBound.{u} true false φ ↔ UniformExtinction.{u} φ :=
  ⟨uniformBound_self_refuting_implies_extinction,
    uniformExtinction_implies_uniformBound⟩

end EventualAndStrongEventualNotionsInPublicAnnouncements.Rich
