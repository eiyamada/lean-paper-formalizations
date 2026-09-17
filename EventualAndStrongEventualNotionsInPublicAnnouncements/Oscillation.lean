import EventualAndStrongEventualNotionsInPublicAnnouncements.Definitions
import ClassificationSigmaValidity.Reduction

/-!
# The alternating true-lie witness

The formula in Lemma 8 is written with `ZPlus` as the standard reduction of
`[↑A]Z`. This has exactly the semantics of the manuscript's displayed `Z⁺`.
-/

namespace EventualAndStrongEventualNotionsInPublicAnnouncements
namespace Oscillation

open ClassificationSigmaValidity

universe u v w
variable {Atom : Type v} {Agent : Type w}

variable (r s p : Atom) (a b : Agent)

def D : Formula Atom Agent :=
  .or (.conj (.atom s) (.dia a (.conj (.neg (.atom r)) (.neg (.atom s)))))
    (.conj (.neg (.atom s)) (.dia b (.conj (.neg (.atom r)) (.atom s))))

def A : Formula Atom Agent :=
  .conj (.neg (.atom r)) (.box b (.or (.atom r) (D r s a b)))

def Z : Formula Atom Agent :=
  .dia a (.conj (.neg (.atom r)) (.conj (.neg (.atom s))
    (.conj (.atom p) (.neg (A r s a b)))))

def ZPlus : Formula Atom Agent :=
  Formula.announcementReduce (A r s a b) (Z r s p a b)

/-- The manuscript's `θ₁₁ᴱ`, also an eventual true lie. -/
def theta : Formula Atom Agent :=
  .or (A r s a b) (.conj (.atom r)
    (.or (Z r s p a b) (.neg (ZPlus r s p a b))))

variable {r s p a b} {World : Type u}

@[simp] theorem theta_at_nonr (M : Model World Atom Agent) (x : World)
    (hx : ¬ M.val r x) :
    M.Satisfies x (theta r s p a b) ↔ M.Satisfies x (A r s a b) := by
  simp [theta, hx]

/-- The guard on each diamond makes `D` insensitive to retained `r`-targets. -/
theorem update_D (M : Model World Atom Agent) (x : World) :
    (M.update (theta r s p a b)).Satisfies x (D r s a b) ↔
      (M.update (A r s a b)).Satisfies x (D r s a b) := by
  have h := theta_at_nonr (r := r) (s := s) (p := p) (a := a) (b := b) M
  simp only [D, Model.satisfies_or, Model.satisfies_and, Model.satisfies_dia,
    Model.satisfies_neg, Model.satisfies_atom, Model.update_val, Model.update_rel]
  constructor
  · rintro (⟨hs, y, ⟨hxy, hy⟩, hyr, hys⟩ | ⟨hs, y, ⟨hxy, hy⟩, hyr, hys⟩)
    · exact Or.inl ⟨hs, y, ⟨hxy, (h y hyr).mp hy⟩, hyr, hys⟩
    · exact Or.inr ⟨hs, y, ⟨hxy, (h y hyr).mp hy⟩, hyr, hys⟩
  · rintro (⟨hs, y, ⟨hxy, hy⟩, hyr, hys⟩ | ⟨hs, y, ⟨hxy, hy⟩, hyr, hys⟩)
    · exact Or.inl ⟨hs, y, ⟨hxy, (h y hyr).mpr hy⟩, hyr, hys⟩
    · exact Or.inr ⟨hs, y, ⟨hxy, (h y hyr).mpr hy⟩, hyr, hys⟩

theorem update_A (M : Model World Atom Agent) (x : World) :
    (M.update (theta r s p a b)).Satisfies x (A r s a b) ↔
      (M.update (A r s a b)).Satisfies x (A r s a b) := by
  classical
  change (¬ M.val r x ∧ ∀ y, (M.rel b x y ∧ M.Satisfies y (theta r s p a b)) →
      (M.update (theta r s p a b)).Satisfies y (.or (.atom r) (D r s a b))) ↔
    (¬ M.val r x ∧ ∀ y, (M.rel b x y ∧ M.Satisfies y (A r s a b)) →
      (M.update (A r s a b)).Satisfies y (.or (.atom r) (D r s a b)))
  simp only [Model.satisfies_or, Model.satisfies_atom, Model.update_val]
  apply and_congr_right
  intro _
  constructor
  · intro h y hy
    by_cases hyr : M.val r y
    · exact Or.inl hyr
    · have hyθ := (theta_at_nonr (p := p) M y hyr).mpr hy.2
      rcases h y ⟨hy.1, hyθ⟩ with hr | hD
      · exact Or.inl hr
      · exact Or.inr ((update_D M y).mp hD)
  · intro h y hy
    by_cases hyr : M.val r y
    · exact Or.inl hyr
    · have hyA := (theta_at_nonr M y hyr).mp hy.2
      rcases h y ⟨hy.1, hyA⟩ with hr | hD
      · exact Or.inl hr
      · exact Or.inr ((update_D M y).mpr hD)

/-- The formula `ZPlus` predicts the value of `Z` after the next announcement. -/
theorem update_Z (M : Model World Atom Agent) (x : World) :
    (M.update (theta r s p a b)).Satisfies x (Z r s p a b) ↔
      M.Satisfies x (ZPlus r s p a b) := by
  rw [ZPlus, ← Model.satisfies_announcementReduce]
  simp only [Z, Model.satisfies_dia, Model.satisfies_and, Model.satisfies_neg,
    Model.satisfies_atom, Model.update_val, Model.update_rel]
  constructor
  · rintro ⟨y, ⟨hxy, hy⟩, hyr, hys, hyp, hyA⟩
    exact ⟨y, ⟨hxy, (theta_at_nonr M y hyr).mp hy⟩, hyr, hys, hyp,
      fun hA => hyA ((update_A M y).mpr hA)⟩
  · rintro ⟨y, ⟨hxy, hy⟩, hyr, hys, hyp, hyA⟩
    exact ⟨y, ⟨hxy, (theta_at_nonr M y hyr).mpr hy⟩, hyr, hys, hyp,
      fun hA => hyA ((update_A M y).mp hA)⟩

/-- The oscillator is already a one-step true lie on every K45 model. -/
theorem theta_trueLie (M : Model World Atom Agent) (hM : IsK45 M) (x : World)
    (hx : ¬ M.Satisfies x (theta r s p a b)) :
    (M.update (theta r s p a b)).Satisfies x (theta r s p a b) := by
  classical
  by_cases hr : M.val r x
  · have hZplus : M.Satisfies x (ZPlus r s p a b) := by
      by_contra hn
      apply hx
      exact (Model.satisfies_or _ _ _ _).mpr (Or.inr ⟨hr, (Model.satisfies_or _ _ _ _).mpr (Or.inr hn)⟩)
    apply (Model.satisfies_or _ _ _ _).mpr
    exact Or.inr ⟨hr, (Model.satisfies_or _ _ _ _).mpr (Or.inl ((update_Z M x).mpr hZplus))⟩
  · apply (theta_at_nonr (M.update (theta r s p a b)) x hr).mpr
    have hAx : ¬ M.Satisfies x (A r s a b) :=
      fun h => hx ((theta_at_nonr M x hr).mpr h)
    refine ⟨hr, ?_⟩
    intro y hy
    apply (Model.satisfies_or _ _ _ _).mpr
    by_cases hyr : M.val r y
    · exact Or.inl hyr
    · have hyA := (theta_at_nonr M y hyr).mp hy.2
      exfalso
      apply hAx
      refine ⟨hr, ?_⟩
      intro z hz
      exact hyA.2 z ((hM b).2 hy.1 hz)

/-- The two positive eventual notions hold globally for the witness. -/
theorem theta_eventual :
    Eventual.{u} true true (theta r s p a b) ∧
      Eventual.{u} false true (theta r s p a b) := by
  classical
  constructor
  · intro World M hM x _
    by_cases h : (M.update (theta r s p a b)).Satisfies x (theta r s p a b)
    · exact ⟨1, le_rfl, h⟩
    · exact ⟨2, by omega, theta_trueLie (M.update _) (Model.update_isK45 hM _) x h⟩
  · intro World M hM x hx
    exact ⟨1, le_rfl, theta_trueLie M hM x hx⟩

/-! The two-peeling model, indexed by distance from the terminal pair. -/

inductive PeelingWorld
  | root
  | node (branch : Nat) (distance : Fin (branch + 1)) (odd : Bool)
  deriving DecidableEq

namespace PeelingWorld

def head (m : Nat) : PeelingWorld := .node m ⟨m, Nat.lt_succ_self m⟩ false

def IsHead (x : PeelingWorld) : Prop := ∃ m, x = head m

def distance : PeelingWorld → Nat
  | .root => 0
  | .node _ d _ => d.val

def RA : PeelingWorld → PeelingWorld → Prop
  | .root, y => IsHead y
  | .node m d false, y => if d.val = m then IsHead y else y = .node m d false
  | .node m d true, y => ∃ e : Fin (m + 1), e.val + 1 = d.val ∧ y = .node m e false

def RB : PeelingWorld → PeelingWorld → Prop
  | .root, _ => False
  | .node m d _, y => y = .node m d true

@[simp] theorem ra_head (m : Nat) (y : PeelingWorld) : RA (head m) y ↔ IsHead y := by
  simp [head, RA]

@[simp] theorem rb_head (m : Nat) (y : PeelingWorld) :
    RB (head m) y ↔ y = .node m ⟨m, Nat.lt_succ_self m⟩ true := Iff.rfl

/-- Every existing arrow leads to a state with the same successor set. -/
theorem ra_successor_eq {x y : PeelingWorld} (h : RA x y) :
    ∀ z, RA x z ↔ RA y z := by
  intro z
  cases x with
  | root =>
    obtain ⟨m, rfl⟩ := h
    exact (ra_head m z).symm
  | node m d side =>
    cases side with
    | false =>
      by_cases hd : d.val = m
      · obtain ⟨k, rfl⟩ := (if_pos hd).mp h
        simp [RA, hd, head]
      · have hy : y = .node m d false := (if_neg hd).mp h
        subst y
        rfl
    | true =>
      obtain ⟨e, he, rfl⟩ := h
      have hem : e.val ≠ m := by omega
      simp only [RA, if_neg hem]
      constructor
      · rintro ⟨f, hf, rfl⟩
        have hfe : f = e := Fin.ext (by omega)
        subst f
        rfl
      · intro hz
        exact ⟨e, he, hz⟩

theorem rb_successor_eq {x y : PeelingWorld} (h : RB x y) :
    ∀ z, RB x z ↔ RB y z := by
  cases x with
  | root => exact False.elim h
  | node m d side =>
    change y = .node m d true at h
    subst y
    exact fun _ => Iff.rfl

theorem ra_k45 : Frame.Transitive RA ∧ Frame.Euclidean RA := by
  constructor
  · intro x y z hxy hyz
    exact (ra_successor_eq hxy z).mpr hyz
  · intro x y z hxy hxz
    exact (ra_successor_eq hxy z).mp hxz

theorem rb_k45 : Frame.Transitive RB ∧ Frame.Euclidean RB := by
  constructor
  · intro x y z hxy hyz
    exact (rb_successor_eq hxy z).mpr hyz
  · intro x y z hxy hxz
    exact (rb_successor_eq hxy z).mp hxz

/-- Atoms `0,1,2,3,4` stand for `r,s,p,t,u`, respectively. -/
def valuation (q : Fin 5) (x : PeelingWorld) : Prop :=
  match q.val with
  | 0 => x = .root
  | 1 => ∃ m d, x = .node m d true
  | 2 => ∃ m, m % 2 = 0 ∧ x = head m
  | 3 => IsHead x
  | 4 => x = head 0
  | _ => False

end PeelingWorld

open PeelingWorld

/-- The explicit model after `n` simultaneous pair deletions. -/
def twoPeeling (a b : Agent) (n : Nat) : Model PeelingWorld (Fin 5) Agent where
  rel i x y := ((i = a ∧ RA x y) ∨ (i = b ∧ RB x y)) ∧ n ≤ distance y
  val := valuation

@[simp] theorem twoPeeling_rel_a (a b : Agent) (hab : a ≠ b) (n : Nat)
    (x y : PeelingWorld) :
    (twoPeeling a b n).rel a x y ↔ RA x y ∧ n ≤ distance y := by
  simp [twoPeeling, hab]

@[simp] theorem twoPeeling_rel_b (a b : Agent) (hab : a ≠ b) (n : Nat)
    (x y : PeelingWorld) :
    (twoPeeling a b n).rel b x y ↔ RB x y ∧ n ≤ distance y := by
  simp [twoPeeling, Ne.symm hab]

theorem twoPeeling_isK45 (a b : Agent) (hab : a ≠ b) (n : Nat) :
    IsK45 (twoPeeling a b n) := by
  intro i
  by_cases hia : i = a
  · subst i
    constructor
    · intro x y z hxy hyz
      rw [twoPeeling_rel_a a b hab] at hxy hyz ⊢
      exact ⟨ra_k45.1 hxy.1 hyz.1, hyz.2⟩
    · intro x y z hxy hxz
      rw [twoPeeling_rel_a a b hab] at hxy hxz ⊢
      exact ⟨ra_k45.2 hxy.1 hxz.1, hxz.2⟩
  · by_cases hib : i = b
    · subst i
      constructor
      · intro x y z hxy hyz
        rw [twoPeeling_rel_b a b hab] at hxy hyz ⊢
        exact ⟨rb_k45.1 hxy.1 hyz.1, hyz.2⟩
      · intro x y z hxy hxz
        rw [twoPeeling_rel_b a b hab] at hxy hxz ⊢
        exact ⟨rb_k45.2 hxy.1 hxz.1, hxz.2⟩
    · simp [Frame.Transitive, Frame.Euclidean, twoPeeling, hia, hib]

@[simp] theorem twoPeeling_nonr (a b : Agent) (n m : Nat) (d : Fin (m + 1))
    (side : Bool) : ¬ (twoPeeling a b n).val 0 (.node m d side) := by
  simp [twoPeeling, valuation]

@[simp] theorem twoPeeling_s (a b : Agent) (n m : Nat) (d : Fin (m + 1))
    (side : Bool) : (twoPeeling a b n).val 1 (.node m d side) ↔ side = true := by
  simp [twoPeeling, valuation]

/-- At an odd node, the selected next arrow survives exactly below its distance. -/
theorem twoPeeling_D_odd (a b : Agent) (hab : a ≠ b) (n m : Nat)
    (d : Fin (m + 1)) :
    (twoPeeling a b n).Satisfies (.node m d true) (D 0 1 a b) ↔ n < d.val := by
  simp only [D, Model.satisfies_or, Model.satisfies_and, Model.satisfies_atom,
    Model.satisfies_neg, Model.satisfies_dia, twoPeeling_s,
    not_true_eq_false, false_and, or_false, true_and]
  constructor
  · rintro ⟨y, hy, _, hys⟩
    obtain ⟨⟨e, he, rfl⟩, hn⟩ := (twoPeeling_rel_a a b hab n _ _).mp hy
    change n ≤ e.val at hn
    omega
  · intro hn
    let e : Fin (m + 1) := ⟨d.val - 1, by omega⟩
    have he : e.val + 1 = d.val := by dsimp [e]; omega
    refine ⟨.node m e false, ?_, twoPeeling_nonr a b n m e false, ?_⟩
    · apply (twoPeeling_rel_a a b hab n _ _).mpr
      exact ⟨⟨e, he, rfl⟩, by change n ≤ e.val; dsimp [e]; omega⟩
    · simp

/-- Exactly the pair at distance `n` falsifies `A` at stage `n`. -/
theorem twoPeeling_A (a b : Agent) (hab : a ≠ b) (n m : Nat)
    (d : Fin (m + 1)) (side : Bool) :
    (twoPeeling a b n).Satisfies (.node m d side) (A 0 1 a b) ↔ n ≠ d.val := by
  simp only [A, Model.satisfies_and, Model.satisfies_neg, Model.satisfies_atom,
    twoPeeling_nonr, not_false_eq_true, true_and, Model.satisfies_box, Model.satisfies_or]
  simp only [twoPeeling_rel_b a b hab, RB, distance]
  constructor
  · intro h hnd
    have htarget := h (.node m d true) ⟨rfl, by simp [hnd]⟩
    rcases htarget with hr | hD
    · exact twoPeeling_nonr a b n m d true hr
    · have hlt := (twoPeeling_D_odd a b hab n m d).mp hD
      omega
  · intro hnd y hy
    rcases hy with ⟨rfl, hn⟩
    exact Or.inr ((twoPeeling_D_odd a b hab n m d).mpr (by change n ≤ d.val at hn; omega))

/-- The model at stage `n+1` is its believed announcement update at stage `n`. -/
theorem twoPeeling_update (a b : Agent) (hab : a ≠ b) (n : Nat) :
    (twoPeeling a b n).update (theta 0 1 2 a b) = twoPeeling a b (n + 1) := by
  apply Model.ext
  · funext i x y
    apply propext
    cases y with
    | root =>
      cases x with
      | root => simp [Model.update_rel, twoPeeling, RA, RB, IsHead, head]
      | node m d side =>
        cases side <;> simp [Model.update_rel, twoPeeling, RA, RB, IsHead, head]
    | node m d side =>
      rw [Model.update_rel, theta_at_nonr _ _ (twoPeeling_nonr a b n m d side),
        twoPeeling_A a b hab]
      change (_ ∧ n ≤ d.val) ∧ n ≠ d.val ↔ _ ∧ n + 1 ≤ d.val
      constructor
      · rintro ⟨⟨hr, hn⟩, hne⟩
        exact ⟨hr, by omega⟩
      · rintro ⟨hr, hn⟩
        exact ⟨⟨hr, by omega⟩, by omega⟩
  · rfl

/-- Identification of the explicit stages with the actual announcement iteration. -/
theorem twoPeeling_iterate (a b : Agent) (hab : a ≠ b) (n : Nat) :
    (twoPeeling a b 0).iterateUpdate (theta 0 1 2 a b) n = twoPeeling a b n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Model.iterateUpdate_succ, ih, twoPeeling_update a b hab]

/-- At the root, `Z` detects the unique currently deleted head. -/
theorem twoPeeling_Z (a b : Agent) (hab : a ≠ b) (n : Nat) :
    (twoPeeling a b n).Satisfies .root (Z 0 1 2 a b) ↔ n % 2 = 0 := by
  simp only [Z, Model.satisfies_dia, Model.satisfies_and, Model.satisfies_neg,
    Model.satisfies_atom]
  constructor
  · rintro ⟨y, hy, _, _, hp, hA⟩
    obtain ⟨⟨m, rfl⟩, hn⟩ := (twoPeeling_rel_a a b hab n _ _).mp hy
    have hnm : n = m := by
      by_contra hne
      exact hA ((twoPeeling_A a b hab n m ⟨m, Nat.lt_succ_self m⟩ false).mpr hne)
    obtain ⟨k, hk, heq⟩ := hp
    have hmk : m = k := congrArg (fun x => match x with
      | PeelingWorld.root => 0
      | .node m _ _ => m) heq
    simpa [hnm, hmk] using hk
  · intro hn
    refine ⟨head n, ?_, ?_, ?_, ?_, ?_⟩
    · apply (twoPeeling_rel_a a b hab n _ _).mpr
      exact ⟨⟨n, rfl⟩, le_rfl⟩
    · exact twoPeeling_nonr a b n n ⟨n, Nat.lt_succ_self n⟩ false
    · simp [head]
    · exact ⟨n, hn, rfl⟩
    · intro hA
      exact (twoPeeling_A a b hab n n ⟨n, Nat.lt_succ_self n⟩ false).mp hA rfl

/-- The announcement truth sequence at the root is `1,0,1,0,…`. -/
theorem twoPeeling_trace (a b : Agent) (hab : a ≠ b) (n : Nat) :
    (twoPeeling a b 0).trace .root (theta 0 1 2 a b) n ↔ n % 2 = 0 := by
  unfold Model.trace
  rw [twoPeeling_iterate a b hab]
  have hZplus : (twoPeeling a b n).Satisfies .root (ZPlus 0 1 2 a b) ↔
      (n + 1) % 2 = 0 := by
    rw [← update_Z, twoPeeling_update a b hab, twoPeeling_Z a b hab]
  simp only [theta, Model.satisfies_or, Model.satisfies_and, Model.satisfies_atom,
    Model.satisfies_neg]
  have hr : (twoPeeling a b n).val 0 .root := rfl
  have hA : ¬ (twoPeeling a b n).Satisfies .root (A 0 1 a b) := fun h => h.1 hr
  rw [iff_false_intro hA, iff_true_intro hr, false_or, true_and,
    twoPeeling_Z a b hab, hZplus]
  omega

/-- Neither initial truth value makes the alternating trace converge to truth. -/
theorem theta_not_strongEventual (a b : Agent) (hab : a ≠ b) :
    ¬ StrongEventual.{0} true true (theta (0 : Fin 5) 1 2 a b) ∧
      ¬ StrongEventual.{0} false true (theta (0 : Fin 5) 1 2 a b) := by
  constructor
  · intro h
    obtain ⟨N, _, hN⟩ := h (twoPeeling a b 0) (twoPeeling_isK45 a b hab 0) .root
      ((twoPeeling_trace a b hab 0).mpr rfl)
    have hn := (twoPeeling_trace a b hab (2 * N + 1)).mp (hN (2 * N + 1) (by omega))
    omega
  · intro h
    let φ := theta (0 : Fin 5) 1 2 a b
    let M := (twoPeeling a b 0).iterateUpdate φ 1
    have hM : IsK45 M := Model.iterateUpdate_isK45 (twoPeeling_isK45 a b hab 0) φ 1
    have hfalse : ¬ M.Satisfies .root φ := by
      intro htrue
      have hbad := (twoPeeling_trace a b hab 1).mp htrue
      omega
    obtain ⟨N, _, hN⟩ := h M hM .root hfalse
    have hlate : M.trace .root φ (2 * N) := hN (2 * N) (by omega)
    have hshift : (twoPeeling a b 0).trace .root φ (1 + 2 * N) := by
      simpa only [M, Model.trace, Model.iterateUpdate_add] using hlate
    have hbad := (twoPeeling_trace a b hab (1 + 2 * N)).mp hshift
    omega

/-- Lemma 8: both finite eventual-to-strong implications are strict. -/
theorem lemma8 (a b : Agent) (hab : a ≠ b) :
    ∃ φ : Formula (Fin 5) Agent,
      (Eventual.{0} true true φ ∧ ¬ StrongEventual.{0} true true φ) ∧
      (Eventual.{0} false true φ ∧ ¬ StrongEventual.{0} false true φ) := by
  refine ⟨theta 0 1 2 a b, ?_⟩
  exact ⟨⟨theta_eventual.1, (theta_not_strongEventual a b hab).1⟩,
    ⟨theta_eventual.2, (theta_not_strongEventual a b hab).2⟩⟩

end Oscillation
end EventualAndStrongEventualNotionsInPublicAnnouncements
