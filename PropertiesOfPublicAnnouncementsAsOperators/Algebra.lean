import ClassificationSigmaValidity.Expressivity
import ClassificationSigmaValidity.Locality
import Mathlib.Tactic.Tauto

/-!
# Announcement operators and their algebra

PAL models below a fixed ambient model are represented by their domains. Domain
equality is exactly equality of their induced relations and valuations. BPAL
models with a fixed valuation are represented by their current relations. These
two representations deliberately use different orders: domain inclusion and
arrow inclusion, respectively.
-/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

def palUpdate (M : Model World Atom Agent) (φ : PALFormula Atom Agent)
    (S : Set World) : Set World := fun x => S x ∧ PAL.Satisfies M S x φ

@[simp] theorem mem_palUpdate (M : Model World Atom Agent) (φ : PALFormula Atom Agent)
    (S : Set World) (x : World) :
    x ∈ palUpdate M φ S ↔ S x ∧ PAL.Satisfies M S x φ := Iff.rfl

def bpalUpdate (M : Model World Atom Agent) (φ : BPALFormula Atom Agent)
    (R : Agent → World → World → Prop) : Agent → World → World → Prop :=
  fun i x y => R i x y ∧ BPAL.Satisfies M R y φ

def bpalUpdateModel (M : Model World Atom Agent) (φ : BPALFormula Atom Agent) :
    Model World Atom Agent := ⟨bpalUpdate M φ M.rel, M.val⟩

theorem bpalSatisfies_ambient_congr (M N : Model World Atom Agent)
    (hv : M.val = N.val) (R : Agent → World → World → Prop)
    (x : World) (φ : BPALFormula Atom Agent) :
    BPAL.Satisfies M R x φ ↔ BPAL.Satisfies N R x φ := by
  rw [BPAL.satisfies_toFormula, BPAL.satisfies_toFormula]
  have he : BPAL.relationModel M R = BPAL.relationModel N R := by
    apply Model.ext'
    · intro i y z; rfl
    · intro p y; change M.val p y ↔ N.val p y; rw [hv]
  rw [he]

/-- The fixed-valuation relation representation agrees with actual successive
updates of `Model`, including dynamic postconditions. -/
theorem bpalUpdateModel_sequence (M : Model World Atom Agent)
    (φ ψ : BPALFormula Atom Agent) :
    bpalUpdateModel (bpalUpdateModel M φ) ψ =
      (⟨bpalUpdate M ψ (bpalUpdate M φ M.rel), M.val⟩ : Model World Atom Agent) := by
  apply Model.ext'
  · intro i x y
    change (bpalUpdate M φ M.rel i x y ∧
      BPAL.Satisfies (bpalUpdateModel M φ) (bpalUpdate M φ M.rel) y ψ) ↔
      (bpalUpdate M φ M.rel i x y ∧
        BPAL.Satisfies M (bpalUpdate M φ M.rel) y ψ)
    exact and_congr Iff.rfl
      (bpalSatisfies_ambient_congr (bpalUpdateModel M φ) M rfl _ y ψ)
  · intro p x; rfl

theorem bpalUpdateModel_composition_eq_iff (M : Model World Atom Agent)
    (φ ψ θ : BPALFormula Atom Agent) :
    bpalUpdateModel (bpalUpdateModel M φ) ψ = bpalUpdateModel M θ ↔
      bpalUpdate M ψ (bpalUpdate M φ M.rel) = bpalUpdate M θ M.rel := by
  rw [bpalUpdateModel_sequence]
  constructor
  · exact fun h => congrArg Model.rel h
  · intro h
    apply Model.ext'
    · intro i x y
      exact iff_of_eq (congrFun (congrFun (congrFun h i) x) y)
    · intro p x; rfl

theorem palUpdate_deflationary (M : Model World Atom Agent)
    (φ : PALFormula Atom Agent) (S : Set World) : palUpdate M φ S ⊆ S :=
  fun _ h => h.1

theorem bpalUpdate_deflationary (M : Model World Atom Agent)
    (φ : BPALFormula Atom Agent) (R : Agent → World → World → Prop)
    (i : Agent) (x y : World) : bpalUpdate M φ R i x y → R i x y :=
  fun h => h.1

/-- Lemma 9, PAL: sequential restrictions equal one guarded announcement. -/
theorem palUpdate_sequential (M : Model World Atom Agent)
    (φ ψ : PALFormula Atom Agent) (S : Set World) :
    palUpdate M ψ (palUpdate M φ S) =
      palUpdate M (.conj φ (.announce φ ψ)) S := by
  ext x
  change ((S x ∧ PAL.Satisfies M S x φ) ∧
      PAL.Satisfies M (palUpdate M φ S) x ψ) ↔
    S x ∧ (PAL.Satisfies M S x φ ∧
      (PAL.Satisfies M S x φ → PAL.Satisfies M (palUpdate M φ S) x ψ))
  tauto

/-- Lemma 9, BPAL. -/
theorem bpalUpdate_sequential (M : Model World Atom Agent)
    (φ ψ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) :
    bpalUpdate M ψ (bpalUpdate M φ R) =
      bpalUpdate M (.conj φ (.announce φ ψ)) R := by
  funext i x y
  apply propext
  change ((R i x y ∧ BPAL.Satisfies M R y φ) ∧
      BPAL.Satisfies M (bpalUpdate M φ R) y ψ) ↔
    R i x y ∧ (BPAL.Satisfies M R y φ ∧
      BPAL.Satisfies M (bpalUpdate M φ R) y ψ)
  tauto

/-- Lemma 10, PAL, pointwise in the initial model. -/
theorem palUpdate_eq_iff (M : Model World Atom Agent)
    (φ ψ : PALFormula Atom Agent) (S : Set World) :
    palUpdate M φ S = palUpdate M ψ S ↔
      ∀ x, S x → (PAL.Satisfies M S x φ ↔ PAL.Satisfies M S x ψ) := by
  constructor
  · intro h x hx
    have he := Set.ext_iff.mp h x
    simpa only [mem_palUpdate, palUpdate, Set.mem_setOf_eq, hx, true_and] using he
  · intro h
    ext x
    by_cases hx : S x
    · simp only [mem_palUpdate, hx, true_and]
      exact h x hx
    · simp [mem_palUpdate, hx]

/-- Lemma 10, BPAL: only targets of arrows have to agree. -/
theorem bpalUpdate_eq_iff (M : Model World Atom Agent)
    (φ ψ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) :
    bpalUpdate M φ R = bpalUpdate M ψ R ↔
      ∀ i x y, R i x y →
        (BPAL.Satisfies M R y φ ↔ BPAL.Satisfies M R y ψ) := by
  constructor
  · intro h i x y hxy
    have he := congrFun (congrFun (congrFun h i) x) y
    simpa only [bpalUpdate, hxy, true_and] using (iff_of_eq he)
  · intro h
    funext i x y
    apply propext
    by_cases hxy : R i x y
    · simpa only [bpalUpdate, hxy, true_and] using h i x y hxy
    · simp [bpalUpdate, hxy]

def palSequence (M : Model World Atom Agent) :
    List (PALFormula Atom Agent) → Set World → Set World
  | [], S => S
  | φ :: σ, S => palSequence M σ (palUpdate M φ S)

def bpalSequence (M : Model World Atom Agent) :
    List (BPALFormula Atom Agent) →
      (Agent → World → World → Prop) → Agent → World → World → Prop
  | [], R => R
  | φ :: σ, R => bpalSequence M σ (bpalUpdate M φ R)

def palAnnouncements : List (PALFormula Atom Agent) →
    PALFormula Atom Agent → PALFormula Atom Agent
  | [], χ => χ
  | φ :: σ, χ => .announce φ (palAnnouncements σ χ)

def bpalAnnouncements : List (BPALFormula Atom Agent) →
    BPALFormula Atom Agent → BPALFormula Atom Agent
  | [], χ => χ
  | φ :: σ, χ => .announce φ (bpalAnnouncements σ χ)

theorem palSequence_subset (M : Model World Atom Agent)
    (σ : List (PALFormula Atom Agent)) (S : Set World) :
    palSequence M σ S ⊆ S := by
  induction σ generalizing S with
  | nil => exact fun _ h => h
  | cons φ σ ih =>
      exact Set.Subset.trans (ih _) (palUpdate_deflationary M φ S)

theorem bpalSequence_subset (M : Model World Atom Agent)
    (σ : List (BPALFormula Atom Agent)) (R : Agent → World → World → Prop) :
    ∀ i x y, bpalSequence M σ R i x y → R i x y := by
  induction σ generalizing R with
  | nil => exact fun _ _ _ h => h
  | cons φ σ ih => exact fun i x y h => (ih _ i x y h).1

theorem palAnnouncements_satisfies (M : Model World Atom Agent)
    (σ : List (PALFormula Atom Agent)) (χ : PALFormula Atom Agent)
    (S : Set World) (x : World) (hx : S x) :
    PAL.Satisfies M S x (palAnnouncements σ χ) ↔
      (palSequence M σ S x → PAL.Satisfies M (palSequence M σ S) x χ) := by
  induction σ generalizing S with
  | nil => simp [palAnnouncements, palSequence, hx]
  | cons φ σ ih =>
      change (PAL.Satisfies M S x φ →
        PAL.Satisfies M (palUpdate M φ S) x (palAnnouncements σ χ)) ↔ _
      by_cases hφ : PAL.Satisfies M S x φ
      · rw [ih _ ⟨hx, hφ⟩]
        simp only [hφ, true_implies, palSequence]
      · have hn : ¬ palSequence M σ (palUpdate M φ S) x :=
          fun h => hφ ((palSequence_subset M σ _ h).2)
        simp only [hφ, false_implies, palSequence, hn]

theorem bpalAnnouncements_satisfies (M : Model World Atom Agent)
    (σ : List (BPALFormula Atom Agent)) (χ : BPALFormula Atom Agent)
    (R : Agent → World → World → Prop) (x : World) :
    BPAL.Satisfies M R x (bpalAnnouncements σ χ) ↔
      BPAL.Satisfies M (bpalSequence M σ R) x χ := by
  induction σ generalizing R with
  | nil => rfl
  | cons φ σ ih => exact ih (bpalUpdate M φ R)

/-- Lemma 11 in PAL; falsity alone detects the surviving domain. -/
theorem palSequence_eq_iff [Inhabited Atom] (M : Model World Atom Agent)
    (σ τ : List (PALFormula Atom Agent)) (S : Set World) :
    palSequence M σ S = palSequence M τ S ↔
      ∀ χ x, S x →
        (PAL.Satisfies M S x (palAnnouncements σ χ) ↔
          PAL.Satisfies M S x (palAnnouncements τ χ)) := by
  constructor
  · intro h χ x hx
    rw [palAnnouncements_satisfies M σ χ S x hx,
      palAnnouncements_satisfies M τ χ S x hx, h]
  · intro h
    let bot : PALFormula Atom Agent := .conj (.atom default) (.neg (.atom default))
    ext x
    by_cases hx : S x
    · have he := h bot x hx
      rw [palAnnouncements_satisfies M σ bot S x hx,
        palAnnouncements_satisfies M τ bot S x hx] at he
      simp only [bot, PAL.Satisfies, and_not_self, imp_false] at he
      exact not_iff_not.mp he
    · have hs : ¬ palSequence M σ S x := fun h => hx (palSequence_subset M σ S h)
      have ht : ¬ palSequence M τ S x := fun h => hx (palSequence_subset M τ S h)
      exact iff_of_false hs ht

/-- Theorem 12, PAL, equivalence with the guarded truth sets. -/
theorem pal_commute_iff (M : Model World Atom Agent)
    (φ ψ : PALFormula Atom Agent) (S : Set World) :
    palUpdate M ψ (palUpdate M φ S) = palUpdate M φ (palUpdate M ψ S) ↔
      ∀ x, S x →
        ((PAL.Satisfies M S x φ ∧ PAL.Satisfies M (palUpdate M φ S) x ψ) ↔
          (PAL.Satisfies M S x ψ ∧ PAL.Satisfies M (palUpdate M ψ S) x φ)) := by
  constructor
  · intro h x hx
    have he := Set.ext_iff.mp h x
    simpa only [mem_palUpdate, palUpdate, Set.mem_setOf_eq, hx, true_and] using he
  · intro h
    ext x
    by_cases hx : S x
    · simpa only [mem_palUpdate, palUpdate, Set.mem_setOf_eq, hx, true_and] using h x hx
    · simp [mem_palUpdate, palUpdate, hx]

/-- Theorem 12, BPAL: the guard equivalence is tested at arrow targets. -/
theorem bpal_commute_iff (M : Model World Atom Agent)
    (φ ψ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) :
    bpalUpdate M ψ (bpalUpdate M φ R) = bpalUpdate M φ (bpalUpdate M ψ R) ↔
      ∀ i x y, R i x y →
        ((BPAL.Satisfies M R y φ ∧ BPAL.Satisfies M (bpalUpdate M φ R) y ψ) ↔
          (BPAL.Satisfies M R y ψ ∧ BPAL.Satisfies M (bpalUpdate M ψ R) y φ)) := by
  rw [bpalUpdate_sequential, bpalUpdate_sequential, bpalUpdate_eq_iff]
  rfl

theorem commute_truth_cases (a b c d : Prop) :
    ((a ∧ c) ↔ (b ∧ d)) ↔
      ((a ∧ ¬ b → ¬ c) ∧ (b ∧ ¬ a → ¬ d) ∧ (a ∧ b → (c ↔ d))) := by
  tauto

/-- Theorem 12, PAL, the three initial-truth cases. -/
theorem pal_commute_iff_cases (M : Model World Atom Agent)
    (φ ψ : PALFormula Atom Agent) (S : Set World) :
    palUpdate M ψ (palUpdate M φ S) = palUpdate M φ (palUpdate M ψ S) ↔
      ∀ x, S x →
        ((PAL.Satisfies M S x φ ∧ ¬ PAL.Satisfies M S x ψ →
            ¬ PAL.Satisfies M (palUpdate M φ S) x ψ) ∧
         (PAL.Satisfies M S x ψ ∧ ¬ PAL.Satisfies M S x φ →
            ¬ PAL.Satisfies M (palUpdate M ψ S) x φ) ∧
         (PAL.Satisfies M S x φ ∧ PAL.Satisfies M S x ψ →
            (PAL.Satisfies M (palUpdate M φ S) x ψ ↔
              PAL.Satisfies M (palUpdate M ψ S) x φ))) := by
  simp only [pal_commute_iff, commute_truth_cases]

/-- Theorem 12, BPAL, the same three cases under an outer box. -/
theorem bpal_commute_iff_cases (M : Model World Atom Agent)
    (φ ψ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) :
    bpalUpdate M ψ (bpalUpdate M φ R) = bpalUpdate M φ (bpalUpdate M ψ R) ↔
      ∀ i x y, R i x y →
        ((BPAL.Satisfies M R y φ ∧ ¬ BPAL.Satisfies M R y ψ →
            ¬ BPAL.Satisfies M (bpalUpdate M φ R) y ψ) ∧
         (BPAL.Satisfies M R y ψ ∧ ¬ BPAL.Satisfies M R y φ →
            ¬ BPAL.Satisfies M (bpalUpdate M ψ R) y φ) ∧
         (BPAL.Satisfies M R y φ ∧ BPAL.Satisfies M R y ψ →
            (BPAL.Satisfies M (bpalUpdate M φ R) y ψ ↔
              BPAL.Satisfies M (bpalUpdate M ψ R) y φ))) := by
  simp only [bpal_commute_iff, commute_truth_cases]

def PalStrongCommute (M : Model World Atom Agent)
    (φ ψ : PALFormula Atom Agent) (S : Set World) : Prop :=
  palUpdate M ψ (palUpdate M φ S) = palUpdate M (.conj φ ψ) S ∧
  palUpdate M φ (palUpdate M ψ S) = palUpdate M (.conj φ ψ) S

def BpalStrongCommute (M : Model World Atom Agent)
    (φ ψ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) : Prop :=
  bpalUpdate M ψ (bpalUpdate M φ R) = bpalUpdate M (.conj φ ψ) R ∧
  bpalUpdate M φ (bpalUpdate M ψ R) = bpalUpdate M (.conj φ ψ) R

theorem pal_sequential_eq_conj_iff (M : Model World Atom Agent)
    (φ ψ : PALFormula Atom Agent) (S : Set World) :
    palUpdate M ψ (palUpdate M φ S) = palUpdate M (.conj φ ψ) S ↔
      ∀ x, S x → PAL.Satisfies M S x φ →
        (PAL.Satisfies M S x ψ ↔ PAL.Satisfies M (palUpdate M φ S) x ψ) := by
  rw [palUpdate_sequential, palUpdate_eq_iff]
  apply forall_congr'
  intro x
  apply imp_congr_right
  intro _
  change ((PAL.Satisfies M S x φ ∧ (PAL.Satisfies M S x φ →
      PAL.Satisfies M (palUpdate M φ S) x ψ)) ↔
    (PAL.Satisfies M S x φ ∧ PAL.Satisfies M S x ψ)) ↔ _
  tauto

theorem bpal_sequential_eq_conj_iff (M : Model World Atom Agent)
    (φ ψ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) :
    bpalUpdate M ψ (bpalUpdate M φ R) = bpalUpdate M (.conj φ ψ) R ↔
      ∀ i x y, R i x y → BPAL.Satisfies M R y φ →
        (BPAL.Satisfies M R y ψ ↔ BPAL.Satisfies M (bpalUpdate M φ R) y ψ) := by
  rw [bpalUpdate_sequential, bpalUpdate_eq_iff]
  apply forall_congr'; intro i
  apply forall_congr'; intro x
  apply forall_congr'; intro y
  apply imp_congr_right; intro _
  change ((BPAL.Satisfies M R y φ ∧ BPAL.Satisfies M (bpalUpdate M φ R) y ψ) ↔
    (BPAL.Satisfies M R y φ ∧ BPAL.Satisfies M R y ψ)) ↔ _
  tauto

theorem palUpdate_conj_comm (M : Model World Atom Agent)
    (φ ψ : PALFormula Atom Agent) (S : Set World) :
    palUpdate M (.conj φ ψ) S = palUpdate M (.conj ψ φ) S := by
  ext x; simp only [mem_palUpdate, PAL.Satisfies, and_comm]

theorem bpalUpdate_conj_comm (M : Model World Atom Agent)
    (φ ψ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) :
    bpalUpdate M (.conj φ ψ) R = bpalUpdate M (.conj ψ φ) R := by
  funext i x y; apply propext
  simp only [bpalUpdate, BPAL.Satisfies, and_comm]

/-- Theorem 13, PAL, mutual stability under truthful announcements. -/
theorem pal_strongCommute_iff (M : Model World Atom Agent)
    (φ ψ : PALFormula Atom Agent) (S : Set World) :
    PalStrongCommute M φ ψ S ↔
      (∀ x, S x → PAL.Satisfies M S x φ →
        (PAL.Satisfies M S x ψ ↔ PAL.Satisfies M (palUpdate M φ S) x ψ)) ∧
      (∀ x, S x → PAL.Satisfies M S x ψ →
        (PAL.Satisfies M S x φ ↔ PAL.Satisfies M (palUpdate M ψ S) x φ)) := by
  unfold PalStrongCommute
  rw [pal_sequential_eq_conj_iff, palUpdate_conj_comm M φ ψ S,
    pal_sequential_eq_conj_iff]

/-- Theorem 13, BPAL. -/
theorem bpal_strongCommute_iff (M : Model World Atom Agent)
    (φ ψ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) :
    BpalStrongCommute M φ ψ R ↔
      (∀ i x y, R i x y → BPAL.Satisfies M R y φ →
        (BPAL.Satisfies M R y ψ ↔ BPAL.Satisfies M (bpalUpdate M φ R) y ψ)) ∧
      (∀ i x y, R i x y → BPAL.Satisfies M R y ψ →
        (BPAL.Satisfies M R y φ ↔ BPAL.Satisfies M (bpalUpdate M ψ R) y φ)) := by
  unfold BpalStrongCommute
  rw [bpal_sequential_eq_conj_iff, bpalUpdate_conj_comm M φ ψ R,
    bpal_sequential_eq_conj_iff]

/-- Corollary 14: the additional requirement for strong commutativity. -/
theorem pal_strongCommute_iff_commute_preserve (M : Model World Atom Agent)
    (φ ψ : PALFormula Atom Agent) (S : Set World) :
    PalStrongCommute M φ ψ S ↔
      (palUpdate M ψ (palUpdate M φ S) = palUpdate M φ (palUpdate M ψ S)) ∧
      (∀ x, S x → PAL.Satisfies M S x φ → PAL.Satisfies M S x ψ →
        PAL.Satisfies M (palUpdate M φ S) x ψ ∧
        PAL.Satisfies M (palUpdate M ψ S) x φ) := by
  rw [pal_strongCommute_iff, pal_commute_iff]
  constructor
  · rintro ⟨hφ, hψ⟩
    constructor
    · intro x hx
      have hp := hφ x hx
      have hq := hψ x hx
      tauto
    · intro x hx hp hq
      exact ⟨(hφ x hx hp).mp hq, (hψ x hx hq).mp hp⟩
  · rintro ⟨hc, hp⟩
    constructor
    · intro x hx hφ
      have hc' := hc x hx
      have hp' := hp x hx
      tauto
    · intro x hx hψ
      have hc' := hc x hx
      have hp' := hp x hx
      tauto

theorem bpal_strongCommute_iff_commute_preserve (M : Model World Atom Agent)
    (φ ψ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) :
    BpalStrongCommute M φ ψ R ↔
      (bpalUpdate M ψ (bpalUpdate M φ R) = bpalUpdate M φ (bpalUpdate M ψ R)) ∧
      (∀ i x y, R i x y → BPAL.Satisfies M R y φ → BPAL.Satisfies M R y ψ →
        BPAL.Satisfies M (bpalUpdate M φ R) y ψ ∧
        BPAL.Satisfies M (bpalUpdate M ψ R) y φ) := by
  rw [bpal_strongCommute_iff, bpal_commute_iff]
  constructor
  · rintro ⟨hφ, hψ⟩
    constructor
    · intro i x y hxy
      have hp := hφ i x y hxy
      have hq := hψ i x y hxy
      tauto
    · intro i x y hxy hp hq
      exact ⟨(hφ i x y hxy hp).mp hq, (hψ i x y hxy hq).mp hp⟩
  · rintro ⟨hc, hp⟩
    constructor
    · intro i x y hxy hφ
      have hc' := hc i x y hxy
      have hp' := hp i x y hxy
      tauto
    · intro i x y hxy hψ
      have hc' := hc i x y hxy
      have hp' := hp i x y hxy
      tauto

/-- Theorem 23(1), PAL. -/
theorem pal_fixed_iff (M : Model World Atom Agent)
    (φ : PALFormula Atom Agent) (S : Set World) :
    palUpdate M φ S = S ↔ ∀ x, S x → PAL.Satisfies M S x φ := by
  constructor
  · intro h x hx
    have hmem : palUpdate M φ S x := by rw [h]; exact hx
    exact hmem.2
  · intro h
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, h x hx⟩⟩

/-- Theorem 23(1), BPAL. -/
theorem bpal_fixed_iff (M : Model World Atom Agent)
    (φ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) :
    bpalUpdate M φ R = R ↔ ∀ i x y, R i x y → BPAL.Satisfies M R y φ := by
  constructor
  · intro h i x y hxy
    have hmem : bpalUpdate M φ R i x y := by rw [h]; exact hxy
    exact hmem.2
  · intro h
    funext i x y
    apply propext
    exact ⟨fun hxy => hxy.1, fun hxy => ⟨hxy, h i x y hxy⟩⟩

/-- Proposition 21(2), the exact PAL success condition at a model. -/
theorem pal_idempotent_iff_success (M : Model World Atom Agent)
    (φ : PALFormula Atom Agent) (S : Set World) :
    palUpdate M φ (palUpdate M φ S) = palUpdate M φ S ↔
      ∀ x, S x → PAL.Satisfies M S x φ →
        PAL.Satisfies M (palUpdate M φ S) x φ := by
  rw [pal_fixed_iff]
  simp only [palUpdate, and_imp]

/-- The modelwise BPAL condition has an incoming-arrow guard. Global K
validity removes that guard using a fresh predecessor (see AlgebraGlobal). -/
theorem bpal_idempotent_iff_target_success (M : Model World Atom Agent)
    (φ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) :
    bpalUpdate M φ (bpalUpdate M φ R) = bpalUpdate M φ R ↔
      ∀ i x y, R i x y → BPAL.Satisfies M R y φ →
        BPAL.Satisfies M (bpalUpdate M φ R) y φ := by
  rw [bpal_fixed_iff]
  simp only [bpalUpdate, and_imp]

/-- Proposition 21(3), PAL. -/
theorem pal_square_zero_iff (M : Model World Atom Agent)
    (φ : PALFormula Atom Agent) (S : Set World) :
    palUpdate M φ (palUpdate M φ S) = ∅ ↔
      ∀ x, S x → PAL.Satisfies M S x φ →
        ¬ PAL.Satisfies M (palUpdate M φ S) x φ := by
  rw [Set.eq_empty_iff_forall_notMem]
  simp only [mem_palUpdate, palUpdate, not_and, and_imp]

theorem bpal_square_zero_iff (M : Model World Atom Agent)
    (φ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) :
    bpalUpdate M φ (bpalUpdate M φ R) = (fun _ _ _ => False) ↔
      ∀ i x y, R i x y → BPAL.Satisfies M R y φ →
        ¬ BPAL.Satisfies M (bpalUpdate M φ R) y φ := by
  constructor
  · intro h i x y hxy hφ hφ'
    have he := congrFun (congrFun (congrFun h i) x) y
    exact (iff_of_eq he).mp ⟨⟨hxy, hφ⟩, hφ'⟩
  · intro h
    funext i x y
    apply propext
    exact ⟨fun ht => h i x y ht.1.1 ht.1.2 ht.2, False.elim⟩

/-- Theorem 23(2), complement. -/
theorem pal_fixed_neg_iff_zero (M : Model World Atom Agent)
    (φ : PALFormula Atom Agent) (S : Set World) :
    palUpdate M (.neg φ) S = S ↔ palUpdate M φ S = ∅ := by
  rw [pal_fixed_iff, Set.eq_empty_iff_forall_notMem]
  simp only [mem_palUpdate, PAL.Satisfies, not_and]

theorem bpal_fixed_neg_iff_zero (M : Model World Atom Agent)
    (φ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) :
    bpalUpdate M (.neg φ) R = R ↔ bpalUpdate M φ R = (fun _ _ _ => False) := by
  rw [bpal_fixed_iff]
  constructor
  · intro h
    funext i x y
    apply propext
    exact ⟨fun ht => h i x y ht.1 ht.2, False.elim⟩
  · intro h i x y hxy hφ
    have he := congrFun (congrFun (congrFun h i) x) y
    exact (iff_of_eq he).mp ⟨hxy, hφ⟩

/-- Theorem 23(2), composition. This requires no commutativity. -/
theorem pal_fixed_composition_iff (M : Model World Atom Agent)
    (φ ψ : PALFormula Atom Agent) (S : Set World) :
    palUpdate M ψ (palUpdate M φ S) = S ↔
      palUpdate M φ S = S ∧ palUpdate M ψ S = S := by
  constructor
  · intro h
    have hp : palUpdate M φ S = S := Set.Subset.antisymm
      (palUpdate_deflationary M φ S) (by
        intro x hx
        have ht : palUpdate M ψ (palUpdate M φ S) x := by rw [h]; exact hx
        exact ht.1)
    exact ⟨hp, by simpa only [hp] using h⟩
  · rintro ⟨hp, hq⟩
    rw [hp, hq]

theorem bpal_fixed_composition_iff (M : Model World Atom Agent)
    (φ ψ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) :
    bpalUpdate M ψ (bpalUpdate M φ R) = R ↔
      bpalUpdate M φ R = R ∧ bpalUpdate M ψ R = R := by
  constructor
  · intro h
    have hp : bpalUpdate M φ R = R := by
      funext i x y
      apply propext
      constructor
      · exact fun ht => ht.1
      · intro hxy
        have ht : bpalUpdate M ψ (bpalUpdate M φ R) i x y := by rw [h]; exact hxy
        exact ht.1
    exact ⟨hp, by simpa only [hp] using h⟩
  · rintro ⟨hp, hq⟩
    rw [hp, hq]

theorem pal_fixed_conj_iff (M : Model World Atom Agent)
    (φ ψ : PALFormula Atom Agent) (S : Set World) :
    palUpdate M (.conj φ ψ) S = S ↔
      palUpdate M φ S = S ∧ palUpdate M ψ S = S := by
  simp only [pal_fixed_iff, PAL.Satisfies, forall_and]

theorem bpal_fixed_conj_iff (M : Model World Atom Agent)
    (φ ψ : BPALFormula Atom Agent) (R : Agent → World → World → Prop) :
    bpalUpdate M (.conj φ ψ) R = R ↔
      bpalUpdate M φ R = R ∧ bpalUpdate M ψ R = R := by
  simp only [bpal_fixed_iff, BPAL.Satisfies, forall_and]

theorem pal_fixed_or_of_fixed (M : Model World Atom Agent)
    (φ ψ : PALFormula Atom Agent) (S : Set World)
    (h : palUpdate M φ S = S ∨ palUpdate M ψ S = S) :
    palUpdate M (.neg (.conj (.neg φ) (.neg ψ))) S = S := by
  rw [pal_fixed_iff]
  intro x hx
  change ¬ (¬ PAL.Satisfies M S x φ ∧ ¬ PAL.Satisfies M S x ψ)
  rcases h with h | h
  · exact fun hn => hn.1 ((pal_fixed_iff M φ S).mp h x hx)
  · exact fun hn => hn.2 ((pal_fixed_iff M ψ S).mp h x hx)

theorem bpal_fixed_or_of_fixed (M : Model World Atom Agent)
    (φ ψ : BPALFormula Atom Agent) (R : Agent → World → World → Prop)
    (h : bpalUpdate M φ R = R ∨ bpalUpdate M ψ R = R) :
    bpalUpdate M (.neg (.conj (.neg φ) (.neg ψ))) R = R := by
  rw [bpal_fixed_iff]
  intro i x y hxy
  change ¬ (¬ BPAL.Satisfies M R y φ ∧ ¬ BPAL.Satisfies M R y ψ)
  rcases h with h | h
  · exact fun hn => hn.1 ((bpal_fixed_iff M φ R).mp h i x y hxy)
  · exact fun hn => hn.2 ((bpal_fixed_iff M ψ R).mp h i x y hxy)

/-- The outer boxes in the BPAL criteria can be removed on reflexive frames. -/
theorem all_targets_iff_of_reflexive [Nonempty Agent]
    (R : Agent → World → World → Prop) (hR : ∀ i x, R i x x) (P : World → Prop) :
    (∀ i x y, R i x y → P y) ↔ ∀ y, P y := by
  constructor
  · intro h y
    obtain ⟨i⟩ := ‹Nonempty Agent›
    exact h i y y (hR i y)
  · exact fun h _ _ y _ => h y

/-- The zero announcement, with an explicit atom avoiding a global choice. -/
def palBottom (p : Atom) : PALFormula Atom Agent := .conj (.atom p) (.neg (.atom p))

def bpalBottom (p : Atom) : BPALFormula Atom Agent := .conj (.atom p) (.neg (.atom p))

theorem palUpdate_bottom (M : Model World Atom Agent) (p : Atom) (S : Set World) :
    palUpdate M (palBottom p) S = ∅ := by
  ext x
  simp [mem_palUpdate, palBottom, PAL.Satisfies]

theorem bpalUpdate_bottom (M : Model World Atom Agent) (p : Atom)
    (R : Agent → World → World → Prop) :
    bpalUpdate M (bpalBottom p) R = (fun _ _ _ => False) := by
  funext i x y
  apply propext
  simp [bpalUpdate, bpalBottom, BPAL.Satisfies]

theorem palUpdate_top (M : Model World Atom Agent) (p : Atom) (S : Set World) :
    palUpdate M (.neg (palBottom p)) S = S := by
  ext x
  change (S x ∧ ¬ (M.val p x ∧ ¬ M.val p x)) ↔ S x
  tauto

theorem bpalUpdate_top (M : Model World Atom Agent) (p : Atom)
    (R : Agent → World → World → Prop) :
    bpalUpdate M (.neg (bpalBottom p)) R = R := by
  funext i x y
  apply propext
  simp [bpalUpdate, bpalBottom, BPAL.Satisfies]

theorem palUpdate_empty (M : Model World Atom Agent) (φ : PALFormula Atom Agent) :
    palUpdate M φ ∅ = ∅ := by
  ext x
  change (False ∧ _) ↔ False
  tauto

theorem bpalUpdate_edgeless (M : Model World Atom Agent) (φ : BPALFormula Atom Agent) :
    bpalUpdate M φ (fun _ _ _ => False) = (fun _ _ _ => False) := by
  funext i x y
  apply propext
  simp [bpalUpdate]

/-- No announcement can reverse a nontrivial preceding announcement. -/
theorem pal_no_nontrivial_inverse (M : Model World Atom Agent)
    (φ ψ : PALFormula Atom Agent) (S : Set World)
    (h : palUpdate M ψ (palUpdate M φ S) = S) : palUpdate M φ S = S :=
  ((pal_fixed_composition_iff M φ ψ S).mp h).1

theorem bpal_no_nontrivial_inverse (M : Model World Atom Agent)
    (φ ψ : BPALFormula Atom Agent) (R : Agent → World → World → Prop)
    (h : bpalUpdate M ψ (bpalUpdate M φ R) = R) : bpalUpdate M φ R = R :=
  ((bpal_fixed_composition_iff M φ ψ R).mp h).1

end PropertiesOfPublicAnnouncementsAsOperators
