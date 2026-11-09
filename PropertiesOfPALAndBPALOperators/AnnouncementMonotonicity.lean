import PropertiesOfPALAndBPALOperators.Preservation
import Mathlib.Data.Set.Finite.Basic

/-! # Monotonicity in announcements and fresh-atom tests -/

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity

universe u v w

variable {World : Type u} {Atom : Type v} {Agent : Type w}

theorem satisfies_of_atom_agreement [DecidableEq Atom]
    {M N : Model World Atom Agent} (φ : Formula Atom Agent)
    (hrel : M.rel = N.rel)
    (hval : ∀ p, p ∈ φ.atoms → ∀ x, M.val p x ↔ N.val p x)
    (x : World) : M.Satisfies x φ ↔ N.Satisfies x φ := by
  induction φ generalizing x with
  | atom p => exact hval p (by simp [Formula.atoms]) x
  | neg φ ih => exact not_congr (ih hval x)
  | conj φ ψ ihφ ihψ =>
    exact and_congr
      (ihφ (fun p hp => hval p (by simp [Formula.atoms, hp])) x)
      (ihψ (fun p hp => hval p (by simp [Formula.atoms, hp])) x)
  | box i φ ih =>
    constructor
    · intro h y hxy
      exact (ih hval y).mp (h y (hrel ▸ hxy))
    · intro h y hxy
      exact (ih hval y).mpr (h y (hrel ▸ hxy))

def revalue [DecidableEq Atom] (M : Model World Atom Agent) (p : Atom)
    (S : Set World) : Model World Atom Agent where
  rel := M.rel
  val q x := if q = p then S x else M.val q x

theorem revalue_satisfies [DecidableEq Atom] (M : Model World Atom Agent)
    (p : Atom) (S : Set World) (φ : Formula Atom Agent) (hp : p ∉ φ.atoms) (x : World) :
    (revalue M p S).Satisfies x φ ↔ M.Satisfies x φ := by
  apply satisfies_of_atom_agreement (M := revalue M p S) (N := M) φ rfl
  intro q hq y
  have hqp : q ≠ p := by intro h; subst q; exact hp hq
  simp [revalue, hqp]

theorem revalue_restrict_satisfies [DecidableEq Atom] (M : Model World Atom Agent)
    (p : Atom) (S T : Set World) (φ : Formula Atom Agent) (hp : p ∉ φ.atoms) (x : T) :
    ((revalue M p S).restrict T).Satisfies x φ ↔ (M.restrict T).Satisfies x φ := by
  apply satisfies_of_atom_agreement (M := (revalue M p S).restrict T)
    (N := M.restrict T) φ rfl
  intro q hq y
  have hqp : q ≠ p := by intro h; subst q; exact hp hq
  simp [Model.restrict, revalue, hqp]

theorem revalue_update_atom [DecidableEq Atom] (M : Model World Atom Agent)
    (p : Atom) (S : Set World) :
    (revalue M p S).update (.atom p) = targetCut (revalue M p S) S := by
  apply Model.ext'
  · intro i x y
    simp [Model.update, Model.Satisfies, revalue, targetCut]
  · intro q x
    rfl

/-- The executable part of the announcement-preservation schema; this is
the PAL schema, and is also a useful intermediate BPAL condition. -/
def AnnouncementPreserved (φ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent) (ψ : Formula Atom Agent) (x : World),
    M.Satisfies x φ → M.Satisfies x ψ → (M.update ψ).Satisfies x φ

/-- The BPAL schema has no executability premise. -/
def BPALAnnouncementPreserved (φ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent) (ψ : Formula Atom Agent) (x : World),
    M.Satisfies x φ → (M.update ψ).Satisfies x φ

theorem announcementPreserved_iff_submodelPreserved [Infinite Atom]
    (φ : Formula Atom Agent) :
    AnnouncementPreserved.{u} φ ↔ SubmodelPreserved.{u} φ := by
  classical
  constructor
  · intro h World M S x hx
    obtain ⟨p,hp⟩ := φ.atoms.exists_notMem
    have hn : (revalue M p S).Satisfies x.val φ :=
      (revalue_satisfies M p S φ hp x.val).mpr hx
    have hstep := h (revalue M p S) (.atom p) x.val hn
      (show (revalue M p S).Satisfies x.val (.atom p) from by
        simp only [Model.satisfies_atom, revalue]
        exact x.property)
    rw [revalue_update_atom] at hstep
    exact (revalue_restrict_satisfies M p S S φ hp x).mp
      ((targetCut_satisfies_restrict (revalue M p S) S x φ).mp hstep)
  · intro h World M ψ x hx _
    exact ((deletionMonotone_iff_submodelPreserved φ).mpr h) M (M.update ψ)
      (update_arrowSubmodel M ψ) x hx

theorem bpalAnnouncementPreserved_iff_submodelPreserved [Infinite Atom]
    (φ : Formula Atom Agent) :
    BPALAnnouncementPreserved.{u} φ ↔ SubmodelPreserved.{u} φ := by
  constructor
  · intro h
    exact (announcementPreserved_iff_submodelPreserved φ).mp
      (fun M ψ x hx _ => h M ψ x hx)
  · intro h World M ψ x hx
    exact ((deletionMonotone_iff_submodelPreserved φ).mpr h) M (M.update ψ)
      (update_arrowSubmodel M ψ) x hx

def Entails (α β : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent) (x : World),
    M.Satisfies x α → M.Satisfies x β

def BPALPositive (φ : Formula Atom Agent) : Prop :=
  ∀ α β, Entails.{u} α β → ∀ {World : Type u} (M : Model World Atom Agent) x,
    (M.update β).Satisfies x φ → (M.update α).Satisfies x φ

def BPALNegative (φ : Formula Atom Agent) : Prop :=
  ∀ α β, Entails.{u} α β → ∀ {World : Type u} (M : Model World Atom Agent) x,
    (M.update α).Satisfies x φ → (M.update β).Satisfies x φ

def PALPositive (φ : Formula Atom Agent) : Prop :=
  ∀ α β, Entails.{u} α β → ∀ {World : Type u} (M : Model World Atom Agent) x,
    (M.Satisfies x β → (M.update β).Satisfies x φ) →
    M.Satisfies x α → (M.update α).Satisfies x φ

def PALNegative (φ : Formula Atom Agent) : Prop :=
  ∀ α β, Entails.{u} α β → ∀ {World : Type u} (M : Model World Atom Agent) x,
    M.Satisfies x α ∧ (M.update α).Satisfies x φ →
    M.Satisfies x β ∧ (M.update β).Satisfies x φ

theorem update_arrowSubmodel_of_entails {α β : Formula Atom Agent}
    (h : Entails.{u} α β) (M : Model World Atom Agent) :
    ArrowSubmodel (M.update α) (M.update β) :=
  ⟨rfl, fun _ _ y he => ⟨he.1,h M y he.2⟩⟩

theorem DeletionMonotone.bpalPositive {φ : Formula Atom Agent}
    (hφ : DeletionMonotone.{u} φ) : BPALPositive.{u} φ := by
  intro α β h World M x hx
  exact hφ _ _ (update_arrowSubmodel_of_entails h M) x hx

theorem DeletionMonotone.palPositive {φ : Formula Atom Agent}
    (hφ : DeletionMonotone.{u} φ) : PALPositive.{u} φ := by
  intro α β h World M x hx hα
  exact hφ _ _ (update_arrowSubmodel_of_entails h M) x (hx (h M x hα))

theorem model_update_verum [Inhabited Atom] (M : Model World Atom Agent) :
    M.update Formula.verum = M := by
  apply Model.ext'
  · intro i x y
    simp only [Model.update_rel, Model.satisfies_verum, and_true]
  · intro p x
    rfl

theorem bpalPositive_iff_deletionMonotone [Infinite Atom] [Inhabited Atom]
    (φ : Formula Atom Agent) : BPALPositive.{u} φ ↔ DeletionMonotone.{u} φ := by
  constructor
  · intro h
    apply (deletionMonotone_iff_submodelPreserved φ).mpr
    apply (bpalAnnouncementPreserved_iff_submodelPreserved φ).mp
    intro World M ψ x hx
    apply h ψ Formula.verum (fun _ _ _ => Model.satisfies_verum _ _) M x
    simpa only [model_update_verum] using hx
  · exact DeletionMonotone.bpalPositive

theorem palPositive_iff_deletionMonotone [Infinite Atom] [Inhabited Atom]
    (φ : Formula Atom Agent) : PALPositive.{u} φ ↔ DeletionMonotone.{u} φ := by
  constructor
  · intro h
    apply (deletionMonotone_iff_submodelPreserved φ).mpr
    apply (announcementPreserved_iff_submodelPreserved φ).mp
    intro World M ψ x hx hψ
    apply h ψ Formula.verum (fun _ _ _ => Model.satisfies_verum _ _) M x ?_ hψ
    intro _
    simpa only [model_update_verum] using hx
  · exact DeletionMonotone.palPositive

theorem bpalPositive_neg_iff_negative (φ : Formula Atom Agent) :
    BPALPositive.{u} (.neg φ) ↔ BPALNegative.{u} φ := by
  classical
  constructor
  · intro h α β hab World M x hx
    by_contra hn
    exact h α β hab M x hn hx
  · intro h α β hab World M x hn hx
    exact hn (h α β hab M x hx)

theorem palPositive_neg_iff_negative (φ : Formula Atom Agent) :
    PALPositive.{u} (.neg φ) ↔ PALNegative.{u} φ := by
  classical
  constructor
  · intro h α β hab World M x hx
    refine ⟨hab M x hx.1, ?_⟩
    by_contra hn
    exact h α β hab M x (fun _ => hn) hx.1 hx.2
  · intro h α β hab World M x hn ha hφ
    have ht := h α β hab M x ⟨ha,hφ⟩
    exact hn ht.1 ht.2

theorem bpalNegative_iff_deletionAntimonotone [Infinite Atom] [Inhabited Atom]
    (φ : Formula Atom Agent) : BPALNegative.{u} φ ↔ DeletionAntimonotone.{u} φ :=
  (bpalPositive_neg_iff_negative φ).symm.trans
    ((bpalPositive_iff_deletionMonotone (.neg φ)).trans (deletionMonotone_neg_iff φ))

theorem palNegative_iff_deletionAntimonotone [Infinite Atom] [Inhabited Atom]
    (φ : Formula Atom Agent) : PALNegative.{u} φ ↔ DeletionAntimonotone.{u} φ :=
  (palPositive_neg_iff_negative φ).symm.trans
    ((palPositive_iff_deletionMonotone (.neg φ)).trans (deletionMonotone_neg_iff φ))

end PropertiesOfPALAndBPALOperators
