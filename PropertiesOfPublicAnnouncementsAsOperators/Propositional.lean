import PropertiesOfPublicAnnouncementsAsOperators.Preservation

/-! # The common part of universal and existential formulas -/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity

universe u v w

variable {World : Type u} {Atom : Type v} {Agent : Type w}

inductive Propositional : Formula Atom Agent → Prop
  | atom (p) : Propositional (.atom p)
  | neg {φ} : Propositional φ → Propositional (.neg φ)
  | conj {φ ψ} : Propositional φ → Propositional ψ → Propositional (.conj φ ψ)

theorem Propositional.valuation_invariant {φ : Formula Atom Agent}
    (hφ : Propositional φ) {M N : Model World Atom Agent} (hval : M.val = N.val)
    (x : World) : M.Satisfies x φ ↔ N.Satisfies x φ := by
  induction hφ with
  | atom p => change M.val p x ↔ N.val p x; rw [hval]
  | neg hφ ih => exact not_congr ih
  | conj hφ hψ ihφ ihψ => exact and_congr ihφ ihψ

def eraseBoxes [Inhabited Atom] : Formula Atom Agent → Formula Atom Agent
  | .atom p => .atom p
  | .neg φ => .neg (eraseBoxes φ)
  | .conj φ ψ => .conj (eraseBoxes φ) (eraseBoxes ψ)
  | .box _ _ => Formula.verum

theorem eraseBoxes_propositional [Inhabited Atom] (φ : Formula Atom Agent) :
    Propositional (eraseBoxes φ) := by
  induction φ with
  | atom p => exact .atom p
  | neg φ ih => exact .neg ih
  | conj φ ψ ihφ ihψ => exact .conj ihφ ihψ
  | box i φ ih => exact .neg (.conj (.atom _) (.neg (.atom _)))

theorem eraseBoxes_satisfies [Inhabited Atom] (M : Model World Atom Agent)
    (x : World) (φ : Formula Atom Agent) :
    (targetCut M ∅).Satisfies x φ ↔ M.Satisfies x (eraseBoxes φ) := by
  induction φ generalizing x with
  | atom p => rfl
  | neg φ ih => exact not_congr (ih x)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ x) (ihψ x)
  | box i φ ih =>
    constructor
    · intro _
      exact Model.satisfies_verum M x
    · intro _ y hy
      exact False.elim hy.2

/-- Semantic equivalence over all models in the specified world universe. -/
def Equivalent (φ ψ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent) (x : World),
    M.Satisfies x φ ↔ M.Satisfies x ψ

def PropositionalEquivalent (φ : Formula Atom Agent) : Prop :=
  ∃ ψ, Propositional ψ ∧ Equivalent.{u} φ ψ

def UniversalEquivalent (φ : Formula Atom Agent) : Prop :=
  ∃ ψ, Universal ψ ∧ Equivalent.{u} φ ψ

def ExistentialEquivalent (φ : Formula Atom Agent) : Prop :=
  ∃ ψ, Existential ψ ∧ Equivalent.{u} φ ψ

theorem UniversalEquivalent.deletionMonotone {φ : Formula Atom Agent}
    (hφ : UniversalEquivalent.{u} φ) : DeletionMonotone.{u} φ := by
  obtain ⟨ψ,hψ,heq⟩ := hφ
  intro World M N hNM x hx
  exact (heq N x).mpr (hψ.preserved_arrowSubmodel hNM ((heq M x).mp hx))

theorem ExistentialEquivalent.deletionAntimonotone {φ : Formula Atom Agent}
    (hφ : ExistentialEquivalent.{u} φ) : DeletionAntimonotone.{u} φ := by
  obtain ⟨ψ,hψ,heq⟩ := hφ
  intro World M N hNM x hx
  exact (heq M x).mpr (hψ.preserved_arrowExtension hNM ((heq N x).mp hx))

theorem propositionalEquivalent_iff_both_deletion [Inhabited Atom]
    (φ : Formula Atom Agent) :
    PropositionalEquivalent.{u} φ ↔
      DeletionMonotone.{u} φ ∧ DeletionAntimonotone.{u} φ := by
  constructor
  · rintro ⟨ψ,hψ,heq⟩
    constructor
    · intro World M N hNM x hx
      exact (heq N x).mpr ((hψ.valuation_invariant hNM.val_eq x).mpr ((heq M x).mp hx))
    · intro World M N hNM x hx
      exact (heq M x).mpr ((hψ.valuation_invariant hNM.val_eq x).mp ((heq N x).mp hx))
  · rintro ⟨hd,ha⟩
    refine ⟨eraseBoxes φ, eraseBoxes_propositional φ, ?_⟩
    intro World M x
    rw [← eraseBoxes_satisfies M x φ]
    exact ⟨hd M _ (targetCut_arrowSubmodel M ∅) x,
      ha M _ (targetCut_arrowSubmodel M ∅) x⟩

/-- Negation normal form for the propositional fragment, producing witnesses
belonging literally to both grammars of Definition 18. -/
theorem Propositional.both_normal_forms {φ : Formula Atom Agent}
    (hφ : Propositional φ) :
    ∃ ψ χ, Universal ψ ∧ Existential ψ ∧ Universal χ ∧ Existential χ ∧
      Equivalent.{u} φ ψ ∧ Equivalent.{u} (.neg φ) χ := by
  induction hφ with
  | atom p =>
    exact ⟨.atom p, .neg (.atom p), .atom p, .atom p, .negAtom p,
      .negAtom p, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  | neg hφ ih =>
    obtain ⟨ψ,χ,huψ,heψ,huχ,heχ,hψ,hχ⟩ := ih
    refine ⟨χ,ψ,huχ,heχ,huψ,heψ,hχ,?_⟩
    intro World M x
    simpa only [Model.satisfies_neg, not_not] using hψ M x
  | conj hφ hθ ihφ ihθ =>
    obtain ⟨ψ,χ,huψ,heψ,huχ,heχ,hψ,hχ⟩ := ihφ
    obtain ⟨ρ,σ,huρ,heρ,huσ,heσ,hρ,hσ⟩ := ihθ
    refine ⟨.conj ψ ρ, Formula.or χ σ, .conj huψ huρ, .conj heψ heρ,
      .disj huχ huσ, .disj heχ heσ, ?_, ?_⟩
    · intro World M x
      exact and_congr (hψ M x) (hρ M x)
    · intro World M x
      classical
      rw [Model.satisfies_neg, Model.satisfies_and, Model.satisfies_or]
      rw [← hχ M x, ← hσ M x]
      exact not_and_or

/-- Corollary 20(1) iff (2): the common semantic fragment is precisely the
propositional fragment. This does not assume a modal preservation theorem. -/
theorem propositionalEquivalent_iff_both_fragments [Inhabited Atom]
    (φ : Formula Atom Agent) :
    PropositionalEquivalent.{u} φ ↔
      UniversalEquivalent.{u} φ ∧ ExistentialEquivalent.{u} φ := by
  constructor
  · rintro ⟨ψ,hψ,hφ⟩
    obtain ⟨χ,_,hu,he,_,_,hc,_⟩ := Propositional.both_normal_forms.{u} hψ
    have h : Equivalent.{u} φ χ := fun M x => (hφ M x).trans (hc M x)
    exact ⟨⟨χ,hu,h⟩, ⟨χ,he,h⟩⟩
  · rintro ⟨hu,he⟩
    exact (propositionalEquivalent_iff_both_deletion φ).mpr
      ⟨hu.deletionMonotone, he.deletionAntimonotone⟩

theorem Propositional.update_satisfies_iff {φ : Formula Atom Agent}
    (hφ : Propositional φ) (M : Model World Atom Agent) (ψ : Formula Atom Agent)
    (x : World) : (M.update ψ).Satisfies x φ ↔ M.Satisfies x φ :=
  hφ.valuation_invariant (M := M.update ψ) (N := M) rfl x

theorem Propositional.update_after_eq_conjunction {φ : Formula Atom Agent}
    (hφ : Propositional φ) (M : Model World Atom Agent) (ψ : Formula Atom Agent) :
    (M.update ψ).update φ = M.update (.conj φ ψ) := by
  apply Model.ext'
  · intro i x y
    change (M.rel i x y ∧ M.Satisfies y ψ) ∧ (M.update ψ).Satisfies y φ ↔
      M.rel i x y ∧ M.Satisfies y φ ∧ M.Satisfies y ψ
    rw [hφ.update_satisfies_iff M ψ y]
    constructor
    · exact fun h => ⟨h.1.1,h.2,h.1.2⟩
    · exact fun h => ⟨⟨h.1,h.2.2⟩,h.2.1⟩
  · intro p x
    rfl

theorem Propositional.commutes_atom {φ : Formula Atom Agent}
    (hφ : Propositional φ) (M : Model World Atom Agent) (p : Atom) :
    (M.update φ).update (.atom p) = (M.update (.atom p)).update φ := by
  rw [(Propositional.atom p).update_after_eq_conjunction,
    hφ.update_after_eq_conjunction]
  apply Model.ext'
  · intro i x y
    change M.rel i x y ∧ (M.val p y ∧ M.Satisfies y φ) ↔
      M.rel i x y ∧ (M.Satisfies y φ ∧ M.val p y)
    exact and_congr Iff.rfl and_comm
  · intro q x
    rfl

end PropertiesOfPublicAnnouncementsAsOperators
