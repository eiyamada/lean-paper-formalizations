import PropertiesOfPALAndBPALOperators.Propositional

/-! # Negation duality of the universal and existential fragments -/

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity

universe u v w
variable {Atom : Type v} {Agent : Type w}

theorem Universal.neg_equivalent_existential {φ : Formula Atom Agent}
    (hφ : Universal φ) : ∃ ψ, Existential ψ ∧ Equivalent.{u} (.neg φ) ψ := by
  classical
  induction hφ with
  | atom p => exact ⟨.neg (.atom p), .negAtom p, fun _ _ => Iff.rfl⟩
  | negAtom p =>
      exact ⟨.atom p, .atom p, fun M x => by simp only [Model.satisfies_neg, not_not]⟩
  | conj hφ hχ ihφ ihχ =>
      obtain ⟨ψ, hψ, eψ⟩ := ihφ
      obtain ⟨ρ, hρ, eρ⟩ := ihχ
      refine ⟨Formula.or ψ ρ, .disj hψ hρ, ?_⟩
      intro W M x
      rw [Model.satisfies_neg, Model.satisfies_and, Model.satisfies_or,
        ← eψ M x, ← eρ M x]
      exact not_and_or
  | disj hφ hχ ihφ ihχ =>
      obtain ⟨ψ, hψ, eψ⟩ := ihφ
      obtain ⟨ρ, hρ, eρ⟩ := ihχ
      refine ⟨.conj ψ ρ, .conj hψ hρ, ?_⟩
      intro W M x
      rw [Model.satisfies_neg, Model.satisfies_or, Model.satisfies_and,
        ← eψ M x, ← eρ M x]
      exact not_or
  | box i hφ ih =>
      obtain ⟨ψ, hψ, eψ⟩ := ih
      refine ⟨Formula.dia i ψ, .dia i hψ, ?_⟩
      intro W M x
      simp only [Model.satisfies_neg, Model.satisfies_box, Model.satisfies_dia,
        not_forall, exists_prop]
      exact exists_congr fun y => and_congr Iff.rfl (eψ M y)

theorem Existential.neg_equivalent_universal {φ : Formula Atom Agent}
    (hφ : Existential φ) : ∃ ψ, Universal ψ ∧ Equivalent.{u} (.neg φ) ψ := by
  classical
  induction hφ with
  | atom p => exact ⟨.neg (.atom p), .negAtom p, fun _ _ => Iff.rfl⟩
  | negAtom p =>
      exact ⟨.atom p, .atom p, fun M x => by simp only [Model.satisfies_neg, not_not]⟩
  | conj hφ hχ ihφ ihχ =>
      obtain ⟨ψ, hψ, eψ⟩ := ihφ
      obtain ⟨ρ, hρ, eρ⟩ := ihχ
      refine ⟨Formula.or ψ ρ, .disj hψ hρ, ?_⟩
      intro W M x
      rw [Model.satisfies_neg, Model.satisfies_and, Model.satisfies_or,
        ← eψ M x, ← eρ M x]
      exact not_and_or
  | disj hφ hχ ihφ ihχ =>
      obtain ⟨ψ, hψ, eψ⟩ := ihφ
      obtain ⟨ρ, hρ, eρ⟩ := ihχ
      refine ⟨.conj ψ ρ, .conj hψ hρ, ?_⟩
      intro W M x
      rw [Model.satisfies_neg, Model.satisfies_or, Model.satisfies_and,
        ← eψ M x, ← eρ M x]
      exact not_or
  | dia i hφ ih =>
      obtain ⟨ψ, hψ, eψ⟩ := ih
      refine ⟨.box i ψ, .box i hψ, ?_⟩
      intro W M x
      simp only [Model.satisfies_neg, Model.satisfies_dia, Model.satisfies_box,
        not_exists, not_and]
      exact forall_congr' fun y => imp_congr Iff.rfl (eψ M y)

theorem universalEquivalent_neg_iff_existentialEquivalent (φ : Formula Atom Agent) :
    UniversalEquivalent.{u} (.neg φ) ↔ ExistentialEquivalent.{u} φ := by
  classical
  constructor
  · rintro ⟨ψ, hψ, eψ⟩
    obtain ⟨χ, hχ, eχ⟩ := Universal.neg_equivalent_existential.{u} hψ
    refine ⟨χ, hχ, fun M x => ?_⟩
    have he := (not_congr (eψ M x)).trans (eχ M x)
    simpa only [Model.satisfies_neg, not_not] using he
  · rintro ⟨ψ, hψ, eψ⟩
    obtain ⟨χ, hχ, eχ⟩ := Existential.neg_equivalent_universal.{u} hψ
    exact ⟨χ, hχ, fun M x => (not_congr (eψ M x)).trans (eχ M x)⟩

theorem existentialEquivalent_neg_iff_universalEquivalent (φ : Formula Atom Agent) :
    ExistentialEquivalent.{u} (.neg φ) ↔ UniversalEquivalent.{u} φ := by
  classical
  constructor
  · rintro ⟨ψ, hψ, eψ⟩
    obtain ⟨χ, hχ, eχ⟩ := Existential.neg_equivalent_universal.{u} hψ
    refine ⟨χ, hχ, fun M x => ?_⟩
    have he := (not_congr (eψ M x)).trans (eχ M x)
    simpa only [Model.satisfies_neg, not_not] using he
  · rintro ⟨ψ, hψ, eψ⟩
    obtain ⟨χ, hχ, eχ⟩ := Universal.neg_equivalent_existential.{u} hψ
    exact ⟨χ, hχ, fun M x => (not_congr (eψ M x)).trans (eχ M x)⟩

end PropertiesOfPALAndBPALOperators
