import PropertiesOfPALAndBPALOperators.Algebra
import Mathlib.Data.Fintype.EquivFin

/-! The fresh-atom argument for Lemma 11 in BPAL. Quantification over all
valuations on a fixed frame is essential; observational equivalence in one
particular model alone does not imply equality of its accessibility relations. -/

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

def bpalAtoms [DecidableEq Atom] : BPALFormula Atom Agent → Finset Atom
  | .atom p => {p}
  | .neg φ => bpalAtoms φ
  | .conj φ ψ => bpalAtoms φ ∪ bpalAtoms ψ
  | .box _ φ => bpalAtoms φ
  | .announce φ ψ => bpalAtoms φ ∪ bpalAtoms ψ

def bpalSequenceAtoms [DecidableEq Atom] : List (BPALFormula Atom Agent) → Finset Atom
  | [] => ∅
  | φ :: σ => bpalAtoms φ ∪ bpalSequenceAtoms σ

theorem bpalSatisfies_valuation_congr [DecidableEq Atom]
    (M N : Model World Atom Agent) (φ : BPALFormula Atom Agent)
    (h : ∀ p ∈ bpalAtoms φ, ∀ x, M.val p x ↔ N.val p x)
    (R : Agent → World → World → Prop) (x : World) :
    BPAL.Satisfies M R x φ ↔ BPAL.Satisfies N R x φ := by
  induction φ generalizing R x with
  | atom p => exact h p (by simp [bpalAtoms]) x
  | neg φ ih =>
      exact not_congr (ih h R x)
  | conj φ ψ ihφ ihψ =>
      exact and_congr
        (ihφ (fun p hp => h p (Finset.mem_union_left _ hp)) R x)
        (ihψ (fun p hp => h p (Finset.mem_union_right _ hp)) R x)
  | box i φ ih =>
      apply forall_congr'; intro y
      exact imp_congr_right (fun _ => ih h R y)
  | announce φ ψ ihφ ihψ =>
      have hr : bpalUpdate M φ R = bpalUpdate N φ R := by
        funext i y z
        apply propext
        exact and_congr Iff.rfl
          (ihφ (fun p hp => h p (Finset.mem_union_left _ hp)) R z)
      change BPAL.Satisfies M (bpalUpdate M φ R) x ψ ↔
        BPAL.Satisfies N (bpalUpdate N φ R) x ψ
      rw [hr]
      exact ihψ (fun p hp => h p (Finset.mem_union_right _ hp)) _ x

theorem bpalSequence_valuation_congr [DecidableEq Atom]
    (M N : Model World Atom Agent) (σ : List (BPALFormula Atom Agent))
    (h : ∀ p ∈ bpalSequenceAtoms σ, ∀ x, M.val p x ↔ N.val p x)
    (R : Agent → World → World → Prop) :
    bpalSequence M σ R = bpalSequence N σ R := by
  induction σ generalizing R with
  | nil => rfl
  | cons φ σ ih =>
      have hr : bpalUpdate M φ R = bpalUpdate N φ R := by
        funext i x y
        apply propext
        exact and_congr Iff.rfl (bpalSatisfies_valuation_congr M N φ
          (fun p hp => h p (Finset.mem_union_left _ hp)) R y)
      change bpalSequence M σ (bpalUpdate M φ R) =
        bpalSequence N σ (bpalUpdate N φ R)
      rw [hr]
      exact ih (fun p hp => h p (Finset.mem_union_right _ hp)) _

/-- Lemma 11, BPAL, on an arbitrary frame. Consequently it holds on any
class of frames, without a closure assumption on that class. -/
theorem bpalSequence_eq_iff_observations [Infinite Atom]
    (R : Agent → World → World → Prop) (σ τ : List (BPALFormula Atom Agent)) :
    (∀ V : Atom → World → Prop,
      bpalSequence (⟨R, V⟩ : Model World Atom Agent) σ R =
        bpalSequence (⟨R, V⟩ : Model World Atom Agent) τ R) ↔
    (∀ (V : Atom → World → Prop) (χ : BPALFormula Atom Agent) (x : World),
      BPAL.Satisfies (⟨R, V⟩ : Model World Atom Agent) R x (bpalAnnouncements σ χ) ↔
        BPAL.Satisfies (⟨R, V⟩ : Model World Atom Agent) R x (bpalAnnouncements τ χ)) := by
  classical
  constructor
  · intro h V χ x
    rw [bpalAnnouncements_satisfies, bpalAnnouncements_satisfies, h V]
  · intro h V
    obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset
      (bpalSequenceAtoms σ ∪ bpalSequenceAtoms τ)
    have hqσ : q ∉ bpalSequenceAtoms σ := fun h' => hq (Finset.mem_union_left _ h')
    have hqτ : q ∉ bpalSequenceAtoms τ := fun h' => hq (Finset.mem_union_right _ h')
    funext i x y
    apply propext
    let V' : Atom → World → Prop := fun p z => if p = q then z = y else V p z
    have hs : bpalSequence (⟨R, V⟩ : Model World Atom Agent) σ R =
        bpalSequence (⟨R, V'⟩ : Model World Atom Agent) σ R := by
      apply bpalSequence_valuation_congr
      intro p hp z
      have hpq : p ≠ q := fun he => hqσ (he ▸ hp)
      simp only [V', hpq, if_false]
    have ht : bpalSequence (⟨R, V⟩ : Model World Atom Agent) τ R =
        bpalSequence (⟨R, V'⟩ : Model World Atom Agent) τ R := by
      apply bpalSequence_valuation_congr
      intro p hp z
      have hpq : p ≠ q := fun he => hqτ (he ▸ hp)
      simp only [V', hpq, if_false]
    have ho := h V' (.neg (.box i (.neg (.atom q)))) x
    rw [bpalAnnouncements_satisfies, bpalAnnouncements_satisfies] at ho
    have ho' : bpalSequence (⟨R, V'⟩ : Model World Atom Agent) σ R i x y ↔
        bpalSequence (⟨R, V'⟩ : Model World Atom Agent) τ R i x y := by
      simpa only [BPAL.Satisfies, V', if_pos rfl, not_forall, Classical.not_imp,
        not_not, exists_prop, exists_eq_right] using ho
    rw [hs, ht]
    exact ho'

/-- Theorem 12(1) iff (2), PAL. -/
theorem pal_commute_iff_postconditions [Inhabited Atom]
    (M : Model World Atom Agent) (φ ψ : PALFormula Atom Agent) (S : Set World) :
    palUpdate M ψ (palUpdate M φ S) = palUpdate M φ (palUpdate M ψ S) ↔
      ∀ χ x, S x →
        (PAL.Satisfies M S x (.announce φ (.announce ψ χ)) ↔
          PAL.Satisfies M S x (.announce ψ (.announce φ χ))) := by
  exact palSequence_eq_iff M [φ, ψ] [ψ, φ] S

/-- Theorem 12(1) iff (2), BPAL, on an arbitrary frame. -/
theorem bpal_commute_iff_postconditions [Infinite Atom]
    (R : Agent → World → World → Prop) (φ ψ : BPALFormula Atom Agent) :
    (∀ V : Atom → World → Prop,
      bpalUpdate (⟨R, V⟩ : Model World Atom Agent) ψ
          (bpalUpdate (⟨R, V⟩ : Model World Atom Agent) φ R) =
        bpalUpdate (⟨R, V⟩ : Model World Atom Agent) φ
          (bpalUpdate (⟨R, V⟩ : Model World Atom Agent) ψ R)) ↔
    (∀ (V : Atom → World → Prop) (χ : BPALFormula Atom Agent) (x : World),
      BPAL.Satisfies (⟨R, V⟩ : Model World Atom Agent) R x
          (.announce φ (.announce ψ χ)) ↔
        BPAL.Satisfies (⟨R, V⟩ : Model World Atom Agent) R x
          (.announce ψ (.announce φ χ))) := by
  exact bpalSequence_eq_iff_observations R [φ, ψ] [ψ, φ]

/-- Theorem 13(1) iff (2), PAL. -/
theorem pal_strongCommute_iff_postconditions [Inhabited Atom]
    (M : Model World Atom Agent) (φ ψ : PALFormula Atom Agent) (S : Set World) :
    PalStrongCommute M φ ψ S ↔
      (∀ χ x, S x →
        (PAL.Satisfies M S x (.announce φ (.announce ψ χ)) ↔
          PAL.Satisfies M S x (.announce (.conj φ ψ) χ))) ∧
      (∀ χ x, S x →
        (PAL.Satisfies M S x (.announce ψ (.announce φ χ)) ↔
          PAL.Satisfies M S x (.announce (.conj φ ψ) χ))) := by
  exact and_congr (palSequence_eq_iff M [φ, ψ] [.conj φ ψ] S)
    (palSequence_eq_iff M [ψ, φ] [.conj φ ψ] S)

/-- Theorem 13(1) iff (2), BPAL. -/
theorem bpal_strongCommute_iff_postconditions [Infinite Atom]
    (R : Agent → World → World → Prop) (φ ψ : BPALFormula Atom Agent) :
    (∀ V : Atom → World → Prop,
      BpalStrongCommute (⟨R, V⟩ : Model World Atom Agent) φ ψ R) ↔
      (∀ (V : Atom → World → Prop) (χ : BPALFormula Atom Agent) (x : World),
        BPAL.Satisfies (⟨R, V⟩ : Model World Atom Agent) R x
            (.announce φ (.announce ψ χ)) ↔
          BPAL.Satisfies (⟨R, V⟩ : Model World Atom Agent) R x
            (.announce (.conj φ ψ) χ)) ∧
      (∀ (V : Atom → World → Prop) (χ : BPALFormula Atom Agent) (x : World),
        BPAL.Satisfies (⟨R, V⟩ : Model World Atom Agent) R x
            (.announce ψ (.announce φ χ)) ↔
          BPAL.Satisfies (⟨R, V⟩ : Model World Atom Agent) R x
            (.announce (.conj φ ψ) χ)) := by
  simp only [BpalStrongCommute, forall_and]
  exact and_congr (bpalSequence_eq_iff_observations R [φ, ψ] [.conj φ ψ])
    (bpalSequence_eq_iff_observations R [ψ, φ] [.conj φ ψ])

end PropertiesOfPALAndBPALOperators
