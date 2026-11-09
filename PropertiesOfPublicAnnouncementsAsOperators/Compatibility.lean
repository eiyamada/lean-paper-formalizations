import PropertiesOfPublicAnnouncementsAsOperators.Algebra

/-! Static formulas agree in PAL's induced submodel and BPAL's target
restriction. This proves the cross-semantics clauses of Lemma 9 and
Theorems 12 and 13. -/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity

universe u v w
variable {World : Type u} {Atom : Type v} {Agent : Type w}

theorem pal_satisfies_restrict (M : Model World Atom Agent) (S : Set World)
    (φ : Formula Atom Agent) (x : S) :
    PAL.Satisfies M S x.val φ.toPAL ↔ (M.restrict S).Satisfies x φ := by
  induction φ generalizing x with
  | atom p => rfl
  | neg φ ih => exact not_congr (ih x)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ x) (ihψ x)
  | box i φ ih =>
      constructor
      · intro h y hxy
        exact (ih y).mp (h y.val y.property hxy)
      · intro h y hy hxy
        exact (ih ⟨y, hy⟩).mpr (h ⟨y, hy⟩ hxy)

theorem palUpdate_static (M : Model World Atom Agent) (S : Set World)
    (φ : Formula Atom Agent) (x : World) (hx : S x) :
    palUpdate M φ.toPAL S x ↔ (M.restrict S).Satisfies ⟨x, hx⟩ φ := by
  exact (and_iff_right hx).trans (pal_satisfies_restrict M S φ ⟨x, hx⟩)

theorem pal_bpal_static (M : Model World Atom Agent) (S : Set World)
    (φ : Formula Atom Agent) (x : World) :
    PAL.Satisfies M S x φ.toPAL ↔
      BPAL.Satisfies M (fun i a b => M.rel i a b ∧ S b) x φ.toBPAL := by
  induction φ generalizing x with
  | atom p => rfl
  | neg φ ih => exact not_congr (ih x)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ x) (ihψ x)
  | box i φ ih =>
      constructor
      · intro h y hxy
        exact (ih y).mp (h y hxy.2 hxy.1)
      · intro h y hy hxy
        exact (ih y).mpr (h y ⟨hxy, hy⟩)

theorem bpal_static_initial (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (x : World) :
    BPAL.Satisfies M M.rel x φ.toBPAL ↔ M.Satisfies x φ :=
  BPAL.initiallySatisfies_toBPAL M x φ

theorem pal_static_initial (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (x : World) :
    PAL.Satisfies M Set.univ x φ.toPAL ↔ M.Satisfies x φ :=
  PAL.initiallySatisfies_toPAL M x φ

theorem pal_bpal_static_after (M : Model World Atom Agent)
    (φ ψ : Formula Atom Agent) (x : World) :
    PAL.Satisfies M (palUpdate M φ.toPAL Set.univ) x ψ.toPAL ↔
      BPAL.Satisfies M (bpalUpdate M φ.toBPAL M.rel) x ψ.toBPAL := by
  rw [pal_bpal_static]
  have he : (fun i a b => M.rel i a b ∧ palUpdate M φ.toPAL Set.univ b) =
      bpalUpdate M φ.toBPAL M.rel := by
    funext i a b
    apply propext
    change (M.rel i a b ∧ (True ∧ PAL.Satisfies M Set.univ b φ.toPAL)) ↔
      (M.rel i a b ∧ BPAL.Satisfies M M.rel b φ.toBPAL)
    rw [pal_static_initial, bpal_static_initial]
    tauto
  rw [he]

/-- Lemma 9, final assertion. -/
theorem guarded_pal_bpal_equivalent (M : Model World Atom Agent)
    (φ ψ : Formula Atom Agent) (x : World) :
    PAL.InitiallySatisfies M x (.conj φ.toPAL (.announce φ.toPAL ψ.toPAL)) ↔
      BPAL.InitiallySatisfies M x (.conj φ.toBPAL (.announce φ.toBPAL ψ.toBPAL)) := by
  change (PAL.Satisfies M Set.univ x φ.toPAL ∧
      (PAL.Satisfies M Set.univ x φ.toPAL →
        PAL.Satisfies M (palUpdate M φ.toPAL Set.univ) x ψ.toPAL)) ↔
    (BPAL.Satisfies M M.rel x φ.toBPAL ∧
      BPAL.Satisfies M (bpalUpdate M φ.toBPAL M.rel) x ψ.toBPAL)
  rw [pal_static_initial, bpal_static_initial, pal_bpal_static_after]
  tauto

/-- Theorem 12, equivalence of the PAL/BPAL conditions on reflexive frames. -/
theorem pal_bpal_commute_iff [Nonempty Agent]
    (M : Model World Atom Agent) (hM : ∀ i x, M.rel i x x)
    (φ ψ : Formula Atom Agent) :
    (palUpdate M ψ.toPAL (palUpdate M φ.toPAL Set.univ) =
      palUpdate M φ.toPAL (palUpdate M ψ.toPAL Set.univ)) ↔
    (bpalUpdate M ψ.toBPAL (bpalUpdate M φ.toBPAL M.rel) =
      bpalUpdate M φ.toBPAL (bpalUpdate M ψ.toBPAL M.rel)) := by
  rw [pal_commute_iff, bpal_commute_iff, all_targets_iff_of_reflexive M.rel hM]
  have hu (x : World) : (Set.univ : Set World) x ↔ True := Iff.rfl
  simp only [hu, true_implies,
    pal_static_initial, bpal_static_initial, pal_bpal_static_after]

/-- Theorem 13, equivalence of strong commutativity on reflexive frames. -/
theorem pal_bpal_strongCommute_iff [Nonempty Agent]
    (M : Model World Atom Agent) (hM : ∀ i x, M.rel i x x)
    (φ ψ : Formula Atom Agent) :
    PalStrongCommute M φ.toPAL ψ.toPAL Set.univ ↔
      BpalStrongCommute M φ.toBPAL ψ.toBPAL M.rel := by
  rw [pal_strongCommute_iff, bpal_strongCommute_iff]
  rw [all_targets_iff_of_reflexive M.rel hM, all_targets_iff_of_reflexive M.rel hM]
  have hu (x : World) : (Set.univ : Set World) x ↔ True := Iff.rfl
  simp only [hu, true_implies,
    pal_static_initial, bpal_static_initial, pal_bpal_static_after]

end PropertiesOfPublicAnnouncementsAsOperators
