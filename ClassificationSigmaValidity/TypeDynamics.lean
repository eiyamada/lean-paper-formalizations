import ClassificationSigmaValidity.FrameClass
import ClassificationSigmaValidity.TypeFormulas

/-!
# Dynamics of exact state types

These lemmas turn the paper's transition diagrams into reusable proof rules.
-/

namespace ClassificationSigmaValidity

universe u v w z

namespace TypeFormulas

variable {World : Type u} {Atom : Type v} {Agent : Type w} {Tag : Type z}

/-- Exact propositional types are invariant under believed announcements. -/
theorem update_satisfies_exactType_iff [Inhabited Atom] [DecidableEq Tag]
    (M : Model World Atom Agent) (announcement : Formula Atom Agent)
    (x : World) (atomOf : Tag -> Atom) (typeUniverse : List Tag) (t : Tag) :
    (M.update announcement).Satisfies x (exactType (Agent := Agent) atomOf typeUniverse t) <->
      M.Satisfies x (exactType (Agent := Agent) atomOf typeUniverse t) := by
  simp [exactType, Model.Satisfies]

/-- Exact propositional types are invariant through every finite iteration. -/
theorem iterateUpdate_satisfies_exactType_iff [Inhabited Atom] [DecidableEq Tag]
    (M : Model World Atom Agent) (announcement : Formula Atom Agent)
    (n : Nat) (x : World) (atomOf : Tag -> Atom) (typeUniverse : List Tag) (t : Tag) :
    (M.iterateUpdate announcement n).Satisfies x
        (exactType (Agent := Agent) atomOf typeUniverse t) <->
      M.Satisfies x (exactType (Agent := Agent) atomOf typeUniverse t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Model.iterateUpdate_succ, update_satisfies_exactType_iff, ih]

/-- In K45, successor-type descriptions agree along an arrow. -/
theorem successorTypes_agreement [Inhabited Atom] [DecidableEq Tag]
    {M : Model World Atom Agent} (hM : IsK45 M)
    {x y : World} {i : Agent} (hxy : M.rel i x y)
    (atomOf : Tag -> Atom) (typeUniverse types : List Tag) :
    M.Satisfies x (successorTypes i atomOf typeUniverse types) <->
      M.Satisfies y (successorTypes i atomOf typeUniverse types) := by
  simp only [satisfies_successorTypes]
  have hrel := Frame.successor_eq_of_transitive_euclidean
    (R := M.rel i) (hM i).1 (hM i).2 hxy
  constructor <;> rintro ⟨hall, hevery⟩
  · constructor
    · intro z hyz
      exact hall z ((hrel z).mpr hyz)
    · intro t ht
      rcases hevery t ht with ⟨z, hxz, hz⟩
      exact ⟨z, (hrel z).mp hxz, hz⟩
  · constructor
    · intro z hxz
      exact hall z ((hrel z).mp hxz)
    · intro t ht
      rcases hevery t ht with ⟨z, hyz, hz⟩
      exact ⟨z, (hrel z).mpr hyz, hz⟩

/-- Filter a successor-type set through one announcement.  The hypothesis
`hcharacterize` says exactly which successor types satisfy the announcement. -/
theorem update_satisfies_successorTypes_of_filter
    [Inhabited Atom] [DecidableEq Tag]
    (M : Model World Atom Agent) (x : World) (i : Agent)
    (atomOf : Tag -> Atom) (typeUniverse types kept : List Tag)
    (announcement : Formula Atom Agent)
    (hTypes : M.Satisfies x (successorTypes i atomOf typeUniverse types))
    (hkept : forall t, t ∈ kept -> t ∈ types)
    (hcharacterize : forall y, M.rel i x y ->
      (M.Satisfies y announcement <->
        exists t, t ∈ kept /\ M.Satisfies y (exactType atomOf typeUniverse t))) :
    (M.update announcement).Satisfies x
      (successorTypes i atomOf typeUniverse kept) := by
  rw [satisfies_successorTypes] at hTypes ⊢
  constructor
  · intro y hxy
    rcases (hcharacterize y hxy.1).mp hxy.2 with ⟨t, ht, hty⟩
    exact ⟨t, ht, (update_satisfies_exactType_iff M announcement y atomOf
      typeUniverse t).mpr hty⟩
  · intro t ht
    rcases hTypes.2 t (hkept t ht) with ⟨y, hxy, hty⟩
    have hyann : M.Satisfies y announcement :=
      (hcharacterize y hxy).mpr ⟨t, ht, hty⟩
    exact ⟨y, ⟨hxy, hyann⟩,
      (update_satisfies_exactType_iff M announcement y atomOf typeUniverse t).mpr hty⟩

/-- If no successor satisfies the announcement, the updated successor type set
is empty. -/
theorem update_satisfies_successorTypes_empty
    [Inhabited Atom] [DecidableEq Tag]
    (M : Model World Atom Agent) (x : World) (i : Agent)
    (atomOf : Tag -> Atom) (typeUniverse : List Tag)
    (announcement : Formula Atom Agent)
    (hnone : forall y, M.rel i x y -> Not (M.Satisfies y announcement)) :
    (M.update announcement).Satisfies x
      (successorTypes i atomOf typeUniverse []) := by
  rw [satisfies_successorTypes]
  constructor
  · intro y hxy
    exact (hnone y hxy.1 hxy.2).elim
  · intro t ht
    simp at ht

end TypeFormulas

end ClassificationSigmaValidity
