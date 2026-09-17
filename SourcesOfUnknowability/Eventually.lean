import SourcesOfUnknowability.DynamicResults
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card

/-!
# Eventual self-refutation in S5

This proves the remaining dynamic direction of Theorem 3. The argument works
with arbitrary (possibly infinite) models. Within one S5 equivalence class,
truth of a formula on any announced submodel depends only on the values of its
finitely many proposition letters. Every truthful announcement in an always
informative formula removes a represented valuation type, so the designated
point cannot continue to satisfy the formula forever.
-/

namespace SourcesOfUnknowability.Eventually

open ClassificationSigmaValidity

universe u v

variable {World : Type u} {Atom : Type v}

noncomputable section

local instance : DecidableEq Atom := Classical.decEq Atom

/-- The truth assignment to the atoms in `A` at a state, represented as the
set of atoms in `A` that are true. -/
noncomputable def atomType (M : Model World Atom Unit)
    (A : Finset Atom) (x : World) : Finset Atom := by
  classical
  exact A.filter (fun p => M.val p x)

theorem atomType_subset (M : Model World Atom Unit)
    (A : Finset Atom) (x : World) : atomType M A x ⊆ A := by
  classical
  exact Finset.filter_subset _ _

theorem val_iff_of_atomType_eq (M : Model World Atom Unit)
    (A : Finset Atom) (x y : World)
    (h : atomType M A x = atomType M A y)
    {p : Atom} (hp : p ∈ A) : M.val p x ↔ M.val p y := by
  classical
  have hmem : (p ∈ atomType M A x) ↔ (p ∈ atomType M A y) :=
    Iff.of_eq (congrArg (fun s : Finset Atom => p ∈ s) h)
  simpa [atomType, hp] using hmem

/-- Worlds with the same atom type and the same surviving successors agree
on every formula supported on `A`. -/
theorem satisfiesOn_iff_of_sameType (M : Model World Atom Unit)
    (A : Finset Atom) (phi : Formula Atom Unit) :
    ∀ (U : Set World) (x y : World),
      atomType M A x = atomType M A y →
      (∀ z, z ∈ U → (M.rel () x z ↔ M.rel () y z)) →
      phi.atoms ⊆ A →
      (Dynamic.SatisfiesOn M U x phi ↔ Dynamic.SatisfiesOn M U y phi) := by
  classical
  induction phi with
  | atom p =>
      intro U x y htype _ hA
      have hp : p ∈ A := hA (by simp [Formula.atoms])
      exact val_iff_of_atomType_eq M A x y htype hp
  | neg psi ih =>
      intro U x y htype hrel hA
      exact not_congr (ih U x y htype hrel (by simpa [Formula.atoms] using hA))
  | conj psi theta ihPsi ihTheta =>
      intro U x y htype hrel hA
      have hPsi : psi.atoms ⊆ A := by
        intro p hp
        exact hA (Finset.mem_union.mpr (Or.inl hp))
      have hTheta : theta.atoms ⊆ A := by
        intro p hp
        exact hA (Finset.mem_union.mpr (Or.inr hp))
      exact and_congr (ihPsi U x y htype hrel hPsi)
        (ihTheta U x y htype hrel hTheta)
  | box i psi ih =>
      intro U x y _ hrel _
      have hi : i = () := Subsingleton.elim i ()
      subst i
      constructor
      · intro h z hz hyz
        exact h z hz ((hrel z hz).mpr hyz)
      · intro h z hz hxz
        exact h z hz ((hrel z hz).mp hxz)

/-- All atom types represented in a set of worlds. This finite set exists
even when the world type itself is infinite. -/
noncomputable def typesPresent (M : Model World Atom Unit)
    (A : Finset Atom) (U : Set World) : Finset (Finset Atom) := by
  classical
  exact A.powerset.filter (fun t => ∃ x, x ∈ U ∧ atomType M A x = t)

theorem mem_typesPresent_iff (M : Model World Atom Unit)
    (A : Finset Atom) (U : Set World) (t : Finset Atom) :
    t ∈ typesPresent M A U ↔
      t ⊆ A ∧ ∃ x, x ∈ U ∧ atomType M A x = t := by
  classical
  simp only [typesPresent, Finset.mem_filter, Finset.mem_powerset]

theorem atomType_mem_typesPresent (M : Model World Atom Unit)
    (A : Finset Atom) (U : Set World) (x : World) (hx : x ∈ U) :
    atomType M A x ∈ typesPresent M A U :=
  (mem_typesPresent_iff M A U _).2
    ⟨atomType_subset M A x, x, hx, rfl⟩

theorem typesPresent_mono (M : Model World Atom Unit)
    (A : Finset Atom) {U V : Set World} (hVU : V ⊆ U) :
    typesPresent M A V ⊆ typesPresent M A U := by
  intro t ht
  obtain ⟨htA, x, hxV, hxt⟩ := (mem_typesPresent_iff M A V t).1 ht
  exact (mem_typesPresent_iff M A U t).2
    ⟨htA, x, hVU hxV, hxt⟩

/-- On a complete single-agent relation, represented atom types strictly
decrease while a point remains true under an always informative formula. -/
private theorem types_strictly_decrease_of_true
    (M : Model World Atom Unit) (hM : IsS5 M)
    (hComplete : ∀ x y : World, M.rel () x y)
    (phi : Formula Atom Unit)
    (hAlways : Dynamic.AlwaysInformative
      (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi)
    (x : World) (n : Nat)
    (hx : Dynamic.TrueAfter M phi n x) :
    (typesPresent M phi.atoms (Dynamic.survivors M phi (n + 1))).card <
      (typesPresent M phi.atoms (Dynamic.survivors M phi n)).card := by
  classical
  let U := Dynamic.survivors M phi n
  let V := Dynamic.survivors M phi (n + 1)
  have hVU : V ⊆ U := by
    intro y hy
    exact (Dynamic.survivors_succ M phi n y).1 hy |>.1
  let N : Model (Subtype U) Atom Unit := M.restrict U
  have hN : IsS5 N := M.restrict_isS5 hM U
  have hxN : N.Satisfies ⟨x, hx.1⟩ phi :=
    (Dynamic.satisfiesOn_iff_restrict M U ⟨x, hx.1⟩ phi).1 hx.2
  have hNotAll : ¬ ∀ z : Subtype U, N.Satisfies z phi := by
    intro hAll
    apply hAlways N hN ⟨x, hx.1⟩ hxN
    ext z
    exact ⟨fun _ => Set.mem_univ z, fun _ => hAll z⟩
  obtain ⟨yU, hyFalse⟩ := not_forall.mp hNotAll
  have hyFalseOn : ¬ Dynamic.SatisfiesOn M U yU.1 phi := by
    intro hy
    exact hyFalse ((Dynamic.satisfiesOn_iff_restrict M U yU phi).1 hy)
  have hNoType : atomType M phi.atoms yU.1 ∉ typesPresent M phi.atoms V := by
    intro htype
    obtain ⟨_, z, hzV, hzt⟩ :=
      (mem_typesPresent_iff M phi.atoms V _).1 htype
    have hzU : z ∈ U := hVU hzV
    have hzTrue : Dynamic.SatisfiesOn M U z phi :=
      (Dynamic.survivors_succ M phi n z).1 hzV |>.2
    have hsame : atomType M phi.atoms yU.1 = atomType M phi.atoms z := hzt.symm
    have heq : Dynamic.SatisfiesOn M U yU.1 phi ↔
        Dynamic.SatisfiesOn M U z phi :=
      satisfiesOn_iff_of_sameType M phi.atoms phi U yU.1 z hsame
        (fun t _ => ⟨fun _ => hComplete z t, fun _ => hComplete yU.1 t⟩)
        Finset.Subset.rfl
    exact hyFalseOn (heq.mpr hzTrue)
  have hsubset : typesPresent M phi.atoms V ⊆ typesPresent M phi.atoms U :=
    typesPresent_mono M phi.atoms hVU
  have hstrict : typesPresent M phi.atoms V ⊂ typesPresent M phi.atoms U :=
    (Finset.ssubset_iff_of_subset hsubset).2
      ⟨atomType M phi.atoms yU.1,
        atomType_mem_typesPresent M phi.atoms U yU.1 yU.2,
        hNoType⟩
  exact Finset.card_lt_card hstrict

/-- Eventual self-refutation for a complete S5 cluster. -/
private theorem eventually_of_complete
    (M : Model World Atom Unit) (hM : IsS5 M)
    (hComplete : ∀ x y : World, M.rel () x y)
    (phi : Formula Atom Unit)
    (hAlways : Dynamic.AlwaysInformative
      (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi)
    (x : World) (_hx : M.Satisfies x phi) :
    ∃ n, ¬ Dynamic.TrueAfter M phi n x := by
  classical
  by_contra hNoRefute
  have hTrue : ∀ n, Dynamic.TrueAfter M phi n x := by
    intro n
    by_contra hn
    exact hNoRefute ⟨n, hn⟩
  let count (n : Nat) : Nat :=
    (typesPresent M phi.atoms (Dynamic.survivors M phi n)).card
  have hDecrease : ∀ n, count (n + 1) < count n := by
    intro n
    exact types_strictly_decrease_of_true M hM hComplete phi hAlways x n (hTrue n)
  have hBound : ∀ n, n + count n ≤ count 0 := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
        have hd := hDecrease n
        omega
  have hImpossible := hBound (count 0 + 1)
  omega

/-- Restriction to a forward-closed carrier commutes with evaluating a
formula in an arbitrary further restricted carrier. -/
private theorem satisfiesOn_restrict_iff (M : Model World Atom Unit)
    (C : Set World) (hC : M.ForwardClosed C)
    (U : Set World) (V : Set (Subtype C))
    (hV : ∀ z : Subtype C, z ∈ V ↔ z.1 ∈ U)
    (x : Subtype C) (phi : Formula Atom Unit) :
    Dynamic.SatisfiesOn (M.restrict C) V x phi ↔
      Dynamic.SatisfiesOn M U x.1 phi := by
  induction phi generalizing x with
  | atom p => rfl
  | neg psi ih => exact not_congr (ih x)
  | conj psi theta ihPsi ihTheta =>
      exact and_congr (ihPsi x) (ihTheta x)
  | box i psi ih =>
      constructor
      · intro h z hzU hxz
        have hzC : z ∈ C := hC x.2 i hxz
        let zC : Subtype C := ⟨z, hzC⟩
        exact (ih zC).1 (h zC ((hV zC).2 hzU) hxz)
      · intro h zC hzV hxz
        exact (ih zC).2 (h zC.1 ((hV zC).1 hzV) hxz)

/-- Iterated announcements in a generated cluster select exactly the
surviving worlds of the original model that lie in that cluster. -/
private theorem survivors_restrict_iff (M : Model World Atom Unit)
    (C : Set World) (hC : M.ForwardClosed C)
    (phi : Formula Atom Unit) :
    ∀ n (x : Subtype C),
      x ∈ Dynamic.survivors (M.restrict C) phi n ↔
        x.1 ∈ Dynamic.survivors M phi n := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [Dynamic.survivors]
  | succ n ih =>
      intro x
      change (x ∈ Dynamic.survivors (M.restrict C) phi n ∧
        Dynamic.SatisfiesOn (M.restrict C)
          (Dynamic.survivors (M.restrict C) phi n) x phi) ↔
        (x.1 ∈ Dynamic.survivors M phi n ∧
          Dynamic.SatisfiesOn M (Dynamic.survivors M phi n) x.1 phi)
      exact and_congr (ih x)
        (satisfiesOn_restrict_iff M C hC
          (Dynamic.survivors M phi n)
          (Dynamic.survivors (M.restrict C) phi n)
          (fun z => ih z) x phi)

private theorem trueAfter_restrict_iff (M : Model World Atom Unit)
    (C : Set World) (hC : M.ForwardClosed C)
    (phi : Formula Atom Unit) (n : Nat) (x : Subtype C) :
    Dynamic.TrueAfter (M.restrict C) phi n x ↔
      Dynamic.TrueAfter M phi n x.1 := by
  exact and_congr (survivors_restrict_iff M C hC phi n x)
    (satisfiesOn_restrict_iff M C hC
      (Dynamic.survivors M phi n)
      (Dynamic.survivors (M.restrict C) phi n)
      (fun z => survivors_restrict_iff M C hC phi n z) x phi)

/-- The missing S5 direction of Theorem 3: every always informative
single-agent formula is eventually self-refuting, even on infinite models. -/
theorem alwaysInformative_implies_eventuallySelfRefuting_s5
    (phi : Formula Atom Unit) :
    Dynamic.AlwaysInformative
      (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi →
    Dynamic.EventuallySelfRefuting
      (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi := by
  intro hAlways World M hM x hx
  let C : Set World := {y | M.rel () x y}
  have hC : M.ForwardClosed C := by
    intro y hy i z hyz
    have hi : i = () := Subsingleton.elim i ()
    subst i
    exact (hM ()).2.1 hy hyz
  let N : Model (Subtype C) Atom Unit := M.restrict C
  have hN : IsS5 N := M.restrict_isS5 hM C
  have hComplete : ∀ y z : Subtype C, N.rel () y z := by
    intro y z
    exact (hM ()).2.2 y.2 z.2
  let xC : Subtype C := ⟨x, (hM ()).1 x⟩
  have hxN : N.Satisfies xC phi :=
    (M.restrict_satisfies_iff C hC xC phi).2 hx
  obtain ⟨n, hn⟩ := eventually_of_complete N hN hComplete phi hAlways xC hxN
  exact ⟨n, fun hOriginal => hn
    ((trueAfter_restrict_iff M C hC phi n xC).2 hOriginal)⟩

/-- In single-agent S5, the three dynamic and static descriptions in
Theorem 3(1),(5),(6) coincide. -/
theorem unbelievable_iff_eventuallySelfRefuting_s5
    (phi : Formula Atom Unit) :
    Static.Unbelievable
      (Static.Classes.S5 : FrameClass.{u} Atom Unit) () phi ↔
    Dynamic.EventuallySelfRefuting
      (Static.Classes.S5 : FrameClass.{u} Atom Unit) phi := by
  constructor
  · intro h
    exact alwaysInformative_implies_eventuallySelfRefuting_s5 phi
      ((DynamicResults.unbelievable_iff_alwaysInformative_s5 phi).1 h)
  · intro h
    exact DynamicResults.eventuallySelfRefuting_implies_unbelievable_s5 phi h

end

end SourcesOfUnknowability.Eventually
