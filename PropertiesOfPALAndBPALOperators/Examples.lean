import PropertiesOfPALAndBPALOperators.Countermodels
import PropertiesOfPALAndBPALOperators.OperatorCharacterizations
import PropertiesOfPALAndBPALOperators.Compatibility

/-! The examples accompanying the algebraic-properties table: failure of
absorption and monotonicity, and commutation without strong commutation. -/

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity

universe u v w

namespace Examples

variable {World : Type u} {Atom : Type v} {Agent : Type w}

def moore (p : Atom) (i : Agent) : Formula Atom Agent :=
  .conj (.atom p) (Formula.dia i (.neg (.atom p)))

def mooreWithAtom (p q : Atom) (i : Agent) : Formula Atom Agent :=
  .conj (moore p i) (.atom q)

theorem moore_false_after (M : Model World Atom Agent) (p : Atom) (i : Agent)
    (α : Formula Atom Agent) (hα : ∀ y, M.Satisfies y α → M.val p y) (x : World) :
    ¬ (M.update α).Satisfies x (moore p i) := by
  rintro ⟨_, hdia⟩
  obtain ⟨y, hxy, hn⟩ := (Model.satisfies_dia _ _ _ _).mp hdia
  exact hn (hα y hxy.2)

theorem bpal_moore_composition_zero (M : Model World Atom Agent) (p q : Atom) (i : Agent) :
    (M.update (moore p i)).update (mooreWithAtom p q i) =
      (⟨fun _ _ _ => False, M.val⟩ : Model World Atom Agent) := by
  apply Model.ext'
  · intro j x y
    exact ⟨fun h => moore_false_after M p i (moore p i) (fun _ ht => ht.1) y h.2.1,
      False.elim⟩
  · intro r x; rfl

theorem bpal_moore_reverse_zero (M : Model World Atom Agent) (p q : Atom) (i : Agent) :
    (M.update (mooreWithAtom p q i)).update (moore p i) =
      (⟨fun _ _ _ => False, M.val⟩ : Model World Atom Agent) := by
  apply Model.ext'
  · intro j x y
    exact ⟨fun h => moore_false_after M p i (mooreWithAtom p q i)
      (fun _ ht => ht.1.1) y h.2, False.elim⟩
  · intro r x; rfl

/-- The two distinct formulas from the manuscript commute on every BPAL model. -/
theorem bpal_moore_commute (M : Model World Atom Agent) (p q : Atom) (i : Agent) :
    (M.update (moore p i)).update (mooreWithAtom p q i) =
      (M.update (mooreWithAtom p q i)).update (moore p i) := by
  rw [bpal_moore_composition_zero, bpal_moore_reverse_zero]

theorem pal_moore_composition_zero (M : Model World Atom Agent) (p q : Atom) (i : Agent) :
    palUpdate M (mooreWithAtom p q i).toPAL (palUpdate M (moore p i).toPAL Set.univ) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have ht := (palUpdate_twice_mem M (mooreWithAtom p q i) (moore p i) x).mp hx
  exact moore_false_after M p i (moore p i) (fun _ h => h.1) x ht.2.1

theorem pal_moore_reverse_zero (M : Model World Atom Agent) (p q : Atom) (i : Agent) :
    palUpdate M (moore p i).toPAL (palUpdate M (mooreWithAtom p q i).toPAL Set.univ) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have ht := (palUpdate_twice_mem M (moore p i) (mooreWithAtom p q i) x).mp hx
  exact moore_false_after M p i (mooreWithAtom p q i) (fun _ h => h.1.1) x ht.2

theorem pal_moore_commute (M : Model World Atom Agent) (p q : Atom) (i : Agent) :
    palUpdate M (mooreWithAtom p q i).toPAL (palUpdate M (moore p i).toPAL Set.univ) =
      palUpdate M (moore p i).toPAL (palUpdate M (mooreWithAtom p q i).toPAL Set.univ) := by
  rw [pal_moore_composition_zero, pal_moore_reverse_zero]

def mooreModel : Model Bool Bool Unit where
  rel _ _ _ := True
  val p x := if p then True else x = true

theorem mooreModel_truth : mooreModel.Satisfies true (moore false ()) := by
  refine ⟨rfl, (Model.satisfies_dia _ _ _ _).mpr ⟨false, trivial, ?_⟩⟩
  change ¬ false = true
  decide

theorem pal_moore_not_strong :
    ¬ PalStrongCommute mooreModel (moore false ()).toPAL
      (mooreWithAtom false true ()).toPAL Set.univ := by
  intro h
  have ht : true ∈ palUpdate mooreModel
      (Formula.conj (moore false ()) (mooreWithAtom false true ())).toPAL Set.univ :=
    (palUpdate_univ_mem _ _ _).mpr ⟨mooreModel_truth, mooreModel_truth, trivial⟩
  change true ∈ palUpdate mooreModel
    (.conj (moore false ()).toPAL (mooreWithAtom false true ()).toPAL) Set.univ at ht
  rw [← h.1, pal_moore_composition_zero] at ht
  exact ht

theorem bpal_moore_not_strong :
    ¬ BpalStrongCommute mooreModel (moore false ()).toBPAL
      (mooreWithAtom false true ()).toBPAL mooreModel.rel := by
  intro h
  exact pal_moore_not_strong
    ((pal_bpal_strongCommute_iff mooreModel (fun _ _ => trivial) _ _).mpr h)

def absorptionModel : Model Bool Bool Unit where
  rel _ _ _ := True
  val p x := if p then x = true else True

theorem pal_absorption_fails :
    palUpdate absorptionModel (.atom true) (palUpdate absorptionModel (.atom false) Set.univ) ≠
        palUpdate absorptionModel (.atom false) Set.univ ∧
    palUpdate absorptionModel (.atom false) (palUpdate absorptionModel (.atom true) Set.univ) ≠
        palUpdate absorptionModel (.atom false) Set.univ := by
  have hp : false ∈ palUpdate absorptionModel (.atom false) Set.univ := ⟨trivial, trivial⟩
  constructor
  · intro h
    have ht := hp
    rw [← h] at ht
    have hbad : false = true := ht.2
    cases hbad
  · intro h
    have ht := hp
    rw [← h] at ht
    have hbad : false = true := ht.1.2
    cases hbad

theorem bpal_absorption_fails :
    (absorptionModel.update (.atom false)).update (.atom true) ≠
        absorptionModel.update (.atom false) ∧
    (absorptionModel.update (.atom true)).update (.atom false) ≠
        absorptionModel.update (.atom false) := by
  have hp : (absorptionModel.update (.atom false)).rel () false false := ⟨trivial, trivial⟩
  constructor
  · intro h
    have ht := hp
    rw [← h] at ht
    have hbad : false = true := ht.2
    cases hbad
  · intro h
    have ht := hp
    rw [← h] at ht
    have hbad : false = true := ht.1.2
    cases hbad

/-- The box announcement is not monotone under induced domain inclusion. -/
theorem pal_monotonicity_fails :
    ∃ S T : Set Bool, S ⊆ T ∧
      ¬ palUpdate Countermodels.twoWorlds (.box () (.atom ())) S ⊆
        palUpdate Countermodels.twoWorlds (.box () (.atom ())) T := by
  let S : Set Bool := fun x => x = true
  refine ⟨S, Set.univ, Set.subset_univ S, ?_⟩
  intro h
  have ht : true ∈ palUpdate Countermodels.twoWorlds (.box () (.atom ())) S :=
    ⟨rfl, fun y hy _ => hy⟩
  have hbad : false = true := (h ht).2 false trivial trivial
  cases hbad

/-- Same-domain arrow deletion is already enough to refute BPAL monotonicity. -/
theorem bpal_monotonicity_fails :
    ∃ N M : Model Bool Unit Unit, ArrowSubmodel N M ∧
      ¬ ArrowSubmodel (N.update (.box () (.atom ()))) (M.update (.box () (.atom ()))) := by
  let M := Countermodels.twoWorlds
  let N := M.update (.atom ())
  refine ⟨N, M, update_arrowSubmodel M (.atom ()), ?_⟩
  intro h
  have hn : (N.update (.box () (.atom ()))).rel () true true :=
    ⟨⟨trivial, rfl⟩, fun y hy => hy.2⟩
  have hbad : false = true := (h.rel_le () true true hn).2 false trivial
  cases hbad

end Examples
end PropertiesOfPALAndBPALOperators
