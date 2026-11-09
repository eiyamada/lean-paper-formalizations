import PropertiesOfPublicAnnouncementsAsOperators.Algebra

/-! Explicit two-world S5 countermodels for the algebraic assertions. -/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity

namespace Countermodels

def twoWorlds : Model Bool Unit Unit where
  rel _ _ _ := True
  val _ x := x = true

theorem twoWorlds_reflexive : ∀ i x, twoWorlds.rel i x x := fun _ _ => trivial

theorem twoWorlds_isS5 : IsS5 twoWorlds := by
  intro i
  refine ⟨fun _ => trivial, ?_, ?_⟩
  · intro x y z hxy hyz; trivial
  · intro x y z hxy hxz; trivial

/-- The inclusion between the union of fixed-point sets and the fixed points
of a disjunction in Theorem 23(2) is strict, already on two S5 worlds. -/
theorem pal_fixed_disjunction_strict :
    palUpdate twoWorlds (.neg (.conj (.neg (.atom ())) (.neg (.neg (.atom ())))))
        Set.univ = Set.univ ∧
    palUpdate twoWorlds (.atom ()) Set.univ ≠ Set.univ ∧
    palUpdate twoWorlds (.neg (.atom ())) Set.univ ≠ Set.univ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pal_fixed_iff]
    intro x _
    change ¬ (¬ (x = true) ∧ ¬ ¬ (x = true))
    tauto
  · intro h
    have ht := (pal_fixed_iff twoWorlds (.atom ()) Set.univ).mp h false (by trivial)
    change false = true at ht
    cases ht
  · intro h
    have ht := (pal_fixed_iff twoWorlds (.neg (.atom ())) Set.univ).mp h true (by trivial)
    exact ht rfl

theorem bpal_fixed_disjunction_strict :
    bpalUpdate twoWorlds (.neg (.conj (.neg (.atom ())) (.neg (.neg (.atom ())))))
        twoWorlds.rel = twoWorlds.rel ∧
    bpalUpdate twoWorlds (.atom ()) twoWorlds.rel ≠ twoWorlds.rel ∧
    bpalUpdate twoWorlds (.neg (.atom ())) twoWorlds.rel ≠ twoWorlds.rel := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bpal_fixed_iff]
    intro i x y _
    change ¬ (¬ (y = true) ∧ ¬ ¬ (y = true))
    tauto
  · intro h
    have ht := (bpal_fixed_iff twoWorlds (.atom ()) twoWorlds.rel).mp h () true false trivial
    change false = true at ht
    cases ht
  · intro h
    have ht := (bpal_fixed_iff twoWorlds (.neg (.atom ())) twoWorlds.rel).mp h () true true trivial
    exact ht rfl

/-- Even universal formulas need not commute. -/
theorem pal_atom_box_not_commute :
    palUpdate twoWorlds (.box () (.atom ())) (palUpdate twoWorlds (.atom ()) Set.univ) ≠
      palUpdate twoWorlds (.atom ()) (palUpdate twoWorlds (.box () (.atom ())) Set.univ) := by
  intro h
  have he := Set.ext_iff.mp h true
  simp [mem_palUpdate, palUpdate, PAL.Satisfies, twoWorlds, Bool.forall_bool] at he
  exact he trivial trivial

theorem bpal_atom_box_not_commute :
    bpalUpdate twoWorlds (.box () (.atom ())) (bpalUpdate twoWorlds (.atom ()) twoWorlds.rel) ≠
      bpalUpdate twoWorlds (.atom ()) (bpalUpdate twoWorlds (.box () (.atom ())) twoWorlds.rel) := by
  intro h
  have he := congrFun (congrFun (congrFun h ()) true) true
  simp [bpalUpdate, BPAL.Satisfies, twoWorlds, Bool.forall_bool] at he

end Countermodels
end PropertiesOfPublicAnnouncementsAsOperators
