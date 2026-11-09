import PropertiesOfPALAndBPALOperators.Propositional
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Finite modal types and syntactic preservation

This development proves the modal preservation theorem used in Theorem 19.
Finite signatures and bounded modal depth give finitely many semantic types.
Their universal characteristic formulas describe exactly the refinement
preorder. A disjunction of the characteristics of the satisfying types is the
required universal formula.
-/

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity

namespace ModalTypes

noncomputable section

attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

variable {Atom Agent : Type}

def Ty (P : Finset Atom) (I : Finset Agent) : Nat → Type
  | 0 => P → Bool
  | n + 1 => (P → Bool) × (I → Finset (Ty P I n))

instance tyDecidableEq (P : Finset Atom) (I : Finset Agent) (n : Nat) :
    DecidableEq (Ty P I n) := Classical.decEq _

instance tyFintype (P : Finset Atom) (I : Finset Agent) (n : Nat) :
    Fintype (Ty P I n) := by
  induction n with
  | zero => unfold Ty; infer_instance
  | succ n ih => unfold Ty; infer_instance

def atoms (P : Finset Atom) (I : Finset Agent) : (n : Nat) → Ty P I n → P → Bool
  | 0, t => t
  | _ + 1, t => t.1

def ofModel {World : Type} (P : Finset Atom) (I : Finset Agent)
    (M : Model World Atom Agent) : (n : Nat) → World → Ty P I n
  | 0, x => fun p => decide (M.val p.val x)
  | n + 1, x =>
      (fun p => decide (M.val p.val x), fun i =>
        Finset.univ.filter (fun t => ∃ y, M.rel i.val x y ∧ ofModel P I M n y = t))

theorem atoms_ofModel {World : Type} (P : Finset Atom) (I : Finset Agent)
    (M : Model World Atom Agent) (n : Nat) (x : World) (p : P) :
    atoms P I n (ofModel P I M n x) p = decide (M.val p.val x) := by
  cases n <;> rfl

@[simp] theorem mem_ofModel_next {World : Type} (P : Finset Atom) (I : Finset Agent)
    (M : Model World Atom Agent) (n : Nat) (x : World) (i : I) (t : Ty P I n) :
    t ∈ (ofModel P I M (n+1) x).2 i ↔
      ∃ y, M.rel i.val x y ∧ ofModel P I M n y = t := by
  simp [ofModel]

def Below (P : Finset Atom) (I : Finset Agent) : (n : Nat) → Ty P I n → Ty P I n → Prop
  | 0, t, s => t = s
  | n+1, t, s => t.1 = s.1 ∧
      ∀ i, ∀ q ∈ s.2 i, ∃ r ∈ t.2 i, Below P I n r q

theorem Below.refl (P : Finset Atom) (I : Finset Agent) (n : Nat) (t : Ty P I n) :
    Below P I n t t := by
  induction n with
  | zero => rfl
  | succ n ih => exact ⟨rfl,fun i q hq => ⟨q,hq,ih q⟩⟩

theorem Below.atoms_eq {P : Finset Atom} {I : Finset Agent} {n : Nat}
    {t s : Ty P I n} (h : Below P I n t s) : atoms P I n t = atoms P I n s := by
  cases n with
  | zero => exact h
  | succ n => exact h.1

def Eval (P : Finset Atom) (I : Finset Agent) (n : Nat) (t : Ty P I n) :
    Formula Atom Agent → Prop
  | .atom p => ∃ hp : p ∈ P, atoms P I n t ⟨p,hp⟩ = true
  | .neg φ => ¬ Eval P I n t φ
  | .conj φ ψ => Eval P I n t φ ∧ Eval P I n t ψ
  | .box i φ => match n, t with
      | 0, _ => True
      | k+1, t => ∀ hi : i ∈ I, ∀ s ∈ t.2 ⟨i,hi⟩, Eval P I k s φ

theorem eval_ofModel_iff {World : Type} (P : Finset Atom) (I : Finset Agent)
    (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (hp : φ.atoms ⊆ P) (hi : φ.agents ⊆ I) (n : Nat)
    (hd : φ.modalDepth ≤ n) (x : World) :
    Eval P I n (ofModel P I M n x) φ ↔ M.Satisfies x φ := by
  induction φ generalizing n x with
  | atom p =>
    have hpp : p ∈ P := hp (by simp [Formula.atoms])
    simp only [Eval, atoms_ofModel, decide_eq_true_eq, Model.satisfies_atom]
    exact ⟨fun ⟨_,h⟩ => h, fun h => ⟨hpp,h⟩⟩
  | neg φ ihφ => exact not_congr (ihφ hp hi n hd x)
  | conj φ ψ ihφ ihψ =>
    have hpφ : φ.atoms ⊆ P := fun p h => hp (by simp [Formula.atoms,h])
    have hpψ : ψ.atoms ⊆ P := fun p h => hp (by simp [Formula.atoms,h])
    have hiφ : φ.agents ⊆ I := fun i h => hi (by simp [Formula.agents,h])
    have hiψ : ψ.agents ⊆ I := fun i h => hi (by simp [Formula.agents,h])
    exact and_congr
      (ihφ hpφ hiφ n (le_trans (Nat.le_max_left _ _) hd) x)
      (ihψ hpψ hiψ n (le_trans (Nat.le_max_right _ _) hd) x)
  | box i φ ihφ =>
    have hii : i ∈ I := hi (by simp [Formula.agents])
    have hiφ : φ.agents ⊆ I := fun j h => hi (by simp [Formula.agents,h])
    cases n with
    | zero => simp [Formula.modalDepth] at hd
    | succ n =>
      have hdφ : φ.modalDepth ≤ n := Nat.succ_le_succ_iff.mp hd
      change (∀ h : i ∈ I, ∀ s ∈ (ofModel P I M (n+1) x).2 ⟨i,h⟩,
        Eval P I n s φ) ↔ ∀ y, M.rel i x y → M.Satisfies y φ
      constructor
      · intro h y hxy
        exact (ihφ hp hiφ n hdφ y).mp
          (h hii _ ((mem_ofModel_next P I M n x ⟨i,hii⟩ _).mpr ⟨y,hxy,rfl⟩))
      · intro h hh s hs
        obtain ⟨y,hxy,rfl⟩ := (mem_ofModel_next P I M n x ⟨i,hh⟩ s).mp hs
        exact (ihφ hp hiφ n hdφ y).mpr (h y hxy)

/-- One fixed model contains canonical realizations of all finite-depth types.
Edges decrease depth by one, so no recursive family of model carriers is needed. -/
def canonical (P : Finset Atom) (I : Finset Agent) :
    Model (Σ n, Ty P I n) Atom Agent where
  val p x := ∃ hp : p ∈ P, atoms P I x.1 x.2 ⟨p,hp⟩ = true
  rel i x y := match x with
    | ⟨0,_⟩ => False
    | ⟨n+1,t⟩ => ∃ s, y = ⟨n,s⟩ ∧ ∃ hi : i ∈ I, s ∈ t.2 ⟨i,hi⟩

theorem canonical_satisfies (P : Finset Atom) (I : Finset Agent)
    (n : Nat) (t : Ty P I n) (φ : Formula Atom Agent) :
    (canonical P I).Satisfies ⟨n,t⟩ φ ↔ Eval P I n t φ := by
  induction φ generalizing n with
  | atom p => rfl
  | neg φ ih => exact not_congr (ih n t)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ n t) (ihψ n t)
  | box i φ ih =>
    cases n with
    | zero =>
      change (∀ y, False → (canonical P I).Satisfies y φ) ↔ True
      simp
    | succ n =>
      constructor
      · intro h hi s hs
        exact (ih n s).mp (h ⟨n,s⟩ ⟨s,rfl,hi,hs⟩)
      · intro h y hy
        obtain ⟨s,rfl,hi,hs⟩ := hy
        exact (ih n s).mpr (h hi s hs)

def Related (P : Finset Atom) (I : Finset Agent)
    (x y : Σ n, Ty P I n) : Prop :=
  ∃ n t s, x = ⟨n,t⟩ ∧ y = ⟨n,s⟩ ∧ Below P I n t s

theorem canonical_refines (P : Finset Atom) (I : Finset Agent) :
    Refines (canonical P I) (canonical P I) (Related P I) := by
  constructor
  · intro x y hxy p
    obtain ⟨n,t,s,rfl,rfl,hts⟩ := hxy
    change (∃ hp : p ∈ P, atoms P I n t ⟨p,hp⟩ = true) ↔
      ∃ hp : p ∈ P, atoms P I n s ⟨p,hp⟩ = true
    rw [hts.atoms_eq]
  · intro x y hxy i z hyz
    obtain ⟨n,t,s,rfl,rfl,hts⟩ := hxy
    cases n with
    | zero => exact False.elim hyz
    | succ n =>
      obtain ⟨q,rfl,hi,hq⟩ := hyz
      obtain ⟨r,hr,hrq⟩ := hts.2 ⟨i,hi⟩ q hq
      exact ⟨⟨n,r⟩, ⟨r,rfl,hi,hr⟩, n,r,q,rfl,rfl,hrq⟩

theorem eval_preserved {P : Finset Atom} {I : Finset Agent} {n : Nat}
    {t s : Ty P I n} (hts : Below P I n t s) {φ : Formula Atom Agent}
    (hφ : RefinementPreserved.{0} φ) : Eval P I n t φ → Eval P I n s φ := by
  intro ht
  exact (canonical_satisfies P I n s φ).mp
    (hφ (canonical P I) (canonical P I) (Related P I) (canonical_refines P I)
      ⟨n,t⟩ ⟨n,s⟩ ⟨n,t,s,rfl,rfl,hts⟩ ((canonical_satisfies P I n t φ).mpr ht))

variable [Inhabited Atom]

def conjunction : List (Formula Atom Agent) → Formula Atom Agent
  | [] => Formula.or (.atom default) (.neg (.atom default))
  | φ :: rest => .conj φ (conjunction rest)

def disjunction : List (Formula Atom Agent) → Formula Atom Agent
  | [] => .conj (.atom default) (.neg (.atom default))
  | φ :: rest => Formula.or φ (disjunction rest)

theorem conjunction_universal (xs : List (Formula Atom Agent))
    (h : ∀ φ ∈ xs, Universal φ) : Universal (conjunction xs) := by
  induction xs with
  | nil => exact .disj (.atom _) (.negAtom _)
  | cons φ xs ih =>
    exact .conj (h φ (by simp)) (ih (fun ψ hψ => h ψ (by simp [hψ])))

theorem disjunction_universal (xs : List (Formula Atom Agent))
    (h : ∀ φ ∈ xs, Universal φ) : Universal (disjunction xs) := by
  induction xs with
  | nil => exact .conj (.atom _) (.negAtom _)
  | cons φ xs ih =>
    exact .disj (h φ (by simp)) (ih (fun ψ hψ => h ψ (by simp [hψ])))

theorem satisfies_conjunction {World : Type} (M : Model World Atom Agent)
    (x : World) (xs : List (Formula Atom Agent)) :
    M.Satisfies x (conjunction xs) ↔ ∀ φ ∈ xs, M.Satisfies x φ := by
  induction xs with
  | nil => simp [conjunction,Model.satisfies_or,Model.Satisfies,Classical.em]
  | cons φ xs ih => simp [conjunction,Model.satisfies_and,ih]

theorem satisfies_disjunction {World : Type} (M : Model World Atom Agent)
    (x : World) (xs : List (Formula Atom Agent)) :
    M.Satisfies x (disjunction xs) ↔ ∃ φ ∈ xs, M.Satisfies x φ := by
  induction xs with
  | nil => simp [disjunction,Model.Satisfies]
  | cons φ xs ih => simp [disjunction,Model.satisfies_or,ih]

def literal {P : Finset Atom} (a : P → Bool) (p : P) : Formula Atom Agent :=
  if a p = true then .atom p.val else .neg (.atom p.val)

def atomic {P : Finset Atom} (a : P → Bool) : Formula Atom Agent :=
  conjunction ((Finset.univ : Finset P).toList.map (literal a))

omit [Inhabited Atom] in
theorem literal_universal {P : Finset Atom} (a : P → Bool) (p : P) :
    Universal (literal (Agent := Agent) a p) := by
  unfold literal
  split
  · exact .atom _
  · exact .negAtom _

theorem atomic_universal {P : Finset Atom} (a : P → Bool) :
    Universal (atomic (Agent := Agent) a) := by
  apply conjunction_universal
  intro φ hφ
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hφ
  exact literal_universal a p

omit [Inhabited Atom] in
theorem literal_satisfies {World : Type} {P : Finset Atom} (a : P → Bool)
    (p : P) (M : Model World Atom Agent) (x : World) :
    M.Satisfies x (literal a p) ↔ a p = decide (M.val p.val x) := by
  cases ha : a p <;> simp [literal,ha,Model.Satisfies]

theorem atomic_satisfies {World : Type} {P : Finset Atom} (a : P → Bool)
    (M : Model World Atom Agent) (x : World) :
    M.Satisfies x (atomic a) ↔ ∀ p, a p = decide (M.val p.val x) := by
  rw [atomic,satisfies_conjunction]
  constructor
  · intro h p
    exact (literal_satisfies a p M x).mp
      (h (literal a p) (List.mem_map.mpr ⟨p,Finset.mem_toList.mpr (Finset.mem_univ p),rfl⟩))
  · intro h φ hφ
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hφ
    exact (literal_satisfies a p M x).mpr (h p)

def characteristic (P : Finset Atom) (I : Finset Agent) :
    (n : Nat) → Ty P I n → Formula Atom Agent
  | 0, t => atomic t
  | n+1, t => .conj (atomic t.1)
      (conjunction ((Finset.univ : Finset I).toList.map (fun i =>
        .box i.val (disjunction ((t.2 i).toList.map (characteristic P I n))))))

theorem characteristic_universal (P : Finset Atom) (I : Finset Agent)
    (n : Nat) (t : Ty P I n) : Universal (characteristic P I n t) := by
  induction n with
  | zero => exact atomic_universal t
  | succ n ih =>
    apply Universal.conj (atomic_universal t.1)
    apply conjunction_universal
    intro φ hφ
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hφ
    apply Universal.box
    apply disjunction_universal
    intro ψ hψ
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hψ
    exact ih s

theorem characteristic_succ_satisfies {World : Type} (P : Finset Atom)
    (I : Finset Agent) (n : Nat) (t : Ty P I (n+1))
    (M : Model World Atom Agent) (x : World) :
    M.Satisfies x (characteristic P I (n+1) t) ↔
      (∀ p, t.1 p = decide (M.val p.val x)) ∧
      ∀ i : I, ∀ y, M.rel i.val x y →
        ∃ s ∈ t.2 i, M.Satisfies y (characteristic P I n s) := by
  change (M.Satisfies x (atomic t.1) ∧ M.Satisfies x (conjunction _)) ↔ _
  rw [atomic_satisfies,satisfies_conjunction]
  apply and_congr Iff.rfl
  constructor
  · intro h i y hxy
    have hb := h (.box i.val (disjunction ((t.2 i).toList.map (characteristic P I n))))
      (List.mem_map.mpr ⟨i,Finset.mem_toList.mpr (Finset.mem_univ i),rfl⟩)
    obtain ⟨φ,hφ,hp⟩ := (satisfies_disjunction M y _).mp (hb y hxy)
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hφ
    exact ⟨s,Finset.mem_toList.mp hs,hp⟩
  · intro h φ hφ
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hφ
    intro y hxy
    obtain ⟨s,hs,hp⟩ := h i y hxy
    exact (satisfies_disjunction M y _).mpr
      ⟨characteristic P I n s,List.mem_map.mpr ⟨s,Finset.mem_toList.mpr hs,rfl⟩,hp⟩

theorem characteristic_satisfies {World : Type} (P : Finset Atom) (I : Finset Agent)
    (n : Nat) (t : Ty P I n) (M : Model World Atom Agent) (x : World) :
    M.Satisfies x (characteristic P I n t) ↔ Below P I n t (ofModel P I M n x) := by
  induction n generalizing x with
  | zero =>
    change M.Satisfies x (atomic t) ↔ t = ofModel P I M 0 x
    rw [atomic_satisfies]
    exact ⟨fun h => funext h,fun h p => congrFun h p⟩
  | succ n ih =>
    rw [characteristic_succ_satisfies]
    change _ ↔ t.1 = (ofModel P I M (n+1) x).1 ∧
      ∀ i, ∀ q ∈ (ofModel P I M (n+1) x).2 i, ∃ r ∈ t.2 i, Below P I n r q
    constructor
    · rintro ⟨ha,hs⟩
      refine ⟨funext ha,?_⟩
      intro i q hq
      obtain ⟨y,hxy,rfl⟩ := (mem_ofModel_next P I M n x i q).mp hq
      obtain ⟨r,hr,hc⟩ := hs i y hxy
      exact ⟨r,hr,(ih r y).mp hc⟩
    · rintro ⟨ha,hs⟩
      refine ⟨fun p => congrFun ha p,?_⟩
      intro i y hxy
      obtain ⟨r,hr,hbelow⟩ := hs i (ofModel P I M n y)
        ((mem_ofModel_next P I M n x i _).mpr ⟨y,hxy,rfl⟩)
      exact ⟨r,hr,(ih r y).mpr hbelow⟩

theorem universalEquivalent_of_refinementPreserved (φ : Formula Atom Agent)
    (hφ : RefinementPreserved.{0} φ) : UniversalEquivalent.{0} φ := by
  let P := φ.atoms
  let I := φ.agents
  let d := φ.modalDepth
  let good : Finset (Ty P I d) := Finset.univ.filter (fun t => Eval P I d t φ)
  let ψ := disjunction (good.toList.map (characteristic P I d))
  refine ⟨ψ,?_,?_⟩
  · apply disjunction_universal
    intro χ hχ
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hχ
    exact characteristic_universal P I d t
  · intro World M x
    change M.Satisfies x φ ↔ M.Satisfies x (disjunction _)
    rw [satisfies_disjunction]
    constructor
    · intro hx
      let t := ofModel P I M d x
      have ht : t ∈ good := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,
          (eval_ofModel_iff P I M φ (fun _ h => h) (fun _ h => h) d le_rfl x).mpr hx⟩
      refine ⟨characteristic P I d t, List.mem_map.mpr ⟨t,Finset.mem_toList.mpr ht,rfl⟩,?_⟩
      exact (characteristic_satisfies P I d t M x).mpr (Below.refl P I d t)
    · rintro ⟨χ,hχ,hx⟩
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hχ
      have heval : Eval P I d t φ :=
        (Finset.mem_filter.mp (Finset.mem_toList.mp ht)).2
      have hbelow := (characteristic_satisfies P I d t M x).mp hx
      exact (eval_ofModel_iff P I M φ (fun _ h => h) (fun _ h => h) d le_rfl x).mp
        (eval_preserved hbelow hφ heval)

end

end ModalTypes

/-- The modal submodel-preservation theorem, proved here by finite modal types.
Worlds, atoms and agents range over `Type`; models need not be finite. -/
theorem submodelPreserved_iff_universalEquivalent {Atom Agent : Type} [Inhabited Atom]
    (φ : Formula Atom Agent) :
    SubmodelPreserved.{0} φ ↔ UniversalEquivalent.{0} φ := by
  constructor
  · intro h
    exact ModalTypes.universalEquivalent_of_refinementPreserved φ
      (SubmodelPreserved.refinementPreserved h)
  · intro h
    exact DeletionMonotone.submodelPreserved (UniversalEquivalent.deletionMonotone h)

theorem deletionMonotone_iff_universalEquivalent {Atom Agent : Type} [Inhabited Atom]
    (φ : Formula Atom Agent) :
    DeletionMonotone.{0} φ ↔ UniversalEquivalent.{0} φ :=
  (deletionMonotone_iff_submodelPreserved φ).trans
    (submodelPreserved_iff_universalEquivalent φ)

theorem refinementPreserved_iff_universalEquivalent {Atom Agent : Type} [Inhabited Atom]
    (φ : Formula Atom Agent) :
    RefinementPreserved.{0} φ ↔ UniversalEquivalent.{0} φ :=
  (submodelPreserved_iff_refinementPreserved φ).symm.trans
    (submodelPreserved_iff_universalEquivalent φ)

end PropertiesOfPALAndBPALOperators
