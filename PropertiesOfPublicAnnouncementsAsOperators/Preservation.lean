import ClassificationSigmaValidity.Locality
import ClassificationSigmaValidity.Expressivity

/-!
# Preservation and monotonicity of announcement operators

The arrow order below is the BPAL order: the valuation and the world type are
unchanged and accessibility arrows may be deleted. Induced submodels, used for
PAL, are represented by `Model.restrict` on a subtype. The two orders must not
be identified.
-/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity

universe u u' v w

variable {World : Type u} {World' : Type u'} {Atom : Type v} {Agent : Type w}

/-- Same-domain arrow inclusion, with exactly the same valuation. -/
structure ArrowSubmodel (N M : Model World Atom Agent) : Prop where
  val_eq : N.val = M.val
  rel_le : ∀ i x y, N.rel i x y → M.rel i x y

theorem ArrowSubmodel.refl (M : Model World Atom Agent) : ArrowSubmodel M M :=
  ⟨rfl, fun _ _ _ h => h⟩

theorem ArrowSubmodel.trans {L M N : Model World Atom Agent}
    (hLM : ArrowSubmodel L M) (hMN : ArrowSubmodel M N) : ArrowSubmodel L N :=
  ⟨hLM.val_eq.trans hMN.val_eq, fun i x y h => hMN.rel_le i x y (hLM.rel_le i x y h)⟩

theorem ArrowSubmodel.antisymm {M N : Model World Atom Agent}
    (hMN : ArrowSubmodel M N) (hNM : ArrowSubmodel N M) : M = N := by
  apply Model.ext'
  · exact fun i x y => ⟨hMN.rel_le i x y, hNM.rel_le i x y⟩
  · intro p x
    rw [hMN.val_eq]

/-- Announcements are deflationary in the BPAL order. -/
theorem update_arrowSubmodel (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    ArrowSubmodel (M.update φ) M := ⟨rfl, fun _ _ _ h => h.1⟩

/-- The universal modal fragment, with negation only on atoms. -/
inductive Universal : Formula Atom Agent → Prop
  | atom (p) : Universal (.atom p)
  | negAtom (p) : Universal (.neg (.atom p))
  | conj {φ ψ} : Universal φ → Universal ψ → Universal (.conj φ ψ)
  | disj {φ ψ} : Universal φ → Universal ψ → Universal (Formula.or φ ψ)
  | box (i) {φ} : Universal φ → Universal (.box i φ)

/-- The existential modal fragment. -/
inductive Existential : Formula Atom Agent → Prop
  | atom (p) : Existential (.atom p)
  | negAtom (p) : Existential (.neg (.atom p))
  | conj {φ ψ} : Existential φ → Existential ψ → Existential (.conj φ ψ)
  | disj {φ ψ} : Existential φ → Existential ψ → Existential (Formula.or φ ψ)
  | dia (i) {φ} : Existential φ → Existential (Formula.dia i φ)

/-- Atoms and the back condition of Definition 17. A related pair witnesses
the nonemptiness required for a pointed refinement. -/
structure Refines (M : Model World Atom Agent) (N : Model World' Atom Agent)
    (Z : World → World' → Prop) : Prop where
  atoms : ∀ x y, Z x y → ∀ p, M.val p x ↔ N.val p y
  back : ∀ x y, Z x y → ∀ i z, N.rel i y z → ∃ t, M.rel i x t ∧ Z t z

/-- Atoms and the forth condition of Definition 17. -/
structure Simulates (M : Model World Atom Agent) (N : Model World' Atom Agent)
    (Z : World → World' → Prop) : Prop where
  atoms : ∀ x y, Z x y → ∀ p, M.val p x ↔ N.val p y
  forth : ∀ x y, Z x y → ∀ i t, M.rel i x t → ∃ z, N.rel i y z ∧ Z t z

/-- A bisimulation has both forth and back. -/
structure Bisimulates (M : Model World Atom Agent) (N : Model World' Atom Agent)
    (Z : World → World' → Prop) : Prop where
  refinement : Refines M N Z
  simulation : Simulates M N Z

theorem simulates_iff_inverse_refines (M : Model World Atom Agent)
    (N : Model World' Atom Agent) (Z : World → World' → Prop) :
    Simulates M N Z ↔ Refines N M (fun y x => Z x y) := by
  constructor
  · intro h
    exact ⟨fun y x hxy p => (h.atoms x y hxy p).symm,
      fun y x hxy i t hxt => h.forth x y hxy i t hxt⟩
  · intro h
    exact ⟨fun x y hxy p => (h.atoms y x hxy p).symm,
      fun x y hxy i t hxt => h.back y x hxy i t hxt⟩

theorem Universal.preserved_refinement {φ : Formula Atom Agent} (hφ : Universal φ)
    {M : Model World Atom Agent} {N : Model World' Atom Agent}
    {Z : World → World' → Prop} (hZ : Refines M N Z)
    {x y} (hxy : Z x y) : M.Satisfies x φ → N.Satisfies y φ := by
  induction hφ generalizing x y with
  | atom p => exact (hZ.atoms x y hxy p).mp
  | negAtom p => exact fun h hn => h ((hZ.atoms x y hxy p).mpr hn)
  | conj hφ hψ ihφ ihψ => exact fun h => ⟨ihφ hxy h.1, ihψ hxy h.2⟩
  | disj hφ hψ ihφ ihψ =>
    simpa only [Model.satisfies_or] using Or.imp (ihφ hxy) (ihψ hxy)
  | box i hφ ih =>
    intro h z hyz
    obtain ⟨t, hxt, htz⟩ := hZ.back x y hxy i z hyz
    exact ih htz (h t hxt)

theorem Existential.preserved_simulation {φ : Formula Atom Agent} (hφ : Existential φ)
    {M : Model World Atom Agent} {N : Model World' Atom Agent}
    {Z : World → World' → Prop} (hZ : Simulates M N Z)
    {x y} (hxy : Z x y) : M.Satisfies x φ → N.Satisfies y φ := by
  induction hφ generalizing x y with
  | atom p => exact (hZ.atoms x y hxy p).mp
  | negAtom p => exact fun h hn => h ((hZ.atoms x y hxy p).mpr hn)
  | conj hφ hψ ihφ ihψ => exact fun h => ⟨ihφ hxy h.1, ihψ hxy h.2⟩
  | disj hφ hψ ihφ ihψ =>
    simpa only [Model.satisfies_or] using Or.imp (ihφ hxy) (ihψ hxy)
  | dia i hφ ih =>
    simp only [Model.satisfies_dia]
    rintro ⟨t, hxt, ht⟩
    obtain ⟨z, hyz, htz⟩ := hZ.forth x y hxy i t hxt
    exact ⟨z, hyz, ih htz ht⟩

theorem Bisimulates.satisfies_iff {M : Model World Atom Agent}
    {N : Model World' Atom Agent} {Z : World → World' → Prop}
    (hZ : Bisimulates M N Z) {x y} (hxy : Z x y) (φ : Formula Atom Agent) :
    M.Satisfies x φ ↔ N.Satisfies y φ := by
  induction φ generalizing x y with
  | atom p => exact hZ.refinement.atoms x y hxy p
  | neg φ ih => exact not_congr (ih hxy)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ hxy) (ihψ hxy)
  | box i φ ih =>
    constructor
    · intro h z hyz
      obtain ⟨t, hxt, htz⟩ := hZ.refinement.back x y hxy i z hyz
      exact (ih htz).mp (h t hxt)
    · intro h t hxt
      obtain ⟨z, hyz, htz⟩ := hZ.simulation.forth x y hxy i t hxt
      exact (ih htz).mpr (h z hyz)

theorem ArrowSubmodel.refines {M N : Model World Atom Agent} (h : ArrowSubmodel N M) :
    Refines M N Eq := by
  constructor
  · intro x y hxy p
    subst y
    rw [h.val_eq]
  · intro x y hxy i z hyz
    subst y
    exact ⟨z, h.rel_le i x z hyz, rfl⟩

theorem ArrowSubmodel.simulates {M N : Model World Atom Agent} (h : ArrowSubmodel N M) :
    Simulates N M Eq := by
  constructor
  · intro x y hxy p
    subst y
    rw [h.val_eq]
  · intro x y hxy i z hxz
    subst y
    exact ⟨z, h.rel_le i x z hxz, rfl⟩

theorem Universal.preserved_arrowSubmodel {φ : Formula Atom Agent} (hφ : Universal φ)
    {M N : Model World Atom Agent} (hNM : ArrowSubmodel N M) {x} :
    M.Satisfies x φ → N.Satisfies x φ :=
  hφ.preserved_refinement hNM.refines rfl

theorem Existential.preserved_arrowExtension {φ : Formula Atom Agent} (hφ : Existential φ)
    {M N : Model World Atom Agent} (hNM : ArrowSubmodel N M) {x} :
    N.Satisfies x φ → M.Satisfies x φ :=
  hφ.preserved_simulation hNM.simulates rfl

theorem restrict_refines (M : Model World Atom Agent) (S : Set World) :
    Refines M (M.restrict S) (fun x y => x = y.val) := by
  constructor
  · intro x y hxy p
    subst x
    rfl
  · intro x y hxy i z hyz
    subst x
    exact ⟨z.val, hyz, rfl⟩

theorem restrict_simulates (M : Model World Atom Agent) (S : Set World) :
    Simulates (M.restrict S) M (fun x y => x.val = y) := by
  constructor
  · intro x y hxy p
    subst y
    rfl
  · intro x y hxy i z hxz
    subst y
    exact ⟨z.val, hxz, rfl⟩

theorem Universal.preserved_submodel {φ : Formula Atom Agent} (hφ : Universal φ)
    (M : Model World Atom Agent) (S : Set World) (x : S) :
    M.Satisfies x.val φ → (M.restrict S).Satisfies x φ :=
  hφ.preserved_refinement (restrict_refines M S) rfl

theorem Existential.preserved_extension {φ : Formula Atom Agent} (hφ : Existential φ)
    (M : Model World Atom Agent) (S : Set World) (x : S) :
    (M.restrict S).Satisfies x φ → M.Satisfies x.val φ :=
  hφ.preserved_simulation (restrict_simulates M S) rfl

/-- Deleting arrows never destroys truth. -/
def DeletionMonotone (φ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M N : Model World Atom Agent), ArrowSubmodel N M →
    ∀ x, M.Satisfies x φ → N.Satisfies x φ

/-- Adding arrows never destroys truth. -/
def DeletionAntimonotone (φ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M N : Model World Atom Agent), ArrowSubmodel N M →
    ∀ x, N.Satisfies x φ → M.Satisfies x φ

theorem Universal.deletionMonotone {φ : Formula Atom Agent} (hφ : Universal φ) :
    DeletionMonotone.{u} φ := fun _ _ h _ => hφ.preserved_arrowSubmodel h

theorem Existential.deletionAntimonotone {φ : Formula Atom Agent} (hφ : Existential φ) :
    DeletionAntimonotone.{u} φ := fun _ _ h _ => hφ.preserved_arrowExtension h

theorem deletionMonotone_neg_iff (φ : Formula Atom Agent) :
    DeletionMonotone.{u} (.neg φ) ↔ DeletionAntimonotone.{u} φ := by
  classical
  simp only [DeletionMonotone, DeletionAntimonotone, Model.satisfies_neg]
  constructor
  · intro h World M N hNM x hn
    by_contra hm
    exact h M N hNM x hm hn
  · intro h World M N hNM x hm hn
    exact hm (h M N hNM x hn)

theorem deletionAntimonotone_neg_iff (φ : Formula Atom Agent) :
    DeletionAntimonotone.{u} (.neg φ) ↔ DeletionMonotone.{u} φ := by
  classical
  simp only [DeletionMonotone, DeletionAntimonotone, Model.satisfies_neg]
  constructor
  · intro h World M N hNM x hm
    by_contra hn
    exact h M N hNM x hn hm
  · intro h World M N hNM x hn hm
    exact hn (h M N hNM x hm)

/-- Monotonicity of a BPAL operator in the arrow order. -/
def BPALOperatorMonotone (φ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M N : Model World Atom Agent), ArrowSubmodel N M →
    ArrowSubmodel (N.update φ) (M.update φ)

theorem DeletionAntimonotone.operatorMonotone {φ : Formula Atom Agent}
    (hφ : DeletionAntimonotone.{u} φ) : BPALOperatorMonotone.{u} φ := by
  intro World M N hNM
  exact ⟨hNM.val_eq, fun i x y h => ⟨hNM.rel_le i x y h.1, hφ M N hNM y h.2⟩⟩

theorem Existential.operatorMonotone {φ : Formula Atom Agent} (hφ : Existential φ) :
    BPALOperatorMonotone.{u} φ :=
  DeletionAntimonotone.operatorMonotone hφ.deletionAntimonotone

theorem Universal.neg_operatorMonotone {φ : Formula Atom Agent} (hφ : Universal φ) :
    BPALOperatorMonotone.{u} (.neg φ) :=
  DeletionAntimonotone.operatorMonotone
    ((deletionAntimonotone_neg_iff φ).mpr hφ.deletionMonotone)

/-- A fresh predecessor makes truth at an arbitrary old world visible as
survival of an incoming arrow. No old world can reach the new predecessor. -/
def withPredecessor (M : Model World Atom Agent) (j : Agent) (root : World) :
    Model (Option World) Atom Agent where
  rel i x y := match x, y with
    | some x, some y => M.rel i x y
    | none, some y => i = j ∧ y = root
    | _, none => False
  val p x := match x with
    | some x => M.val p x
    | none => False

theorem withPredecessor_satisfies (M : Model World Atom Agent) (j : Agent)
    (root x : World) (φ : Formula Atom Agent) :
    (withPredecessor M j root).Satisfies (some x) φ ↔ M.Satisfies x φ := by
  induction φ generalizing x with
  | atom p => rfl
  | neg φ ih => exact not_congr (ih x)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ x) (ihψ x)
  | box i φ ih =>
    constructor
    · intro h y hxy
      exact (ih y).mp (h (some y) hxy)
    · intro h y hxy
      cases y with
      | none => exact False.elim hxy
      | some y => exact (ih y).mpr (h y hxy)

theorem ArrowSubmodel.withPredecessor {M N : Model World Atom Agent}
    (hNM : ArrowSubmodel N M) (j : Agent) (root : World) :
    ArrowSubmodel (withPredecessor N j root) (withPredecessor M j root) := by
  constructor
  · funext p x
    cases x with
    | none => rfl
    | some x => exact congrFun (congrFun hNM.val_eq p) x
  · intro i x y hxy
    cases x <;> cases y
    · exact hxy
    · exact hxy
    · exact hxy
    · exact hNM.rel_le _ _ _ hxy

/-- The predecessor argument proves the difficult direction of operator
monotonicity without assuming that every world originally has an incoming arrow. -/
theorem operatorMonotone_iff_deletionAntimonotone [Nonempty Agent]
    (φ : Formula Atom Agent) :
    BPALOperatorMonotone.{u} φ ↔ DeletionAntimonotone.{u} φ := by
  constructor
  · intro h World M N hNM x hx
    obtain ⟨i⟩ := ‹Nonempty Agent›
    have hplus := h (withPredecessor M i x) (withPredecessor N i x)
      (hNM.withPredecessor i x)
    have hedge : ((withPredecessor N i x).update φ).rel i none (some x) :=
      ⟨⟨rfl, rfl⟩, (withPredecessor_satisfies N i x x φ).mpr hx⟩
    exact (withPredecessor_satisfies M i x x φ).mp
      (hplus.rel_le i none (some x) hedge).2
  · exact DeletionAntimonotone.operatorMonotone

theorem neg_operatorMonotone_iff_deletionMonotone [Nonempty Agent]
    (φ : Formula Atom Agent) :
    BPALOperatorMonotone.{u} (.neg φ) ↔ DeletionMonotone.{u} φ :=
  (operatorMonotone_iff_deletionAntimonotone (.neg φ)).trans
    (deletionAntimonotone_neg_iff φ)

/-- Cut only incoming arrows to worlds outside a chosen domain. -/
def targetCut (M : Model World Atom Agent) (S : Set World) : Model World Atom Agent where
  rel i x y := M.rel i x y ∧ S y
  val := M.val

theorem targetCut_arrowSubmodel (M : Model World Atom Agent) (S : Set World) :
    ArrowSubmodel (targetCut M S) M := ⟨rfl, fun _ _ _ h => h.1⟩

theorem targetCut_bisimulates_restrict (M : Model World Atom Agent) (S : Set World) :
    Bisimulates (targetCut M S) (M.restrict S) (fun x y => x = y.val) := by
  constructor
  · constructor
    · intro x y hxy p
      subst x
      rfl
    · intro x y hxy i z hyz
      subst x
      exact ⟨z.val, ⟨hyz, z.property⟩, rfl⟩
  · constructor
    · intro x y hxy p
      subst x
      rfl
    · intro x y hxy i z hxz
      subst x
      exact ⟨⟨z, hxz.2⟩, hxz.1, rfl⟩

theorem targetCut_satisfies_restrict (M : Model World Atom Agent) (S : Set World)
    (x : S) (φ : Formula Atom Agent) :
    (targetCut M S).Satisfies x.val φ ↔ (M.restrict S).Satisfies x φ :=
  (targetCut_bisimulates_restrict M S).satisfies_iff rfl φ

/-- Preservation by induced submodels (condition (2) of Theorem 19). -/
def SubmodelPreserved (φ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent) (S : Set World) (x : S),
    M.Satisfies x.val φ → (M.restrict S).Satisfies x φ

/-- Preservation by extensions of induced submodels. -/
def ExtensionPreserved (φ : Formula Atom Agent) : Prop :=
  ∀ {World : Type u} (M : Model World Atom Agent) (S : Set World) (x : S),
    (M.restrict S).Satisfies x φ → M.Satisfies x.val φ

theorem DeletionMonotone.submodelPreserved {φ : Formula Atom Agent}
    (hφ : DeletionMonotone.{u} φ) : SubmodelPreserved.{u} φ := by
  intro World M S x hx
  exact (targetCut_satisfies_restrict M S x φ).mp
    (hφ M (targetCut M S) (targetCut_arrowSubmodel M S) x.val hx)

theorem DeletionAntimonotone.extensionPreserved {φ : Formula Atom Agent}
    (hφ : DeletionAntimonotone.{u} φ) : ExtensionPreserved.{u} φ := by
  intro World M S x hx
  exact hφ M (targetCut M S) (targetCut_arrowSubmodel M S) x.val
    ((targetCut_satisfies_restrict M S x φ).mpr hx)

/-- A model bisimilar to `M`, containing a copy of the refinement of `M` as
an induced submodel. The right summand supplies every original successor;
the left summand carries the refinement relation. -/
def refinementCover (M : Model World Atom Agent) (N : Model World' Atom Agent)
    (Z : World → World' → Prop) : Model ((World × World') ⊕ World) Atom Agent where
  rel i x y := match x, y with
    | .inl (x, y), .inl (x', y') => M.rel i x x' ∧ N.rel i y y' ∧ Z x y ∧ Z x' y'
    | .inl (x, _), .inr x' => M.rel i x x'
    | .inr x, .inr x' => M.rel i x x'
    | .inr _, .inl _ => False
  val p x := M.val p (match x with | .inl xy => xy.1 | .inr x => x)

def refinementDomain (Z : World → World' → Prop) : Set ((World × World') ⊕ World)
  | .inl (x,y) => Z x y
  | .inr _ => False

theorem refinementCover_bisimulates (M : Model World Atom Agent)
    (N : Model World' Atom Agent) (Z : World → World' → Prop) :
    Bisimulates (refinementCover M N Z) M
      (fun x y => (match x with | .inl xy => xy.1 | .inr x => x) = y) := by
  constructor
  · constructor
    · intro x y hxy p
      change M.val p _ ↔ M.val p y
      rw [hxy]
    · intro x y hxy i z hyz
      refine ⟨.inr z, ?_, rfl⟩
      cases x with
      | inl xy => simpa only [refinementCover, hxy] using hyz
      | inr x => simpa only [refinementCover, hxy] using hyz
  · constructor
    · intro x y hxy p
      change M.val p _ ↔ M.val p y
      rw [hxy]
    · intro x y hxy i z hxz
      cases x with
      | inl xy =>
        cases z with
        | inl uv => exact ⟨uv.1, hxy ▸ hxz.1, rfl⟩
        | inr z => exact ⟨z, hxy ▸ hxz, rfl⟩
      | inr x =>
        cases z with
        | inl uv => exact False.elim hxz
        | inr z => exact ⟨z, hxy ▸ hxz, rfl⟩

theorem refinementCover_restrict_bisimulates {M : Model World Atom Agent}
    {N : Model World' Atom Agent} {Z : World → World' → Prop} (hZ : Refines M N Z) :
    Bisimulates ((refinementCover M N Z).restrict (refinementDomain Z)) N
      (fun x y => match x.val with | .inl xy => xy.2 = y | .inr _ => False) := by
  constructor
  · constructor
    · rintro ⟨xy, hxy⟩ y hy p
      cases xy with
      | inl xy =>
        change M.val p xy.1 ↔ N.val p y
        exact hy ▸ hZ.atoms xy.1 xy.2 hxy p
      | inr x => exact False.elim hxy
    · rintro ⟨xy, hxy⟩ y hy i z hyz
      cases xy with
      | inl xy =>
        change xy.2 = y at hy
        obtain ⟨t, hxt, htz⟩ := hZ.back xy.1 xy.2 hxy i z (hy ▸ hyz)
        refine ⟨⟨.inl (t,z), htz⟩, ?_, rfl⟩
        exact ⟨hxt, hy ▸ hyz, hxy, htz⟩
      | inr x => exact False.elim hxy
  · constructor
    · rintro ⟨xy, hxy⟩ y hy p
      cases xy with
      | inl xy =>
        change M.val p xy.1 ↔ N.val p y
        exact hy ▸ hZ.atoms xy.1 xy.2 hxy p
      | inr x => exact False.elim hxy
    · rintro ⟨xy, hxy⟩ y hy i ⟨tz, htz⟩ hrel
      cases xy with
      | inl xy =>
        cases tz with
        | inl tz => exact ⟨tz.2, hy ▸ hrel.2.1, rfl⟩
        | inr t => exact False.elim htz
      | inr x => exact False.elim hxy

/-- Preservation under arbitrary pointed refinements in the given universe. -/
def RefinementPreserved (φ : Formula Atom Agent) : Prop :=
  ∀ {World World' : Type u} (M : Model World Atom Agent) (N : Model World' Atom Agent)
    (Z : World → World' → Prop), Refines M N Z →
    ∀ x y, Z x y → M.Satisfies x φ → N.Satisfies y φ

/-- Preservation under arbitrary pointed simulations in the given universe. -/
def SimulationPreserved (φ : Formula Atom Agent) : Prop :=
  ∀ {World World' : Type u} (M : Model World Atom Agent) (N : Model World' Atom Agent)
    (Z : World → World' → Prop), Simulates M N Z →
    ∀ x y, Z x y → M.Satisfies x φ → N.Satisfies y φ

theorem SubmodelPreserved.refinementPreserved {φ : Formula Atom Agent}
    (hφ : SubmodelPreserved.{u} φ) : RefinementPreserved.{u} φ := by
  intro World World' M N Z hZ x y hxy hx
  let c : ((World × World') ⊕ World) := .inl (x,y)
  have hc : (refinementCover M N Z).Satisfies c φ :=
    ((refinementCover_bisimulates M N Z).satisfies_iff (x := c) rfl φ).mpr hx
  have hr := hφ (refinementCover M N Z) (refinementDomain Z) ⟨c,hxy⟩ hc
  exact ((refinementCover_restrict_bisimulates hZ).satisfies_iff
    (x := ⟨c,hxy⟩) (y := y) rfl φ).mp hr

theorem RefinementPreserved.deletionMonotone {φ : Formula Atom Agent}
    (hφ : RefinementPreserved.{u} φ) : DeletionMonotone.{u} φ := by
  intro World M N hNM x hx
  exact hφ M N Eq hNM.refines x x rfl hx

theorem deletionMonotone_iff_submodelPreserved (φ : Formula Atom Agent) :
    DeletionMonotone.{u} φ ↔ SubmodelPreserved.{u} φ :=
  ⟨DeletionMonotone.submodelPreserved,
    fun h => RefinementPreserved.deletionMonotone (SubmodelPreserved.refinementPreserved h)⟩

theorem submodelPreserved_iff_refinementPreserved (φ : Formula Atom Agent) :
    SubmodelPreserved.{u} φ ↔ RefinementPreserved.{u} φ :=
  ⟨SubmodelPreserved.refinementPreserved,
    fun h => DeletionMonotone.submodelPreserved (RefinementPreserved.deletionMonotone h)⟩

theorem submodelPreserved_neg_iff_extensionPreserved (φ : Formula Atom Agent) :
    SubmodelPreserved.{u} (.neg φ) ↔ ExtensionPreserved.{u} φ := by
  classical
  constructor
  · intro h World M S x hx
    by_contra hn
    exact h M S x hn hx
  · intro h World M S x hn hx
    exact hn (h M S x hx)

theorem refinementPreserved_neg_iff_simulationPreserved (φ : Formula Atom Agent) :
    RefinementPreserved.{u} (.neg φ) ↔ SimulationPreserved.{u} φ := by
  classical
  constructor
  · intro h World World' M N Z hZ x y hxy hx
    by_contra hn
    exact h N M (fun y x => Z x y) ((simulates_iff_inverse_refines M N Z).mp hZ)
      y x hxy hn hx
  · intro h World World' M N Z hZ x y hxy hn hx
    have hs : Simulates N M (fun y x => Z x y) :=
      (simulates_iff_inverse_refines N M (fun y x => Z x y)).mpr hZ
    exact hn (h N M (fun y x => Z x y) hs y x hxy hx)

theorem deletionAntimonotone_iff_extensionPreserved (φ : Formula Atom Agent) :
    DeletionAntimonotone.{u} φ ↔ ExtensionPreserved.{u} φ :=
  (deletionMonotone_neg_iff φ).symm.trans
    ((deletionMonotone_iff_submodelPreserved (.neg φ)).trans
      (submodelPreserved_neg_iff_extensionPreserved φ))

theorem extensionPreserved_iff_simulationPreserved (φ : Formula Atom Agent) :
    ExtensionPreserved.{u} φ ↔ SimulationPreserved.{u} φ :=
  (submodelPreserved_neg_iff_extensionPreserved φ).symm.trans
    ((submodelPreserved_iff_refinementPreserved (.neg φ)).trans
      (refinementPreserved_neg_iff_simulationPreserved φ))

theorem Universal.successful {φ : Formula Atom Agent} (hφ : Universal φ)
    (M : Model World Atom Agent) (x : World) :
    M.Satisfies x φ → (M.update φ).Satisfies x φ :=
  hφ.preserved_arrowSubmodel (update_arrowSubmodel M φ)

theorem Universal.update_idempotent {φ : Formula Atom Agent} (hφ : Universal φ)
    (M : Model World Atom Agent) : (M.update φ).update φ = M.update φ := by
  apply Model.ext'
  · intro i x y
    exact ⟨fun h => h.1, fun h => ⟨h, hφ.successful M y h.2⟩⟩
  · intro p x
    rfl

theorem Universal.fixed_downward {φ : Formula Atom Agent} (hφ : Universal φ)
    {M N : Model World Atom Agent} (hNM : ArrowSubmodel N M) (hM : M.update φ = M) :
    N.update φ = N := by
  apply Model.ext'
  · intro i x y
    constructor
    · exact And.left
    · intro hxy
      have hm : (M.update φ).rel i x y := by rw [hM]; exact hNM.rel_le i x y hxy
      exact ⟨hxy, hφ.preserved_arrowSubmodel hNM hm.2⟩
  · intro p x
    rfl

/-- Universal announcements absorb a later repetition, even across an
arbitrary intervening announcement (Theorem 23(3)). -/
theorem Universal.absorption {φ : Formula Atom Agent} (hφ : Universal φ)
    (ψ : Formula Atom Agent) (M : Model World Atom Agent) :
    ((M.update φ).update ψ).update φ = (M.update φ).update ψ :=
  hφ.fixed_downward (update_arrowSubmodel (M.update φ) ψ) (hφ.update_idempotent M)

theorem Universal.composition_idempotent {φ ψ : Formula Atom Agent}
    (hφ : Universal φ) (hψ : Universal ψ) (M : Model World Atom Agent) :
    (((M.update φ).update ψ).update φ).update ψ = (M.update φ).update ψ := by
  rw [hφ.absorption ψ M, hψ.update_idempotent]

theorem Existential.fixed_below_update {φ : Formula Atom Agent} (hφ : Existential φ)
    {M N : Model World Atom Agent} (hNM : ArrowSubmodel N M) (hN : N.update φ = N) :
    ArrowSubmodel N (M.update φ) ∧ ArrowSubmodel (M.update φ) M := by
  refine ⟨⟨hNM.val_eq, ?_⟩, update_arrowSubmodel M φ⟩
  intro i x y hxy
  have hn : (N.update φ).rel i x y := by rw [hN]; exact hxy
  exact ⟨hNM.rel_le i x y hxy, hφ.preserved_arrowExtension hNM hn.2⟩

end PropertiesOfPublicAnnouncementsAsOperators
