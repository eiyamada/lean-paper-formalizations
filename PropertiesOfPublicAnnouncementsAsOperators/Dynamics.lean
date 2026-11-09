import EventualAndStrongEventualNotionsInPublicAnnouncements.OrdinalDynamics
import ClassificationSigmaValidity.Expressivity

/-!
# Ordinal PAL and BPAL dynamics

The PAL orbit is represented by its surviving domain in the original model.
The proofs below identify its successor with the actual induced-submodel update,
and its limit with intersection. Thus equality of domains is precisely equality
of the corresponding induced models, not merely modal equivalence.
-/

namespace PropertiesOfPublicAnnouncementsAsOperators

open ClassificationSigmaValidity
open EventualAndStrongEventualNotionsInPublicAnnouncements

universe u v w

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- States retained by all announcements strictly before `α`. -/
def palDomain (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) : Set World :=
  {x | ∀ β < α, (ordinalUpdate M φ β).Satisfies x φ}

@[simp] theorem palDomain_zero (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    palDomain M φ 0 = Set.univ := by
  ext x
  simp [palDomain]

theorem palDomain_antitone (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    Antitone (palDomain M φ) := by
  intro α β hαβ x hx γ hγ
  exact hx γ (lt_of_lt_of_le hγ hαβ)

theorem palDomain_succ (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) :
    palDomain M φ (Order.succ α) =
      {x | x ∈ palDomain M φ α ∧ (ordinalUpdate M φ α).Satisfies x φ} := by
  ext x
  constructor
  · intro h
    exact ⟨fun β hβ => h β (lt_trans hβ (Order.lt_succ α)), h α (Order.lt_succ α)⟩
  · rintro ⟨h, hα⟩ β hβ
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hβ) with hlt | rfl
    · exact h β hlt
    · exact hα

/-- The limit clause of transfinite PAL iteration. -/
theorem palDomain_limit (M : Model World Atom Agent) (φ : Formula Atom Agent)
    {α : Ordinal.{max u w}} (hα : Order.IsSuccLimit α) :
    palDomain M φ α = ⋂ β < α, palDomain M φ β := by
  ext x
  simp only [Set.mem_iInter]
  constructor
  · exact fun h β hβ => palDomain_antitone M φ hβ.le h
  · intro h β hβ
    exact h (Order.succ β) (hα.succ_lt hβ) β (Order.lt_succ β)

/-- The same-domain BPAL presentation of the PAL orbit. -/
theorem palDomain_domainModel (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) :
    PAL.domainModel M (palDomain M φ α) = ordinalUpdate M φ α := by
  apply Model.ext'
  · intro i x y
    rw [PAL.domainModel_rel, ordinalUpdate_rel_iff]
    exact and_comm
  · intro p x
    exact (ordinalUpdate_val M φ α p x).symm

/-- The original and updated models induce the same model on survivors. -/
theorem palDomain_restrict_eq (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) :
    (ordinalUpdate M φ α).restrict (palDomain M φ α) =
      M.restrict (palDomain M φ α) := by
  apply Model.ext'
  · intro i x y
    change (ordinalUpdate M φ α).rel i x.val y.val ↔ M.rel i x.val y.val
    rw [ordinalUpdate_rel_iff]
    exact and_iff_left y.property
  · intro p x
    exact ordinalUpdate_val M φ α p x.val

theorem palDomain_forwardClosed (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) :
    (ordinalUpdate M φ α).ForwardClosed (palDomain M φ α) := by
  intro x hx i y hxy
  exact ((ordinalUpdate_rel_iff M φ α i x y).mp hxy).2

/-- Orbit correspondence for every static epistemic formula. -/
theorem palDomain_satisfies_iff (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) (x : palDomain M φ α) (ψ : Formula Atom Agent) :
    (M.restrict (palDomain M φ α)).Satisfies x ψ ↔
      (ordinalUpdate M φ α).Satisfies x.val ψ := by
  rw [← palDomain_restrict_eq]
  exact Model.restrict_satisfies_iff _ _ (palDomain_forwardClosed M φ α) x ψ

/-- The successor clause uses the actual PAL semantics. -/
theorem palDomain_succ_pal (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) :
    palDomain M φ (Order.succ α) =
      {x | x ∈ palDomain M φ α ∧ PAL.Satisfies M (palDomain M φ α) x φ.toPAL} := by
  rw [palDomain_succ]
  ext x
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, PAL.satisfies_toPAL, palDomain_domainModel]

/-- A PAL stage is stable precisely when its next surviving domain is equal. -/
def PALStable (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) : Prop :=
  palDomain M φ (Order.succ α) = palDomain M φ α

/-- A BPAL stage is stable precisely when the next actual model is equal. -/
def BPALStable (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) : Prop :=
  ordinalUpdate M φ (Order.succ α) = ordinalUpdate M φ α

theorem palStable_iff (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) :
    PALStable M φ α ↔ ∀ x ∈ palDomain M φ α, (ordinalUpdate M φ α).Satisfies x φ := by
  rw [PALStable, palDomain_succ]
  constructor
  · intro h x hx
    have : x ∈ {x | x ∈ palDomain M φ α ∧ (ordinalUpdate M φ α).Satisfies x φ} := by
      rw [h]
      exact hx
    exact this.2
  · intro h
    ext x
    exact ⟨And.left, fun hx => ⟨hx, h x hx⟩⟩

/-- PAL stability implies BPAL stability at the same stage. -/
theorem bpalStable_of_palStable (M : Model World Atom Agent) (φ : Formula Atom Agent)
    {α : Ordinal.{max u w}} (h : PALStable M φ α) : BPALStable M φ α := by
  change ordinalUpdate M φ (Order.succ α) = ordinalUpdate M φ α
  rw [← palDomain_domainModel, ← palDomain_domainModel, h]

/-- A stable BPAL orbit has at most one additional PAL deletion step. -/
theorem palStable_succ_of_bpalStable (M : Model World Atom Agent) (φ : Formula Atom Agent)
    {α : Ordinal.{max u w}} (h : BPALStable M φ α) : PALStable M φ (Order.succ α) := by
  apply (palStable_iff M φ _).mpr
  intro x hx
  rw [palDomain_succ] at hx
  change (ordinalUpdate M φ (Order.succ α)).Satisfies x φ
  rw [h]
  exact hx.2

/-- Every initial world is the target of some initial labelled arrow. -/
def HasIncoming (M : Model World Atom Agent) : Prop :=
  ∀ y, ∃ i x, M.rel i x y

/-- Incoming arrows make BPAL equality detect every PAL domain deletion. -/
theorem palStable_of_bpalStable (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (hin : HasIncoming M) {α : Ordinal.{max u w}} (h : BPALStable M φ α) :
    PALStable M φ α := by
  apply (palStable_iff M φ α).mpr
  intro y hy
  obtain ⟨i, x, hxy⟩ := hin y
  have harrow : (ordinalUpdate M φ α).rel i x y :=
    (ordinalUpdate_rel_iff M φ α i x y).mpr ⟨hxy, hy⟩
  have harrow' : (ordinalUpdate M φ (Order.succ α)).rel i x y := by rw [h]; exact harrow
  rw [ordinalUpdate_succ, Model.update_rel] at harrow'
  exact harrow'.2

theorem exists_palStable (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    ∃ α, PALStable M φ α := by
  obtain ⟨α, hα⟩ := exists_ordinalUpdate_stableStep M φ
  exact ⟨Order.succ α, palStable_succ_of_bpalStable M φ hα⟩

/-- The least transfinite PAL stabilization rank (Definition 22). -/
noncomputable def palRank (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    Ordinal.{max u w} := sInf {α | PALStable M φ α}

/-- The least transfinite BPAL stabilization rank (Definition 22). -/
noncomputable def bpalRank (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    Ordinal.{max u w} := sInf {α | BPALStable M φ α}

theorem palRank_stable (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    PALStable M φ (palRank M φ) := csInf_mem (exists_palStable M φ)

theorem bpalRank_stable (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    BPALStable M φ (bpalRank M φ) := csInf_mem (exists_ordinalUpdate_stableStep M φ)

theorem palRank_le_of_stable (M : Model World Atom Agent) (φ : Formula Atom Agent)
    {α : Ordinal.{max u w}} (h : PALStable M φ α) : palRank M φ ≤ α := csInf_le' h

theorem bpalRank_le_of_stable (M : Model World Atom Agent) (φ : Formula Atom Agent)
    {α : Ordinal.{max u w}} (h : BPALStable M φ α) : bpalRank M φ ≤ α := csInf_le' h

/-- Theorem 24(1), the two rank inequalities. -/
theorem stabilization_rank_comparison (M : Model World Atom Agent) (φ : Formula Atom Agent) :
    bpalRank M φ ≤ palRank M φ ∧ palRank M φ ≤ bpalRank M φ + 1 := by
  exact ⟨bpalRank_le_of_stable M φ (bpalStable_of_palStable M φ (palRank_stable M φ)),
    palRank_le_of_stable M φ (palStable_succ_of_bpalStable M φ (bpalRank_stable M φ))⟩

/-- Theorem 24(1), equality if every state has an incoming arrow. -/
theorem stabilization_rank_eq_of_incoming (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (hin : HasIncoming M) : palRank M φ = bpalRank M φ := by
  exact le_antisymm
    (palRank_le_of_stable M φ (palStable_of_bpalStable M φ hin (bpalRank_stable M φ)))
    (stabilization_rank_comparison M φ).1

theorem hasIncoming_of_reflexive [Nonempty Agent] (M : Model World Atom Agent)
    (h : ∀ i x, M.rel i x x) : HasIncoming M := by
  classical
  intro x
  exact ⟨Classical.arbitrary Agent, x, h _ _⟩

theorem stabilization_rank_eq_of_s5 [Nonempty Agent] (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (h : IsS5 M) : palRank M φ = bpalRank M φ := by
  apply stabilization_rank_eq_of_incoming M φ
  apply hasIncoming_of_reflexive
  intro i x
  exact (h i).1 x

/-- No PAL states are lost after a stable stage, including at limits. -/
theorem palDomain_eq_of_ge_of_stable (M : Model World Atom Agent) (φ : Formula Atom Agent)
    {α β : Ordinal.{max u w}} (h : PALStable M φ α) (hαβ : α ≤ β) :
    palDomain M φ β = palDomain M φ α := by
  apply Set.Subset.antisymm (palDomain_antitone M φ hαβ)
  intro x hx γ hγ
  by_cases hγα : γ < α
  · exact hx γ hγα
  · rw [ordinalUpdate_eq_of_ge_of_step M φ (bpalStable_of_palStable M φ h)
      (le_of_not_gt hγα)]
    exact (palStable_iff M φ α).mp h x hx

theorem palStable_of_le (M : Model World Atom Agent) (φ : Formula Atom Agent)
    {α β : Ordinal.{max u w}} (h : PALStable M φ α) (hαβ : α ≤ β) :
    PALStable M φ β := by
  unfold PALStable
  rw [palDomain_eq_of_ge_of_stable M φ h hαβ,
    palDomain_eq_of_ge_of_stable M φ h (le_trans hαβ (Order.le_succ β))]

theorem bpalStable_of_le (M : Model World Atom Agent) (φ : Formula Atom Agent)
    {α β : Ordinal.{max u w}} (h : BPALStable M φ α) (hαβ : α ≤ β) :
    BPALStable M φ β := by
  unfold BPALStable
  rw [ordinalUpdate_eq_of_ge_of_step M φ h hαβ,
    ordinalUpdate_eq_of_ge_of_step M φ h (le_trans hαβ (Order.le_succ β))]

theorem palRank_le_iff (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) : palRank M φ ≤ α ↔ PALStable M φ α :=
  ⟨palStable_of_le M φ (palRank_stable M φ), palRank_le_of_stable M φ⟩

theorem bpalRank_le_iff (M : Model World Atom Agent) (φ : Formula Atom Agent)
    (α : Ordinal.{max u w}) : bpalRank M φ ≤ α ↔ BPALStable M φ α :=
  ⟨bpalStable_of_le M φ (bpalRank_stable M φ), bpalRank_le_of_stable M φ⟩

/-- A decreasing chain of subsets of a finite carrier has a stable step by
the carrier's cardinality. Each strict step consumes a different element. -/
theorem antitoneSet_stableStep_le_card {X : Type*} [Fintype X]
    (s : Nat → Set X) (hs : Antitone s) :
    ∃ n ≤ Fintype.card X, s (n + 1) = s n := by
  classical
  by_contra! hn
  have hex (n : Fin (Fintype.card X + 1)) : ∃ x, x ∈ s n.val ∧ x ∉ s (n.val + 1) := by
    by_contra! hnone
    apply hn n.val (Nat.le_of_lt_succ n.isLt)
    exact Set.Subset.antisymm (hs (Nat.le_succ _)) hnone
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have hnotlt (a b : Fin (Fintype.card X + 1)) (hab : f a = f b) : ¬a.val < b.val := by
      intro hlt
      have hremain := hs (Nat.succ_le_of_lt hlt) (hf b).1
      rw [← hab] at hremain
      exact (hf a).2 hremain
    exact le_antisymm (le_of_not_gt (hnotlt b a hab.symm))
      (le_of_not_gt (hnotlt a b hab))
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- Theorem 24(2): a finite PAL model stabilizes in at most `|W|` steps. -/
theorem palRank_le_card [Fintype World] (M : Model World Atom Agent)
    (φ : Formula Atom Agent) : palRank M φ ≤ (Fintype.card World : Ordinal.{max u w}) := by
  obtain ⟨n, hn, heq⟩ := antitoneSet_stableStep_le_card
    (fun n : Nat => palDomain M φ (n : Ordinal.{max u w}))
    (fun _ _ h => palDomain_antitone M φ (by exact_mod_cast h))
  have hstable : PALStable M φ (n : Ordinal.{max u w}) := heq
  exact le_trans (palRank_le_of_stable M φ hstable) (by exact_mod_cast hn)

/-- Theorem 24(2), including BPAL even with infinitely many labelled arrows
per surviving world. -/
theorem bpalRank_le_card [Fintype World] (M : Model World Atom Agent)
    (φ : Formula Atom Agent) : bpalRank M φ ≤ (Fintype.card World : Ordinal.{max u w}) :=
  le_trans (stabilization_rank_comparison M φ).1 (palRank_le_card M φ)

end PropertiesOfPublicAnnouncementsAsOperators
