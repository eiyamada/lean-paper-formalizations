import Mathlib.SetTheory.Ordinal.FixedPointApproximants

/-! # General deflationary ordinal iteration (Definition 22)

For PAL, `X` is the original world carrier and subsets are surviving domains.
For BPAL, `X` is the carrier of original labelled arrows; the initial domain and
valuation stay fixed. The operator need not be monotone. Monotonicity is used
only for the greatest-fixed-point conclusion.
-/

namespace PropertiesOfPublicAnnouncementsAsOperators.AbstractIteration

universe u
variable {X : Type u}

def Deflationary (F : Set X → Set X) : Prop := ∀ S, F S ⊆ S

/-- The set retained from `S` by all earlier applications of `F`. -/
def iterate (F : Set X → Set X) (S : Set X) (α : Ordinal.{u}) : Set X :=
  {x | x ∈ S ∧ ∀ β < α, x ∈ F (iterate F S β)}
termination_by α
decreasing_by assumption

theorem mem_iterate (F : Set X → Set X) (S : Set X) (α : Ordinal.{u}) (x : X) :
    x ∈ iterate F S α ↔ x ∈ S ∧ ∀ β < α, x ∈ F (iterate F S β) := by
  rw [iterate]
  rfl

@[simp] theorem iterate_zero (F : Set X → Set X) (S : Set X) : iterate F S 0 = S := by
  ext x
  simp [mem_iterate]

theorem iterate_subset (F : Set X → Set X) (S : Set X) (α : Ordinal.{u}) :
    iterate F S α ⊆ S := fun x hx => ((mem_iterate F S α x).mp hx).1

theorem iterate_antitone (F : Set X → Set X) (S : Set X) : Antitone (iterate F S) := by
  intro α β hαβ x hx
  rw [mem_iterate] at hx ⊢
  exact ⟨hx.1, fun γ hγ => hx.2 γ (lt_of_lt_of_le hγ hαβ)⟩

/-- The successor clause requires only deflationarity, not monotonicity. -/
theorem iterate_succ (F : Set X → Set X) (hF : Deflationary F)
    (S : Set X) (α : Ordinal.{u}) : iterate F S (Order.succ α) = F (iterate F S α) := by
  ext x
  constructor
  · intro hx
    exact ((mem_iterate F S (Order.succ α) x).mp hx).2 α (Order.lt_succ α)
  · intro hx
    have hα := (mem_iterate F S α x).mp (hF _ hx)
    rw [mem_iterate]
    refine ⟨hα.1, fun β hβ => ?_⟩
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hβ) with hlt | rfl
    · exact hα.2 β hlt
    · exact hx

theorem iterate_limit (F : Set X → Set X) (hF : Deflationary F)
    (S : Set X) {α : Ordinal.{u}} (hα : Order.IsSuccLimit α) :
    iterate F S α = ⋂ β < α, iterate F S β := by
  ext x
  simp only [Set.mem_iInter]
  constructor
  · exact fun hx β hβ => iterate_antitone F S hβ.le hx
  · intro hx
    rw [mem_iterate]
    refine ⟨?_, fun β hβ => ?_⟩
    · simpa only [iterate_zero] using hx 0 hα.bot_lt
    · rw [← iterate_succ F hF]
      exact hx (Order.succ β) (hα.succ_lt hβ)

def Stable (F : Set X → Set X) (S : Set X) (α : Ordinal.{u}) : Prop :=
  iterate F S (Order.succ α) = iterate F S α

theorem stable_iff_fixed (F : Set X → Set X) (hF : Deflationary F)
    (S : Set X) (α : Ordinal.{u}) : Stable F S α ↔ F (iterate F S α) = iterate F S α := by
  rw [Stable, iterate_succ F hF]

/-- Every strict step loses an original element. -/
theorem exists_deleted_point (F : Set X → Set X) (S : Set X) (α : Ordinal.{u})
    (h : ¬Stable F S α) :
    ∃ x : S, x.val ∈ iterate F S α ∧ x.val ∉ iterate F S (Order.succ α) := by
  classical
  by_contra! hn
  apply h
  apply Set.Subset.antisymm (iterate_antitone F S (Order.le_succ α))
  intro x hx
  exact hn ⟨x, iterate_subset F S α hx⟩ hx

/-- No strictly decreasing run can have more strict stages than original
elements. The bound is the ordinal of the successor cardinal of `S`. -/
theorem exists_stable_bounded (F : Set X → Set X) (S : Set X) :
    ∃ α < (Order.succ (Cardinal.mk S)).ord, Stable F S α := by
  classical
  let κ := (Order.succ (Cardinal.mk S)).ord
  by_contra! hn
  have hκ : (0 : Ordinal.{u}) < κ := by
    simpa only [Cardinal.ord_zero] using
      Cardinal.ord_strictMono (Cardinal.succ_pos (Cardinal.mk S))
  have hex : ∀ α < κ, ∃ x : S,
      x.val ∈ iterate F S α ∧ x.val ∉ iterate F S (Order.succ α) :=
    fun α hα => exists_deleted_point F S α (hn α hα)
  obtain ⟨x₀, _⟩ := hex 0 hκ
  let f : Ordinal.{u} → S := fun α =>
    if hα : α < κ then Classical.choose (hex α hα) else x₀
  have hf (α : Ordinal.{u}) (hα : α < κ) :
      (f α).val ∈ iterate F S α ∧ (f α).val ∉ iterate F S (Order.succ α) := by
    simpa only [f, dif_pos hα] using Classical.choose_spec (hex α hα)
  apply Cardinal.not_injective_limitation_set f
  intro α hα β hβ heq
  have hnotlt : ∀ a < κ, ∀ b < κ, f a = f b → ¬a < b := by
    intro a ha b hb hab hlt
    have hremain := iterate_antitone F S (Order.succ_le_of_lt hlt) (hf b hb).1
    rw [← hab] at hremain
    exact (hf a ha).2 hremain
  exact le_antisymm (le_of_not_gt (hnotlt β hβ α hα heq.symm))
    (le_of_not_gt (hnotlt α hα β hβ heq))

theorem exists_stable (F : Set X → Set X) (S : Set X) : ∃ α, Stable F S α := by
  obtain ⟨α, _, hα⟩ := exists_stable_bounded F S
  exact ⟨α, hα⟩

/-- A stable stage remains fixed through every later successor and limit. -/
theorem iterate_eq_of_ge_of_stable (F : Set X → Set X) (hF : Deflationary F)
    (S : Set X) {α β : Ordinal.{u}} (h : Stable F S α) (hαβ : α ≤ β) :
    iterate F S β = iterate F S α := by
  induction β using Ordinal.induction with
  | h β ih =>
      apply Set.Subset.antisymm (iterate_antitone F S hαβ)
      intro x hx
      have hx' := (mem_iterate F S α x).mp hx
      rw [mem_iterate]
      refine ⟨hx'.1, fun γ hγ => ?_⟩
      by_cases hγα : γ < α
      · exact hx'.2 γ hγα
      · rw [ih γ hγ (le_of_not_gt hγα), (stable_iff_fixed F hF S α).mp h]
        exact hx

noncomputable def rank (F : Set X → Set X) (S : Set X) : Ordinal.{u} :=
  sInf {α | Stable F S α}

theorem rank_stable (F : Set X → Set X) (S : Set X) : Stable F S (rank F S) :=
  csInf_mem (exists_stable F S)

theorem rank_le_of_stable (F : Set X → Set X) (S : Set X) {α : Ordinal.{u}}
    (h : Stable F S α) : rank F S ≤ α := csInf_le' h

noncomputable def terminal (F : Set X → Set X) (S : Set X) : Set X :=
  iterate F S (rank F S)

theorem terminal_fixed (F : Set X → Set X) (hF : Deflationary F) (S : Set X) :
    F (terminal F S) = terminal F S := (stable_iff_fixed F hF S _).mp (rank_stable F S)

theorem terminal_subset (F : Set X → Set X) (S : Set X) : terminal F S ⊆ S :=
  iterate_subset F S _

/-- A fixed point below the initial set lies below every monotone iterate. -/
theorem fixed_below_iterate (F : Set X → Set X) (hmono : Monotone F)
    (S N : Set X) (hNS : N ⊆ S) (hN : F N = N) (α : Ordinal.{u}) :
    N ⊆ iterate F S α := by
  induction α using Ordinal.induction with
  | h α ih =>
      intro x hx
      rw [mem_iterate]
      refine ⟨hNS hx, fun β hβ => ?_⟩
      apply hmono (ih β hβ)
      rw [hN]
      exact hx

/-- The greatest-fixed-point description used in Theorem 23, for any
monotone deflationary set operator. -/
theorem terminal_eq_union_fixed (F : Set X → Set X) (hF : Deflationary F)
    (hmono : Monotone F) (S : Set X) :
    terminal F S = ⋃₀ {N | N ⊆ S ∧ F N = N} := by
  ext x
  constructor
  · intro hx
    exact ⟨terminal F S, ⟨terminal_subset F S, terminal_fixed F hF S⟩, hx⟩
  · rintro ⟨N, ⟨hNS, hN⟩, hx⟩
    exact fixed_below_iterate F hmono S N hNS hN _ hx

end PropertiesOfPublicAnnouncementsAsOperators.AbstractIteration
