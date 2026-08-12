import ClassificationSigmaValidity.EquivalenceClasses
import ClassificationSigmaValidity.Examples
import ClassificationSigmaValidity.ExistenceS5Zero
import ClassificationSigmaValidity.ExistenceZeroOne
import ClassificationSigmaValidity.Unravelling
import ClassificationSigmaValidity.AgentSupport
import ClassificationSigmaValidity.ClassificationDisjointness
import ClassificationSigmaValidity.WellDefinedness

/-!
# Classification theorem

This file gives a precise version of the paper's disjoint-union statement.
`ValClass C sigma representative` includes the requirement that `sigma` is
admissible: equivalence of validity sets alone does not, in general, imply
that the same truth pattern is satisfiable.  The normal-form predicates below
therefore describe exactly the elements of the paper's set `S`, grouped by
their `ValEq` class.
-/

namespace ClassificationSigmaValidity

universe u v w

open Pattern Sigma

namespace Classification

variable {Atom : Type v} {Agent : Type w} {sigma : Pattern}

/-- Membership in the validity class represented by `representative`, within
the paper's domain `S` of admissible patterns. -/
def ValClass (C : FrameClass.{u} Atom Agent) (sigma representative : Pattern) : Prop :=
  Sigma.Admissible C sigma ∧ Sigma.ValEq C sigma representative

/-- The five kinds of validity class occurring over K45. -/
inductive K45NormalForm (C : FrameClass.{u} Atom Agent) (sigma : Pattern) : Prop where
  | zerosInf : ValClass C sigma Pattern.zerosInf -> K45NormalForm C sigma
  | zeroOnes (k : Nat) (hk : 1 <= k) :
      ValClass C sigma (Pattern.zeroOnes k hk) -> K45NormalForm C sigma
  | zeroOnesInf : ValClass C sigma Pattern.zeroOnesInf -> K45NormalForm C sigma
  | oneZerosInf : ValClass C sigma Pattern.oneZerosInf -> K45NormalForm C sigma
  | onesInf : ValClass C sigma Pattern.onesInf -> K45NormalForm C sigma

/-- The two additional classes caused by the loss of seriality after an
announcement in single-agent KD45. -/
inductive SingleKD45NormalForm
    (C : FrameClass.{u} Atom Unit) (sigma : Pattern) : Prop where
  | zerosInf : ValClass C sigma Pattern.zerosInf -> SingleKD45NormalForm C sigma
  | zeroOnes (k : Nat) (hk : 1 <= k) :
      ValClass C sigma (Pattern.zeroOnes k hk) -> SingleKD45NormalForm C sigma
  | zeroOnesInf : ValClass C sigma Pattern.zeroOnesInf -> SingleKD45NormalForm C sigma
  | oneZero : ValClass C sigma Pattern.oneZero -> SingleKD45NormalForm C sigma
  | oneZerosInf : ValClass C sigma Pattern.oneZerosInf -> SingleKD45NormalForm C sigma
  | oneZeroOnesInf :
      ValClass C sigma Pattern.oneZeroOnesInf -> SingleKD45NormalForm C sigma
  | onesInf : ValClass C sigma Pattern.onesInf -> SingleKD45NormalForm C sigma

/-- The common normal forms for multi-agent KD45 (with two distinct agents)
and S5.  These add the finite all-zero hierarchy. -/
inductive SerialNormalForm (C : FrameClass.{u} Atom Agent) (sigma : Pattern) : Prop where
  | zerosInf : ValClass C sigma Pattern.zerosInf -> SerialNormalForm C sigma
  | zeros (k : Nat) (hk : 2 <= k) :
      ValClass C sigma (Pattern.zeros k hk) -> SerialNormalForm C sigma
  | zeroOnes (k : Nat) (hk : 1 <= k) :
      ValClass C sigma (Pattern.zeroOnes k hk) -> SerialNormalForm C sigma
  | zeroOnesInf : ValClass C sigma Pattern.zeroOnesInf -> SerialNormalForm C sigma
  | oneZero : ValClass C sigma Pattern.oneZero -> SerialNormalForm C sigma
  | oneZerosInf : ValClass C sigma Pattern.oneZerosInf -> SerialNormalForm C sigma
  | oneZeroOnesInf :
      ValClass C sigma Pattern.oneZeroOnesInf -> SerialNormalForm C sigma
  | onesInf : ValClass C sigma Pattern.onesInf -> SerialNormalForm C sigma

/-! ## Pattern combinatorics -/

private theorem holdsBit_unique {b c : Bool} {P : Prop}
    (hb : Pattern.HoldsBit b P) (hc : Pattern.HoldsBit c P) : b = c := by
  cases b <;> cases c <;> simp_all [Pattern.HoldsBit]

/-- A pattern and an infinite stream realized by the same trace agree at every
place in the pattern's domain. -/
theorem isPrefix_infinite_of_common_realization
    {sigma : Pattern} {bits : Nat -> Bool} {trace : Nat -> Prop}
    (hsigma : sigma.RealizesTrace trace)
    (hbits : (Pattern.infinite bits).RealizesTrace trace) :
    sigma.IsPrefix (Pattern.infinite bits) := by
  cases sigma with
  | finite xs hxs =>
      intro n hn
      exact holdsBit_unique (hsigma n hn) (hbits n)
  | infinite ys =>
      funext n
      exact holdsBit_unique (hsigma n) (hbits n)

/-- Admissibility is inherited by a prefix. -/
theorem admissible_of_prefix (C : FrameClass.{u} Atom Agent)
    {tau sigma : Pattern} (hp : tau.IsPrefix sigma)
    (h : Sigma.Admissible C sigma) : Sigma.Admissible C tau := by
  rcases h with ⟨phi, hvalid, hsatisfiable⟩
  exact ⟨phi, Sigma.valid_of_prefix C phi hp hvalid,
    Sigma.satisfiable_of_prefix C phi hp hsatisfiable⟩

theorem first_eq_of_prefix {rho sigma : Pattern} (hp : rho.IsPrefix sigma) :
    rho.first = sigma.first := by
  cases rho with
  | finite xs hxs =>
      cases sigma with
      | finite ys hys =>
          have hx : 0 < xs.length := Nat.lt_of_lt_of_le (by decide) hxs
          have hy : 0 < ys.length :=
            Nat.lt_of_lt_of_le hx (List.IsPrefix.length_le hp)
          simpa [Pattern.first] using hp.getElem hx
      | infinite ys =>
          have hx : 0 < xs.length := Nat.lt_of_lt_of_le (by decide) hxs
          simpa [Pattern.first] using hp 0 hx
  | infinite xs =>
      cases sigma with
      | finite ys hys => exact hp.elim
      | infinite ys => exact congrFun hp 0

/-- If an admissible pattern extends a finite representative whose validity
class already determines an infinite completion, then the pattern belongs to
that completion class. -/
theorem valEq_completion_of_admissible
    (C : FrameClass.{u} Atom Agent) {rho sigma : Pattern} {bits : Nat -> Bool}
    (hrho : rho.IsPrefix sigma)
    (hcollapse : Sigma.ValEq C rho (Pattern.infinite bits))
    (hfirst : sigma.first = bits 0)
    (hadm : Sigma.Admissible C sigma) :
    Sigma.ValEq C sigma (Pattern.infinite bits) := by
  rcases hadm with ⟨witness, hwValid, World, M, hM, x, hx⟩
  have hrhoValid : Sigma.Valid C witness rho :=
    Sigma.valid_of_prefix C witness hrho hwValid
  have hcompletionValid : Sigma.Valid C witness (Pattern.infinite bits) :=
    (hcollapse witness).mp hrhoValid
  have hstartSigma := Pattern.realizesTrace_first hx
  have hstartCompletion : Pattern.HoldsBit (bits 0) (M.trace x witness 0) := by
    simpa [hfirst] using hstartSigma
  have hcompletion := hcompletionValid M hM x hstartCompletion
  have hsigmaPrefix : sigma.IsPrefix (Pattern.infinite bits) :=
    isPrefix_infinite_of_common_realization hx hcompletion
  intro phi
  constructor
  · intro hphi
    exact (hcollapse phi).mp (Sigma.valid_of_prefix C phi hrho hphi)
  · exact Sigma.valid_of_prefix C phi hsigmaPrefix

/-- Every pattern has exactly one of the four possible length-two prefixes.
Only existence is needed by the classification proof. -/
theorem four_prefixes (sigma : Pattern) :
    Pattern.zeroZero.IsPrefix sigma ∨ Pattern.zeroOne.IsPrefix sigma ∨
      Pattern.oneZero.IsPrefix sigma ∨ Pattern.oneOne.IsPrefix sigma := by
  cases sigma with
  | finite bits hlen =>
      cases bits with
      | nil => simp at hlen
      | cons b0 tail =>
          cases tail with
          | nil => simp at hlen
          | cons b1 rest =>
              cases b0 <;> cases b1
              · apply Or.inl
                change [false, false] <+: false :: false :: rest
                simp
              · apply Or.inr; apply Or.inl
                change [false, true] <+: false :: true :: rest
                simp
              · exact Or.inr (Or.inr (Or.inl (by
                  change [true, false] <+: true :: false :: rest
                  simp)))
              · exact Or.inr (Or.inr (Or.inr (by
                  change [true, true] <+: true :: true :: rest
                  simp)))
  | infinite bits =>
      cases h0 : bits 0 <;> cases h1 : bits 1
      · left
        intro n hn
        have hn2 : n < 2 := by simpa using hn
        have : n = 0 ∨ n = 1 := by omega
        rcases this with rfl | rfl <;> simp [h0, h1]
      · right; left
        intro n hn
        have hn2 : n < 2 := by simpa using hn
        have : n = 0 ∨ n = 1 := by omega
        rcases this with rfl | rfl <;> simp [h0, h1]
      · right; right; left
        intro n hn
        have hn2 : n < 2 := by simpa using hn
        have : n = 0 ∨ n = 1 := by omega
        rcases this with rfl | rfl <;> simp [h0, h1]
      · right; right; right
        intro n hn
        have hn2 : n < 2 := by simpa using hn
        have : n = 0 ∨ n = 1 := by omega
        rcases this with rfl | rfl <;> simp [h0, h1]

private theorem boolList_true_run (xs : List Bool) :
    xs = List.replicate xs.length true ∨
      ∃ k rest, xs = List.replicate k true ++ false :: rest := by
  induction xs with
  | nil => exact Or.inl (by simp)
  | cons b xs ih =>
      cases b with
      | false => exact Or.inr ⟨0, xs, by simp⟩
      | true =>
          rcases ih with h | ⟨k, rest, h⟩
          · left
            calc
              true :: xs = true :: List.replicate xs.length true :=
                congrArg (true :: ·) h
              _ = List.replicate (true :: xs).length true := by
                simp only [List.length_cons, List.replicate_succ]
          · right
            refine ⟨k + 1, rest, ?_⟩
            calc
              true :: xs = true :: (List.replicate k true ++ false :: rest) :=
                congrArg (true :: ·) h
              _ = List.replicate (k + 1) true ++ false :: rest := by
                rw [List.replicate_succ, List.cons_append]

private theorem boolList_false_run (xs : List Bool) :
    xs = List.replicate xs.length false ∨
      ∃ k rest, xs = List.replicate k false ++ true :: rest := by
  induction xs with
  | nil => exact Or.inl (by simp)
  | cons b xs ih =>
      cases b with
      | false =>
          rcases ih with h | ⟨k, rest, h⟩
          · left
            calc
              false :: xs = false :: List.replicate xs.length false :=
                congrArg (false :: ·) h
              _ = List.replicate (false :: xs).length false := by
                simp only [List.length_cons, List.replicate_succ]
          · right
            refine ⟨k + 1, rest, ?_⟩
            calc
              false :: xs = false :: (List.replicate k false ++ true :: rest) :=
                congrArg (false :: ·) h
              _ = List.replicate (k + 1) false ++ true :: rest := by
                rw [List.replicate_succ, List.cons_append]
      | true => exact Or.inr ⟨0, xs, by simp⟩

/-- A pattern beginning `01` is a finite or infinite block of ones, unless it
has a forbidden prefix `01^k0`. -/
theorem zeroOne_shape {sigma : Pattern} (h01 : Pattern.zeroOne.IsPrefix sigma) :
    (∃ k, ∃ hk : 1 <= k, sigma = Pattern.zeroOnes k hk) ∨
      sigma = Pattern.zeroOnesInf ∨
      ∃ k, ∃ hk : 1 <= k, (Pattern.zeroOnesZero k hk).IsPrefix sigma := by
  cases sigma with
  | finite bits hlen =>
      cases bits with
      | nil => simp at hlen
      | cons b0 tail =>
          cases tail with
          | nil => simp at hlen
          | cons b1 rest =>
              have hb0 : b0 = false := by
                simpa [Pattern.zeroOne, Pattern.bits2] using
                  h01.getElem (i := 0) (by decide)
              have hb1 : b1 = true := by
                simpa [Pattern.zeroOne, Pattern.bits2] using
                  h01.getElem (i := 1) (by decide)
              subst b0
              subst b1
              rcases boolList_true_run rest with htrue | ⟨r, more, hr⟩
              · left
                refine ⟨rest.length + 1, by omega, ?_⟩
                congr 1
                calc
                  false :: true :: rest =
                      false :: true :: List.replicate rest.length true :=
                    congrArg (fun xs => false :: true :: xs) htrue
                  _ = false :: List.replicate (rest.length + 1) true := by
                    rw [List.replicate_succ]
              · right; right
                refine ⟨r + 1, by omega, ?_⟩
                change (false :: List.replicate (r + 1) true ++ [false]) <+:
                  false :: true :: rest
                rw [hr, List.replicate_succ]
                simp
  | infinite bits =>
      have h0 : bits 0 = false := by
        simpa [Pattern.zeroOne, Pattern.bits2] using h01 0 (by decide)
      have h1 : bits 1 = true := by
        simpa [Pattern.zeroOne, Pattern.bits2] using h01 1 (by decide)
      by_cases hall : ∀ n, 2 <= n -> bits n = true
      · right; left
        congr 1
        funext n
        cases n with
        | zero => simpa [Pattern.zeroOnesInf] using h0
        | succ n =>
            cases n with
            | zero => simpa [Pattern.zeroOnesInf] using h1
            | succ n => simpa [Pattern.zeroOnesInf] using hall (n + 2) (by omega)
      · push_neg at hall
        let n := Nat.find hall
        have hn2 : 2 <= n := (Nat.find_spec hall).1
        have hnFalse : bits n = false :=
          Bool.eq_false_iff.mpr (Nat.find_spec hall).2
        let k := n - 1
        have hk : 1 <= k := by omega
        right; right
        refine ⟨k, hk, ?_⟩
        intro m hm
        have hmBound : m < k + 2 := by
          simpa [Pattern.zeroOnesZero] using hm
        have hmle : m <= n := by
          dsimp [k] at hmBound
          omega
        by_cases hm0 : m = 0
        · subst m
          simpa [Pattern.zeroOnesZero] using h0
        by_cases hmn : m = n
        · subst m
          change (false :: (List.replicate k true ++ [false]))[n] = bits n
          rw [hnFalse]
          have hnEq : n = k + 1 := by
            dsimp [k]
            omega
          simp only [hnEq]
          rw [List.getElem_cons_succ]
          simpa only [List.length_replicate] using
            (List.getElem_concat_length
              (l := List.replicate k true) (a := false) rfl (by simp))
        have hm1 : 1 <= m := by omega
        have hmlt : m < n := by omega
        have hmTrue : bits m = true := by
          by_cases hmEq1 : m = 1
          · simpa [hmEq1] using h1
          · have hm2 : 2 <= m := by omega
            by_contra hnot
            have hmFalse : bits m = false := by simpa using hnot
            exact (Nat.find_min hall hmlt) ⟨hm2, by simp [hmFalse]⟩
        have hindex : m - 1 < k := by omega
        change (false :: (List.replicate k true ++ [false]))[m] = bits m
        rw [hmTrue]
        cases m with
        | zero => exact (hm0 rfl).elim
        | succ q =>
            have hq : q < k := by simpa using hindex
            have hqRep : q < (List.replicate k true).length := by
              simpa using hq
            have hqApp : q < (List.replicate k true ++ [false]).length := by
              simp only [List.length_append, List.length_replicate,
                List.length_cons, List.length_nil]
              omega
            rw [List.getElem_cons_succ]
            calc
              (List.replicate k true ++ [false])[q]'hqApp =
                  (List.replicate k true)[q]'hqRep :=
                List.getElem_append_left hqRep
              _ = true := List.getElem_replicate hqRep

/-- A pattern beginning `00` is a finite or infinite zero block, unless it has
a forbidden prefix `0^k1`. -/
theorem zeroZero_shape {sigma : Pattern} (h00 : Pattern.zeroZero.IsPrefix sigma) :
    (∃ k, ∃ hk : 2 <= k, sigma = Pattern.zeros k hk) ∨
      sigma = Pattern.zerosInf ∨
      ∃ k, ∃ hk : 2 <= k, (Pattern.zerosOne k hk).IsPrefix sigma := by
  cases sigma with
  | finite bits hlen =>
      cases bits with
      | nil => simp at hlen
      | cons b0 tail =>
          cases tail with
          | nil => simp at hlen
          | cons b1 rest =>
              have hb0 : b0 = false := by
                simpa [Pattern.zeroZero, Pattern.bits2] using
                  h00.getElem (i := 0) (by decide)
              have hb1 : b1 = false := by
                simpa [Pattern.zeroZero, Pattern.bits2] using
                  h00.getElem (i := 1) (by decide)
              subst b0
              subst b1
              rcases boolList_false_run rest with hfalse | ⟨r, more, hr⟩
              · left
                refine ⟨rest.length + 2, by omega, ?_⟩
                congr 1
                calc
                  false :: false :: rest =
                      false :: false :: List.replicate rest.length false :=
                    congrArg (fun xs => false :: false :: xs) hfalse
                  _ = List.replicate (rest.length + 2) false := by
                    rw [show rest.length + 2 = (rest.length + 1) + 1 by omega,
                      List.replicate_succ, List.replicate_succ]
              · right; right
                refine ⟨r + 2, by omega, ?_⟩
                change (List.replicate (r + 2) false ++ [true]) <+:
                  false :: false :: rest
                rw [show r + 2 = (r + 1) + 1 by omega,
                  List.replicate_succ, List.replicate_succ, hr]
                simp
  | infinite bits =>
      have h0 : bits 0 = false := by
        simpa [Pattern.zeroZero, Pattern.bits2] using h00 0 (by decide)
      have h1 : bits 1 = false := by
        simpa [Pattern.zeroZero, Pattern.bits2] using h00 1 (by decide)
      by_cases hall : ∀ n, 2 <= n -> bits n = false
      · right; left
        congr 1
        funext n
        cases n with
        | zero => simpa [Pattern.zerosInf] using h0
        | succ n =>
            cases n with
            | zero => simpa [Pattern.zerosInf] using h1
            | succ n => simpa [Pattern.zerosInf] using hall (n + 2) (by omega)
      · push_neg at hall
        let n := Nat.find hall
        have hn2 : 2 <= n := (Nat.find_spec hall).1
        have hnTrue : bits n = true := by
          cases h : bits n
          · exact ((Nat.find_spec hall).2 h).elim
          · rfl
        right; right
        refine ⟨n, hn2, ?_⟩
        intro m hm
        have hmBound : m < n + 1 := by
          simpa [Pattern.zerosOne] using hm
        have hmle : m <= n := by
          omega
        by_cases hmn : m = n
        · subst m
          simpa [Pattern.zerosOne] using hnTrue.symm
        have hmlt : m < n := by omega
        have hmFalse : bits m = false := by
          by_cases hm0 : m = 0
          · simpa [hm0] using h0
          by_cases hm1 : m = 1
          · simpa [hm1] using h1
          · have hm2 : 2 <= m := by omega
            by_contra hnot
            have hmTrue : bits m = true := by simpa using hnot
            exact (Nat.find_min hall hmlt) ⟨hm2, by simp [hmTrue]⟩
        have hindex : m < n := hmlt
        simpa [Pattern.zerosOne, List.getElem_append, hindex,
          List.getElem_replicate] using hmFalse.symm

/-- A `10`-pattern either stops immediately, or its third bit is `0` or `1`. -/
theorem oneZero_shape {sigma : Pattern} (h10 : Pattern.oneZero.IsPrefix sigma) :
    sigma = Pattern.oneZero ∨
      (Pattern.bits3 true false false).IsPrefix sigma ∨
      (Pattern.bits3 true false true).IsPrefix sigma := by
  cases sigma with
  | finite bits hlen =>
      cases bits with
      | nil => simp at hlen
      | cons b0 tail =>
          cases tail with
          | nil => simp at hlen
          | cons b1 rest =>
              have hb0 : b0 = true := by
                simpa [Pattern.oneZero, Pattern.bits2] using
                  h10.getElem (i := 0) (by decide)
              have hb1 : b1 = false := by
                simpa [Pattern.oneZero, Pattern.bits2] using
                  h10.getElem (i := 1) (by decide)
              subst b0
              subst b1
              cases rest with
              | nil => left; rfl
              | cons b2 more =>
                  cases b2
                  · right; left
                    change [true, false, false] <+:
                      true :: false :: false :: more
                    simp
                  · right; right
                    change [true, false, true] <+:
                      true :: false :: true :: more
                    simp
  | infinite bits =>
      have h0 : bits 0 = true := by
        simpa [Pattern.oneZero, Pattern.bits2] using h10 0 (by decide)
      have h1 : bits 1 = false := by
        simpa [Pattern.oneZero, Pattern.bits2] using h10 1 (by decide)
      cases h2 : bits 2
      · right; left
        intro n hn
        have hn3 : n < 3 := by simpa using hn
        have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
        rcases this with rfl | rfl | rfl <;> simp [h0, h1, h2]
      · right; right
        intro n hn
        have hn3 : n < 3 := by simpa using hn
        have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
        rcases this with rfl | rfl | rfl <;> simp [h0, h1, h2]

/-! ## Exhaustive classification, abstracted over the nonexistence inputs -/

theorem k45_normalForm_of_admissible
    (hadm : Sigma.Admissible
      (Classes.K45 : FrameClass.{u} Atom Agent) sigma) :
    K45NormalForm (Classes.K45 : FrameClass.{u} Atom Agent) sigma := by
  rcases four_prefixes sigma with h00 | h01 | h10 | h11
  · apply K45NormalForm.zerosInf
    exact ⟨hadm, valEq_completion_of_admissible _ h00
      EquivalenceClasses.k45_zeroZero_valEq_zerosInf (by
        simpa [Pattern.zeroZero, Pattern.zerosInf] using
          (first_eq_of_prefix h00).symm) hadm⟩
  · rcases zeroOne_shape h01 with ⟨k, hk, rfl⟩ | rfl | ⟨k, hk, hp⟩
    · exact K45NormalForm.zeroOnes k hk ⟨hadm, Sigma.valEq_refl _ _⟩
    · exact K45NormalForm.zeroOnesInf ⟨hadm, Sigma.valEq_refl _ _⟩
    · exact (Nonexistence.k45_zeroOnesZero_not_admissible
        (Atom := Atom) (Agent := Agent) k hk (admissible_of_prefix _ hp hadm)).elim
  · apply K45NormalForm.oneZerosInf
    exact ⟨hadm, valEq_completion_of_admissible _ h10
      EquivalenceClasses.k45_oneZero_valEq_oneZerosInf (by
        simpa [Pattern.oneZero, Pattern.oneZerosInf] using
          (first_eq_of_prefix h10).symm) hadm⟩
  · apply K45NormalForm.onesInf
    exact ⟨hadm, valEq_completion_of_admissible _ h11
      (EquivalenceClasses.oneOne_valEq_onesInf _) (by
        simpa [Pattern.oneOne, Pattern.onesInf] using
          (first_eq_of_prefix h11).symm) hadm⟩

theorem k45_classification :
    Sigma.Admissible (Classes.K45 : FrameClass.{u} Atom Agent) sigma ↔
      K45NormalForm (Classes.K45 : FrameClass.{u} Atom Agent) sigma := by
  constructor
  · exact k45_normalForm_of_admissible
  · intro h
    cases h with
    | zerosInf h => exact h.1
    | zeroOnes _ _ h => exact h.1
    | zeroOnesInf h => exact h.1
    | oneZerosInf h => exact h.1
    | onesInf h => exact h.1

theorem single_kd45_normalForm_of_admissible
    (hadm : Sigma.Admissible
      (Classes.KD45 : FrameClass.{u} Atom Unit) sigma) :
    SingleKD45NormalForm
      (Classes.KD45 : FrameClass.{u} Atom Unit) sigma := by
  rcases four_prefixes sigma with h00 | h01 | h10 | h11
  · apply SingleKD45NormalForm.zerosInf
    exact ⟨hadm, valEq_completion_of_admissible _ h00
      EquivalenceClasses.single_kd45_zeroZero_valEq_zerosInf (by
        simpa [Pattern.zeroZero, Pattern.zerosInf] using
          (first_eq_of_prefix h00).symm) hadm⟩
  · rcases zeroOne_shape h01 with ⟨k, hk, rfl⟩ | rfl | ⟨k, hk, hp⟩
    · exact SingleKD45NormalForm.zeroOnes k hk ⟨hadm, Sigma.valEq_refl _ _⟩
    · exact SingleKD45NormalForm.zeroOnesInf ⟨hadm, Sigma.valEq_refl _ _⟩
    · exact (Nonexistence.single_kd45_zeroOnesZero_not_admissible
        (Atom := Atom) k hk (admissible_of_prefix _ hp hadm)).elim
  · rcases oneZero_shape h10 with rfl | h100 | h101
    · exact SingleKD45NormalForm.oneZero ⟨hadm, Sigma.valEq_refl _ _⟩
    · apply SingleKD45NormalForm.oneZerosInf
      exact ⟨hadm, valEq_completion_of_admissible _ h100
        (EquivalenceClasses.oneZeroZero_valEq_oneZerosInf _) (by
          simpa [Pattern.oneZerosInf] using
            (first_eq_of_prefix h100).symm) hadm⟩
    · apply SingleKD45NormalForm.oneZeroOnesInf
      exact ⟨hadm, valEq_completion_of_admissible _ h101
        (EquivalenceClasses.oneZeroOne_valEq_oneZeroOnesInf _) (by
          simpa [Pattern.oneZeroOnesInf] using
            (first_eq_of_prefix h101).symm) hadm⟩
  · apply SingleKD45NormalForm.onesInf
    exact ⟨hadm, valEq_completion_of_admissible _ h11
      (EquivalenceClasses.oneOne_valEq_onesInf _) (by
        simpa [Pattern.oneOne, Pattern.onesInf] using
          (first_eq_of_prefix h11).symm) hadm⟩

theorem single_kd45_classification :
    Sigma.Admissible (Classes.KD45 : FrameClass.{u} Atom Unit) sigma ↔
      SingleKD45NormalForm
        (Classes.KD45 : FrameClass.{u} Atom Unit) sigma := by
  constructor
  · exact single_kd45_normalForm_of_admissible
  · intro h
    cases h with
    | zerosInf h => exact h.1
    | zeroOnes _ _ h => exact h.1
    | zeroOnesInf h => exact h.1
    | oneZero h => exact h.1
    | oneZerosInf h => exact h.1
    | oneZeroOnesInf h => exact h.1
    | onesInf h => exact h.1

/-- Common exhaustive argument for S5 and multi-agent KD45. -/
theorem serial_normalForm_of_admissible
    (C : FrameClass.{u} Atom Agent)
    (hNoZerosOne : ∀ k (hk : 2 <= k),
      ¬ Sigma.Admissible C (Pattern.zerosOne k hk))
    (hNoZeroOnesZero : ∀ k (hk : 1 <= k),
      ¬ Sigma.Admissible C (Pattern.zeroOnesZero k hk))
    (hadm : Sigma.Admissible C sigma) : SerialNormalForm C sigma := by
  rcases four_prefixes sigma with h00 | h01 | h10 | h11
  · rcases zeroZero_shape h00 with ⟨k, hk, rfl⟩ | rfl | ⟨k, hk, hp⟩
    · exact SerialNormalForm.zeros k hk ⟨hadm, Sigma.valEq_refl _ _⟩
    · exact SerialNormalForm.zerosInf ⟨hadm, Sigma.valEq_refl _ _⟩
    · exact (hNoZerosOne k hk (admissible_of_prefix C hp hadm)).elim
  · rcases zeroOne_shape h01 with ⟨k, hk, rfl⟩ | rfl | ⟨k, hk, hp⟩
    · exact SerialNormalForm.zeroOnes k hk ⟨hadm, Sigma.valEq_refl _ _⟩
    · exact SerialNormalForm.zeroOnesInf ⟨hadm, Sigma.valEq_refl _ _⟩
    · exact (hNoZeroOnesZero k hk (admissible_of_prefix C hp hadm)).elim
  · rcases oneZero_shape h10 with rfl | h100 | h101
    · exact SerialNormalForm.oneZero ⟨hadm, Sigma.valEq_refl _ _⟩
    · apply SerialNormalForm.oneZerosInf
      exact ⟨hadm, valEq_completion_of_admissible C h100
        (EquivalenceClasses.oneZeroZero_valEq_oneZerosInf C) (by
          simpa [Pattern.oneZerosInf] using
            (first_eq_of_prefix h100).symm) hadm⟩
    · apply SerialNormalForm.oneZeroOnesInf
      exact ⟨hadm, valEq_completion_of_admissible C h101
        (EquivalenceClasses.oneZeroOne_valEq_oneZeroOnesInf C) (by
          simpa [Pattern.oneZeroOnesInf] using
            (first_eq_of_prefix h101).symm) hadm⟩
  · apply SerialNormalForm.onesInf
    exact ⟨hadm, valEq_completion_of_admissible C h11
      (EquivalenceClasses.oneOne_valEq_onesInf C) (by
        simpa [Pattern.oneOne, Pattern.onesInf] using
          (first_eq_of_prefix h11).symm) hadm⟩

theorem s5_classification :
    Sigma.Admissible (Classes.S5 : FrameClass.{u} Atom Agent) sigma ↔
      SerialNormalForm (Classes.S5 : FrameClass.{u} Atom Agent) sigma := by
  constructor
  · exact serial_normalForm_of_admissible _
      (Nonexistence.s5_zerosOne_not_admissible (Atom := Atom) (Agent := Agent))
      (Nonexistence.s5_zeroOnesZero_not_admissible
        (Atom := Atom) (Agent := Agent))
  · intro h
    cases h with
    | zerosInf h => exact h.1
    | zeros _ _ h => exact h.1
    | zeroOnes _ _ h => exact h.1
    | zeroOnesInf h => exact h.1
    | oneZero h => exact h.1
    | oneZerosInf h => exact h.1
    | oneZeroOnesInf h => exact h.1
    | onesInf h => exact h.1

/-- Multi-agent KD45 classification, stated with the two paper nonexistence
inputs exposed.  The concrete theorem below instantiates them with the
unravelling results. -/
theorem kd45_classification_of_nonexistence
    (hNoZerosOne : ∀ k (hk : 2 <= k),
      ¬ Sigma.Admissible
        (Classes.KD45 : FrameClass.{u} Atom Agent) (Pattern.zerosOne k hk))
    (hNoZeroOnesZero : ∀ k (hk : 1 <= k),
      ¬ Sigma.Admissible
        (Classes.KD45 : FrameClass.{u} Atom Agent) (Pattern.zeroOnesZero k hk)) :
    Sigma.Admissible (Classes.KD45 : FrameClass.{u} Atom Agent) sigma ↔
      SerialNormalForm (Classes.KD45 : FrameClass.{u} Atom Agent) sigma := by
  constructor
  · exact serial_normalForm_of_admissible _ hNoZerosOne hNoZeroOnesZero
  · intro h
    cases h with
    | zerosInf h => exact h.1
    | zeros _ _ h => exact h.1
    | zeroOnes _ _ h => exact h.1
    | zeroOnesInf h => exact h.1
    | oneZero h => exact h.1
    | oneZerosInf h => exact h.1
    | oneZeroOnesInf h => exact h.1
    | onesInf h => exact h.1

/-- The paper's multi-agent KD45 classification.  Each candidate formula is
renamed to its finite type of occurring agents before applying the finite
unravelling theorem, and one unused dummy agent handles formulas of modal
depth zero.  Thus the ambient type need not be finite.  Nonemptiness is needed
to interpret that dummy when restricting an ambient model.  Having two
distinct agents is not needed for exhaustiveness, but is needed to show that
every finite-zero representative is inhabited; see
`WellDefinedness.kd45_zeros`. -/
theorem kd45_classification [Nonempty Agent] :
    Sigma.Admissible
        (Classes.KD45 : FrameClass.{max u w} Atom Agent) sigma ↔
      SerialNormalForm
        (Classes.KD45 : FrameClass.{max u w} Atom Agent) sigma :=
  kd45_classification_of_nonexistence
    (AgentSupport.kd45_zerosOne_not_admissible
      (Atom := Atom) (Agent := Agent))
    (AgentSupport.kd45_zeroOnesZero_not_admissible
      (Atom := Atom) (Agent := Agent))

/-!
## Well-definedness and disjointness

The exhaustive theorems above deliberately quantify over the proposition and
agent types used by the class.  The paper additionally claims that every
displayed representative denotes a nonempty class and that the displayed
classes are pairwise different.  For the paper's countably infinite stock of
letters (`Atom := Nat`), the former claims are the theorems in namespace
`WellDefinedness`: modal representatives take an explicit agent, and the
multi-agent KD45 finite-zero family takes explicit `a b` and `a ≠ b`.

The latter claims are the explicit `Not (Sigma.ValEq ...)` theorems in
namespace `ClassificationDisjointness`.  Their hypotheses expose exactly the
separating formula's requirements (`Inhabited Atom`, a chosen agent, an
injective type-to-atom map, or two distinct agents).  Keeping these claims
separate avoids hiding the paper's nonemptiness assumptions inside the purely
exhaustive normal-form theorem.
-/

end Classification

end ClassificationSigmaValidity
