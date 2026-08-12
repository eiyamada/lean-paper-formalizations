import ClassificationSigmaValidity.Patterns

/-!
# Elementary lemmas about finite and infinite truth patterns
-/

namespace ClassificationSigmaValidity

namespace Pattern

@[simp] theorem finitePrefix_first (bits : Nat -> Bool) (n : Nat) (hn : 2 <= n) :
    (finitePrefix bits n hn).first = bits 0 := by
  simp [finitePrefix, first]

theorem finitePrefix_isPrefix (bits : Nat -> Bool) (n : Nat) (hn : 2 <= n) :
    (finitePrefix bits n hn).IsPrefix (.infinite bits) := by
  intro j hj
  simp

theorem realizesTrace_mono_of_prefix {trace : Nat -> Prop} {tau sigma : Pattern}
    (hp : tau.IsPrefix sigma) (h : sigma.RealizesTrace trace) :
    tau.RealizesTrace trace := by
  cases tau with
  | finite xs hxs =>
      cases sigma with
      | finite ys hys =>
          intro n hn
          have hlen : xs.length <= ys.length := List.IsPrefix.length_le hp
          have hny : n < ys.length := Nat.lt_of_lt_of_le hn hlen
          have hget : xs[n] = ys[n] := hp.getElem hn
          rw [hget]
          exact h n hny
      | infinite ys =>
          intro n hn
          rw [hp n hn]
          exact h n
  | infinite xs =>
      cases sigma with
      | finite ys hys => exact hp.elim
      | infinite ys =>
          subst ys
          exact h

/-- The direct all-coordinate semantics for an infinite pattern is equivalent
to realizing every finite prefix, as in the paper's definition. -/
theorem realizesTrace_infinite_iff_all_finitePrefixes
    (trace : Nat -> Prop) (bits : Nat -> Bool) :
    RealizesTrace trace (.infinite bits) <->
      forall n (hn : 2 <= n), RealizesTrace trace (finitePrefix bits n hn) := by
  constructor
  · intro h n hn
    exact realizesTrace_mono_of_prefix (finitePrefix_isPrefix bits n hn) h
  · intro h j
    have hj : j < (List.ofFn fun i : Fin (j + 2) => bits i).length := by
      simp only [List.length_ofFn]
      omega
    have hp := h (j + 2) (by omega) j hj
    change HoldsBit
      (List.ofFn (fun i : Fin (j + 2) => bits i))[j] (trace j) at hp
    rw [List.getElem_ofFn] at hp
    exact hp

theorem holdsBit_iff_eq {P : Prop} {b : Bool} :
    HoldsBit b P <-> (P <-> b = true) := by
  cases b <;> simp [HoldsBit]

/-- If one trace realizes two patterns and one of the patterns is valid from
its first bit, their first bits agree. -/
theorem first_eq_of_common_realization {trace : Nat -> Prop} {sigma tau : Pattern}
    (hs : sigma.RealizesTrace trace) (ht : tau.RealizesTrace trace) :
    sigma.first = tau.first := by
  have hs0 := realizesTrace_first hs
  have ht0 := realizesTrace_first ht
  cases hsig : sigma.first <;> cases htau : tau.first
  · rfl
  · have hs0' : Not (trace 0) := by simpa [hsig, HoldsBit] using hs0
    have ht0' : trace 0 := by simpa [htau, HoldsBit] using ht0
    exact (hs0' ht0').elim
  · have hs0' : trace 0 := by simpa [hsig, HoldsBit] using hs0
    have ht0' : Not (trace 0) := by simpa [htau, HoldsBit] using ht0
    exact (ht0' hs0').elim
  · rfl

end Pattern

namespace Sigma

universe u v w

variable {Atom : Type v} {Agent : Type w}

/-- Validity is inherited by a prefix. -/
theorem valid_of_prefix (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent)
    {tau sigma : Pattern} (hp : tau.IsPrefix sigma)
    (h : Valid C phi sigma) : Valid C phi tau := by
  intro World M hM x hx
  have hfirst : tau.first = sigma.first := by
    cases tau with
    | finite xs hxs =>
        cases sigma with
        | finite ys hys =>
            have h0x : 0 < xs.length := Nat.lt_of_lt_of_le (by decide) hxs
            have hlen : xs.length <= ys.length := List.IsPrefix.length_le hp
            have h0y : 0 < ys.length := Nat.lt_of_lt_of_le h0x hlen
            simp [Pattern.first]
            exact hp.getElem h0x
        | infinite ys =>
            have h0 : 0 < xs.length := Nat.lt_of_lt_of_le (by decide) hxs
            simpa [Pattern.first] using hp 0 h0
    | infinite xs =>
        cases sigma with
        | finite ys hys => exact hp.elim
        | infinite ys =>
            have hfun : xs = ys := hp
            exact congrFun hfun 0
  have hsigma := h M hM x (by simpa [hfirst] using hx)
  exact Pattern.realizesTrace_mono_of_prefix hp hsigma

/-- Satisfiability is inherited by a prefix. -/
theorem satisfiable_of_prefix (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent)
    {tau sigma : Pattern} (hp : tau.IsPrefix sigma)
    (h : Satisfiable C phi sigma) : Satisfiable C phi tau := by
  rcases h with ⟨World, M, hM, x, hx⟩
  exact ⟨World, M, hM, x, Pattern.realizesTrace_mono_of_prefix hp hx⟩

/-- The paper defines infinite sigma-validity as validity of every finite
prefix.  This theorem proves that formulation equivalent to the direct
all-coordinate definition used by `Sigma.Valid`. -/
theorem valid_infinite_iff_all_finitePrefixes
    (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent)
    (bits : Nat -> Bool) :
    Valid C phi (.infinite bits) <->
      forall n (hn : 2 <= n), Valid C phi (Pattern.finitePrefix bits n hn) := by
  constructor
  · intro h n hn
    exact valid_of_prefix C phi (Pattern.finitePrefix_isPrefix bits n hn) h
  · intro h World M hM x hx
    apply (Pattern.realizesTrace_infinite_iff_all_finitePrefixes
      (M.trace x phi) bits).2
    intro n hn
    apply h n hn M hM x
    simpa using hx

end Sigma

end ClassificationSigmaValidity
