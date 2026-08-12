import ClassificationSigmaValidity.Frames

/-!
# Finite and infinite sigma-patterns

This file formalizes Definition `def:sigma_satisfiable_and_valid` and the four
length-two notions (success, self-refutation, true lies, and impossible lies).
-/

namespace ClassificationSigmaValidity

universe u v w

/-- A class of Kripke models, uniformly over state types in one universe. -/
abbrev FrameClass (Atom : Type v) (Agent : Type w) :=
  {World : Type u} -> Model World Atom Agent -> Prop

/-- A sigma is either a finite bit string of length at least two, or an infinite
bit stream. -/
inductive Pattern where
  | finite (bits : List Bool) (length_ge_two : 2 <= bits.length)
  | infinite (bits : Nat -> Bool)

namespace Pattern

/-- A proposition has the truth value represented by a bit. -/
def HoldsBit (b : Bool) (P : Prop) : Prop := if b then P else Not P

@[simp] theorem holdsBit_true (P : Prop) : HoldsBit true P <-> P := by
  simp [HoldsBit]

@[simp] theorem holdsBit_false (P : Prop) : HoldsBit false P <-> Not P := by
  simp [HoldsBit]

/-- The pattern prescribes bit `b` at time `n` (when that time lies in its
domain). -/
def HoldsAt (sigma : Pattern) (n : Nat) (P : Prop) : Prop :=
  match sigma with
  | .finite bits _ => forall h : n < bits.length, HoldsBit bits[n] P
  | .infinite bits => HoldsBit (bits n) P

/-- The first bit.  It exists because finite patterns have length at least two. -/
def first : Pattern -> Bool
  | .finite bits h => bits[0]'(Nat.lt_of_lt_of_le (by decide) h)
  | .infinite bits => bits 0

/-- A trace realizes every prescribed bit of a pattern. -/
def RealizesTrace (trace : Nat -> Prop) : Pattern -> Prop
  | .finite bits _ => forall n (hn : n < bits.length), HoldsBit bits[n] (trace n)
  | .infinite bits => forall n, HoldsBit (bits n) (trace n)

theorem realizesTrace_first {trace : Nat -> Prop} {sigma : Pattern}
    (h : RealizesTrace trace sigma) : HoldsBit sigma.first (trace 0) := by
  cases sigma with
  | finite bits hlen =>
      simpa [RealizesTrace, first] using h 0 (Nat.lt_of_lt_of_le (by decide) hlen)
  | infinite bits => simpa [RealizesTrace, first] using h 0

/-- `prefix tau sigma` means that every position prescribed by `tau` has the
same bit in `sigma`. -/
def IsPrefix : Pattern -> Pattern -> Prop
  | .finite xs _, .finite ys _ => xs <+: ys
  | .finite xs _, .infinite ys => forall n (hn : n < xs.length), xs[n] = ys n
  | .infinite xs, .infinite ys => xs = ys
  | .infinite _, .finite _ _ => False

/-- A finite all-zero pattern. -/
def zeros (n : Nat) (h : 2 <= n) : Pattern := .finite (List.replicate n false) (by simp [h])

/-- A finite all-one pattern. -/
def ones (n : Nat) (h : 2 <= n) : Pattern := .finite (List.replicate n true) (by simp [h])

/-- `0 1^k`, where `k >= 1`. -/
def zeroOnes (k : Nat) (h : 1 <= k) : Pattern :=
  .finite (false :: List.replicate k true) (by simp; omega)

/-- `1 0^k`, where `k >= 1`. -/
def oneZeros (k : Nat) (h : 1 <= k) : Pattern :=
  .finite (true :: List.replicate k false) (by simp; omega)

/-- The constant-zero infinite pattern. -/
def zerosInf : Pattern := .infinite fun _ => false

/-- The constant-one infinite pattern. -/
def onesInf : Pattern := .infinite fun _ => true

/-- `0 1^omega`. -/
def zeroOnesInf : Pattern := .infinite fun n => n != 0

/-- `1 0^omega`. -/
def oneZerosInf : Pattern := .infinite fun n => n = 0

/-- `1 0 1^omega`. -/
def oneZeroOnesInf : Pattern := .infinite fun n => n != 1

/-- The finite prefix of length `k + 1` given by `0 1^k`. -/
def zeroOnesNat (k : Nat) (hk : 1 <= k) : Pattern := zeroOnes k hk

/-- The finite prefix of length `k + 1` given by `1 0^k`. -/
def oneZerosNat (k : Nat) (hk : 1 <= k) : Pattern := oneZeros k hk

/-- `0^k 1`, used by the nonexistence lemmas (`k >= 2`). -/
def zerosOne (k : Nat) (hk : 2 <= k) : Pattern :=
  .finite (List.replicate k false ++ [true]) (by simp; omega)

/-- `0 1^k 0`, used by the nonexistence lemmas (`k >= 1`). -/
def zeroOnesZero (k : Nat) (_hk : 1 <= k) : Pattern :=
  .finite (false :: List.replicate k true ++ [false]) (by simp)

/-- A pattern consisting of exactly two bits. -/
def bits2 (b0 b1 : Bool) : Pattern := .finite [b0, b1] (by simp)

/-- A pattern consisting of exactly three bits. -/
def bits3 (b0 b1 b2 : Bool) : Pattern := .finite [b0, b1, b2] (by simp)

/-- The length-`n` prefix of an infinite bit stream.  This is the finite
pattern used in the paper's definition of infinite sigma-validity. -/
def finitePrefix (bits : Nat -> Bool) (n : Nat) (hn : 2 <= n) : Pattern :=
  .finite (List.ofFn fun i : Fin n => bits i) (by simpa using hn)

def zeroZero : Pattern := bits2 false false
def zeroOne : Pattern := bits2 false true
def oneZero : Pattern := bits2 true false
def oneOne : Pattern := bits2 true true

@[simp] theorem first_bits2 (b0 b1 : Bool) : (bits2 b0 b1).first = b0 := by
  simp [bits2, first]

@[simp] theorem first_bits3 (b0 b1 b2 : Bool) : (bits3 b0 b1 b2).first = b0 := by
  simp [bits3, first]

theorem realizesTrace_bits2 {trace : Nat -> Prop} {b0 b1 : Bool} :
    RealizesTrace trace (bits2 b0 b1) <->
      HoldsBit b0 (trace 0) /\ HoldsBit b1 (trace 1) := by
  constructor
  · intro h
    exact ⟨by simpa [bits2, RealizesTrace] using h 0 (by simp),
      by simpa [bits2, RealizesTrace] using h 1 (by simp)⟩
  · rintro ⟨h0, h1⟩ n hn
    have hn2 : n < 2 := by simpa [bits2] using hn
    have hn' : n = 0 \/ n = 1 := by omega
    rcases hn' with rfl | rfl
    · simpa [bits2, RealizesTrace] using h0
    · simpa [bits2, RealizesTrace] using h1

theorem realizesTrace_bits3 {trace : Nat -> Prop} {b0 b1 b2 : Bool} :
    RealizesTrace trace (bits3 b0 b1 b2) <->
      HoldsBit b0 (trace 0) /\ HoldsBit b1 (trace 1) /\ HoldsBit b2 (trace 2) := by
  constructor
  · intro h
    exact ⟨by simpa [bits3, RealizesTrace] using h 0 (by simp),
      by simpa [bits3, RealizesTrace] using h 1 (by simp),
      by simpa [bits3, RealizesTrace] using h 2 (by simp)⟩
  · rintro ⟨h0, h1, h2⟩ n hn
    have hn3 : n < 3 := by simpa [bits3] using hn
    have hn' : n = 0 \/ n = 1 \/ n = 2 := by omega
    rcases hn' with rfl | rfl | rfl
    · simpa [bits3, RealizesTrace] using h0
    · simpa [bits3, RealizesTrace] using h1
    · simpa [bits3, RealizesTrace] using h2

end Pattern

namespace Sigma

variable {Atom : Type v} {Agent : Type w}

/-- A pointed model realizes a sigma under iterated announcements. -/
def Realizes {World : Type u} (M : Model World Atom Agent) (x : World)
    (phi : Formula Atom Agent) (sigma : Pattern) : Prop :=
  sigma.RealizesTrace (M.trace x phi)

/-- Sigma-validity over a specified frame class. -/
def Valid (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent)
    (sigma : Pattern) : Prop :=
  forall {World : Type u} (M : Model World Atom Agent), C M -> forall x,
    Pattern.HoldsBit sigma.first (M.trace x phi 0) -> Realizes M x phi sigma

/-- Paper-facing variant of validity whose model carriers are explicitly
nonempty. -/
def ValidOnNonemptyModels (C : FrameClass.{u} Atom Agent)
    (phi : Formula Atom Agent) (sigma : Pattern) : Prop :=
  forall {World : Type u} [Nonempty World] (M : Model World Atom Agent),
    C M -> forall x,
      Pattern.HoldsBit sigma.first (M.trace x phi 0) -> Realizes M x phi sigma

/-- Allowing an empty carrier in the Lean structure does not change validity:
an empty model has no pointed states, while any supplied point itself gives a
`Nonempty` instance. -/
theorem valid_iff_validOnNonemptyModels
    (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent)
    (sigma : Pattern) :
    Valid C phi sigma <-> ValidOnNonemptyModels C phi sigma := by
  constructor
  · intro h World _ M hM x hx
    exact h M hM x hx
  · intro h World M hM x hx
    letI : Nonempty World := ⟨x⟩
    exact h M hM x hx

/-- Sigma-satisfiability over a specified frame class. -/
def Satisfiable (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent)
    (sigma : Pattern) : Prop :=
  exists (World : Type u) (M : Model World Atom Agent), C M /\
    exists x : World, Realizes M x phi sigma

/-- Non-trivial sigma-validity is validity plus satisfiability. -/
def NontriviallyValid (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent)
    (sigma : Pattern) : Prop :=
  Valid C phi sigma /\ Satisfiable C phi sigma

/-- The set `S` from the paper. -/
def Admissible (C : FrameClass.{u} Atom Agent) (sigma : Pattern) : Prop :=
  exists phi : Formula Atom Agent, NontriviallyValid C phi sigma

/-- Equality of the paper's sets `Val(sigma)` and `Val(tau)`. -/
def ValEq (C : FrameClass.{u} Atom Agent) (sigma tau : Pattern) : Prop :=
  forall phi : Formula Atom Agent, Valid C phi sigma <-> Valid C phi tau

theorem valEq_refl (C : FrameClass.{u} Atom Agent) (sigma : Pattern) :
    ValEq C sigma sigma := fun _ => Iff.rfl

theorem valEq_symm (C : FrameClass.{u} Atom Agent) {sigma tau : Pattern}
    (h : ValEq C sigma tau) : ValEq C tau sigma := fun phi => (h phi).symm

theorem valEq_trans (C : FrameClass.{u} Atom Agent) {sigma tau rho : Pattern}
    (h1 : ValEq C sigma tau) (h2 : ValEq C tau rho) : ValEq C sigma rho :=
  fun phi => (h1 phi).trans (h2 phi)

/-- Successful formulas. -/
def Successful (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent) : Prop :=
  forall {World : Type u} (M : Model World Atom Agent), C M -> forall x,
    M.Satisfies x phi -> (M.update phi).Satisfies x phi

/-- Self-refuting formulas. -/
def SelfRefuting (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent) : Prop :=
  forall {World : Type u} (M : Model World Atom Agent), C M -> forall x,
    M.Satisfies x phi -> Not ((M.update phi).Satisfies x phi)

/-- True lies. -/
def TrueLie (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent) : Prop :=
  forall {World : Type u} (M : Model World Atom Agent), C M -> forall x,
    Not (M.Satisfies x phi) -> (M.update phi).Satisfies x phi

/-- Impossible lies. -/
def ImpossibleLie (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent) : Prop :=
  forall {World : Type u} (M : Model World Atom Agent), C M -> forall x,
    Not (M.Satisfies x phi) -> Not ((M.update phi).Satisfies x phi)

theorem realizes_bits2_iff {World : Type u} (M : Model World Atom Agent) (x : World)
    (phi : Formula Atom Agent) (b0 b1 : Bool) :
    Realizes M x phi (Pattern.bits2 b0 b1) <->
      Pattern.HoldsBit b0 (M.Satisfies x phi) /\
        Pattern.HoldsBit b1 ((M.update phi).Satisfies x phi) := by
  simpa [Realizes, Model.trace] using
    (Pattern.realizesTrace_bits2 (trace := M.trace x phi) (b0 := b0) (b1 := b1))

/-- The paper's observation that `11`-validity is success. -/
theorem valid_oneOne_iff_successful
    (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent) :
    Valid C phi Pattern.oneOne <-> Successful C phi := by
  constructor
  · intro h World M hM x hx
    have hr := h M hM x (by simpa [Pattern.oneOne] using hx)
    exact (realizes_bits2_iff M x phi true true).mp hr |>.2
  · intro h World M hM x hx
    apply (realizes_bits2_iff M x phi true true).mpr
    exact ⟨by simpa [Pattern.oneOne] using hx, h M hM x (by simpa [Pattern.oneOne] using hx)⟩

/-- The paper's observation that `10`-validity is self-refutation. -/
theorem valid_oneZero_iff_selfRefuting
    (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent) :
    Valid C phi Pattern.oneZero <-> SelfRefuting C phi := by
  constructor
  · intro h World M hM x hx
    have hr := h M hM x (by simpa [Pattern.oneZero] using hx)
    exact (realizes_bits2_iff M x phi true false).mp hr |>.2
  · intro h World M hM x hx
    apply (realizes_bits2_iff M x phi true false).mpr
    exact ⟨by simpa [Pattern.oneZero] using hx,
      h M hM x (by simpa [Pattern.oneZero] using hx)⟩

/-- The paper's observation that `01`-validity is being a true lie. -/
theorem valid_zeroOne_iff_trueLie
    (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent) :
    Valid C phi Pattern.zeroOne <-> TrueLie C phi := by
  constructor
  · intro h World M hM x hx
    have hr := h M hM x (by simpa [Pattern.zeroOne] using hx)
    exact (realizes_bits2_iff M x phi false true).mp hr |>.2
  · intro h World M hM x hx
    apply (realizes_bits2_iff M x phi false true).mpr
    exact ⟨by simpa [Pattern.zeroOne] using hx,
      h M hM x (by simpa [Pattern.zeroOne] using hx)⟩

/-- The paper's observation that `00`-validity is being an impossible lie. -/
theorem valid_zeroZero_iff_impossibleLie
    (C : FrameClass.{u} Atom Agent) (phi : Formula Atom Agent) :
    Valid C phi Pattern.zeroZero <-> ImpossibleLie C phi := by
  constructor
  · intro h World M hM x hx
    have hr := h M hM x (by simpa [Pattern.zeroZero] using hx)
    exact (realizes_bits2_iff M x phi false false).mp hr |>.2
  · intro h World M hM x hx
    apply (realizes_bits2_iff M x phi false false).mpr
    exact ⟨by simpa [Pattern.zeroZero] using hx,
      h M hM x (by simpa [Pattern.zeroZero] using hx)⟩

end Sigma

end ClassificationSigmaValidity
