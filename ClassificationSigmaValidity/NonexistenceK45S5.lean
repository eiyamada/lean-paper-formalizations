import ClassificationSigmaValidity.Locality
import ClassificationSigmaValidity.FiniteDynamics
import ClassificationSigmaValidity.FrameClass
import ClassificationSigmaValidity.FiniteModelProperty

/-!
# Finite-model nonexistence for `0^k 1` and `0 1^k 0`

This file formalizes the finite combinatorial core of the paper's two
nonexistence lemmas.  No finite-model property is assumed: the main results
say directly that a pattern-valid formula has no counterexample on a finite
model of the indicated frame class.  Consequently, a pattern-valid formula
cannot have a finite realization of the pattern.
-/

namespace ClassificationSigmaValidity

universe u v w

namespace Pattern

@[simp] theorem first_zerosOne (k : Nat) (hk : 2 <= k) :
    (zerosOne k hk).first = false := by
  have hpos : 0 < k := by omega
  simp [zerosOne, first, hpos]

/-- The final two prescribed values of `0^k 1`. -/
theorem realizesTrace_zerosOne_last {trace : Nat -> Prop} {k : Nat}
    (hk : 2 <= k) (h : RealizesTrace trace (zerosOne k hk)) :
    Not (trace (k - 1)) /\ trace k := by
  constructor
  · have hlast := h (k - 1) (by simp; omega)
    have hnot : ¬ k ≤ k - 1 := by omega
    simpa [zerosOne, HoldsBit, List.getElem_append, List.getElem_replicate,
      hnot] using hlast
  · have hfinal := h k (by simp)
    simpa [zerosOne, HoldsBit, List.getElem_append, List.getElem_replicate] using hfinal

/-- The initial value and final change prescribed by `0 1^k 0`. -/
theorem realizesTrace_zeroOnesZero_ends {trace : Nat -> Prop} {k : Nat}
    (hk : 1 <= k) (h : RealizesTrace trace (zeroOnesZero k hk)) :
    Not (trace 0) /\ trace k /\ Not (trace (k + 1)) := by
  cases k with
  | zero => omega
  | succ k =>
      constructor
      · have hzero := h 0 (by simp)
        simpa [zeroOnesZero, HoldsBit] using hzero
      constructor
      · have hkth := h (k + 1) (by simp)
        simpa [zeroOnesZero, HoldsBit, List.getElem_append,
          List.getElem_replicate] using hkth
      · have hfinal := h (k + 1 + 1) (by simp)
        simpa [zeroOnesZero, HoldsBit, List.getElem_append,
          List.getElem_replicate, Nat.add_assoc] using hfinal

/-- The first post-announcement value prescribed by `0 1^k 0`. -/
theorem realizesTrace_zeroOnesZero_one {trace : Nat -> Prop} {k : Nat}
    (hk : 1 <= k) (h : RealizesTrace trace (zeroOnesZero k hk)) : trace 1 := by
  cases k with
  | zero => omega
  | succ k =>
      have hone := h 1 (by simp)
      simpa [zeroOnesZero, HoldsBit, List.getElem_append,
        List.getElem_replicate] using hone

end Pattern

namespace Sigma

variable {Atom : Type v} {Agent : Type w}

/-- Sigma-satisfiability with an explicitly finite witness model.  This is
kept separate from `Satisfiable`, since no finite-model property is assumed in
the development. -/
def FinitelySatisfiable (C : FrameClass.{u} Atom Agent)
    (phi : Formula Atom Agent) (sigma : Pattern) : Prop :=
  exists (World : Type u) (_ : Finite World) (M : Model World Atom Agent),
    C M /\ exists x : World, Realizes M x phi sigma

/-- The finite-witness version of non-trivial sigma-validity. -/
def FinitelyNontriviallyValid (C : FrameClass.{u} Atom Agent)
    (phi : Formula Atom Agent) (sigma : Pattern) : Prop :=
  Valid C phi sigma /\ FinitelySatisfiable C phi sigma

/-- The finite-witness version of membership in the paper's admissible set. -/
def FinitelyAdmissible (C : FrameClass.{u} Atom Agent) (sigma : Pattern) : Prop :=
  exists phi : Formula Atom Agent, FinitelyNontriviallyValid C phi sigma

end Sigma

namespace Nonexistence

open Pattern Sigma

variable {Atom : Type v} {Agent : Type w}

/-- At a dead end, the truth of every modal formula depends only on the
valuation at that point. -/
theorem satisfies_iff_of_deadEnd
    {World : Type u} (M N : Model World Atom Agent) (x : World)
    (hval : forall p, M.val p x <-> N.val p x)
    (hM : forall i y, Not (M.rel i x y))
    (hN : forall i y, Not (N.rel i x y))
    (psi : Formula Atom Agent) :
    M.Satisfies x psi <-> N.Satisfies x psi := by
  induction psi with
  | atom p => exact hval p
  | neg psi ih => exact not_congr ih
  | conj psi chi ihPsi ihChi => exact and_congr ihPsi ihChi
  | box i psi ih =>
      constructor
      · intro _ y hxy
        exact (hN i y hxy).elim
      · intro _ y hxy
        exact (hM i y hxy).elim

/-- Once a point has no outgoing arrows, repeated believed announcements do
not change the truth of any formula there. -/
theorem iterateUpdate_satisfies_iff_of_deadEnd
    {World : Type u} (M : Model World Atom Agent) (x : World)
    (hdead : forall i y, Not (M.rel i x y))
    (phi psi : Formula Atom Agent) (n : Nat) :
    (M.iterateUpdate phi n).Satisfies x psi <-> M.Satisfies x psi := by
  apply satisfies_iff_of_deadEnd (M.iterateUpdate phi n) M x
  · intro p
    exact M.iterateUpdate_val phi n p x
  · intro i y hxy
    exact hdead i y ((M.iterateUpdate_rel_iff phi n i x y).mp hxy).1
  · exact hdead

/-- A finite decreasing survivor sequence cannot have a nonempty drop every
`a` steps forever. -/
theorem no_finite_periodic_drops
    {World : Type u} [Finite World] (M : Model World Atom Agent)
    (phi : Formula Atom Agent) (a : Nat) (ha : 0 < a)
    (hfirst : (M.dropSet phi a).Nonempty)
    (hnext : forall t, (M.dropSet phi t).Nonempty ->
      (M.dropSet phi (t + a)).Nonempty) : False := by
  have hdrops : forall r : Nat,
      (M.dropSet phi (a + r * a)).Nonempty := by
    intro r
    induction r with
    | zero => simpa using hfirst
    | succ r ihr =>
        have := hnext (a + r * a) ihr
        simpa [Nat.succ_mul, Nat.add_assoc] using this
  obtain ⟨n, hconst⟩ := M.exists_survivorSet_eventually_constant phi
  let t := a + n * a
  have hnt : n <= t := by
    have hmul : n + 1 <= (n + 1) * a :=
      Nat.le_mul_of_pos_right (n + 1) ha
    have hshape : t = (n + 1) * a := by
      simp [t, Nat.succ_mul, Nat.add_comm]
    rw [hshape]
    exact Nat.le_trans (Nat.le_succ n) hmul
  obtain ⟨y, hyt, hynext⟩ := hdrops n
  have hyN : y ∈ M.survivorSet phi n := by
    rw [← hconst t hnt]
    exact hyt
  apply hynext
  rw [hconst (t + 1) (Nat.le_trans hnt (Nat.le_add_right t 1))]
  exact hyN

/-- In an S5 run, `0^k1`-validity propagates every drop `k-1` stages
forward.  The restriction to the current survivor set is again S5, and the
restriction/update shift theorem identifies its local run with the original
run at the later time. -/
theorem s5_zerosOne_drop_next
    {World : Type u} (M : Model World Atom Agent) (hM : IsS5 M)
    (phi : Formula Atom Agent) (k : Nat) (hk : 2 <= k)
    (hvalid : Sigma.Valid
      (Classes.S5 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent) phi
      (Pattern.zerosOne k hk)) (t : Nat)
    (hdrop : (M.dropSet phi t).Nonempty) :
    (M.dropSet phi (t + (k - 1))).Nonempty := by
  obtain ⟨y, hy⟩ := hdrop
  have hydata := (M.mem_dropSet_iff phi t y).mp hy
  let U := M.survivalSet phi t
  let yU : Subtype U := ⟨y, hydata.1⟩
  have hlocalFalse0 : Not ((M.restrict U).Satisfies yU phi) := by
    intro hlocal
    apply hydata.2
    have hshift :=
      (M.restrict_survivalSet_shift_satisfies_iff phi t 0 yU phi).mp hlocal
    simpa [U] using hshift
  have hstart : Pattern.HoldsBit (Pattern.zerosOne k hk).first
      ((M.restrict U).trace yU phi 0) := by
    simpa [Pattern.HoldsBit, Model.trace]
      using hlocalFalse0
  have hreal := hvalid (M.restrict U) (M.restrict_isS5 hM U) yU hstart
  have hlast := Pattern.realizesTrace_zerosOne_last hk hreal
  have hglobalFalse :
      Not ((M.iterateUpdate phi (t + (k - 1))).Satisfies y phi) := by
    intro hglobal
    apply hlast.1
    exact (M.restrict_survivalSet_shift_satisfies_iff
      phi t (k - 1) yU phi).mpr hglobal
  have hglobalTrue : (M.iterateUpdate phi (t + k)).Satisfies y phi :=
    (M.restrict_survivalSet_shift_satisfies_iff phi t k yU phi).mp hlast.2
  have hnextTrue :
      (M.iterateUpdate phi ((t + (k - 1)) + 1)).Satisfies y phi := by
    have hidx : (t + (k - 1)) + 1 = t + k := by omega
    rw [hidx]
    exact hglobalTrue
  apply M.dropSet_nonempty_of_satisfaction_change phi y phi
  intro hiff
  exact hglobalFalse (hiff.mpr hnextTrue)

/-- In an S5 run, `01^k0`-validity propagates every drop `k` stages
forward. -/
theorem s5_zeroOnesZero_drop_next
    {World : Type u} (M : Model World Atom Agent) (hM : IsS5 M)
    (phi : Formula Atom Agent) (k : Nat) (hk : 1 <= k)
    (hvalid : Sigma.Valid
      (Classes.S5 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent) phi
      (Pattern.zeroOnesZero k hk)) (t : Nat)
    (hdrop : (M.dropSet phi t).Nonempty) :
    (M.dropSet phi (t + k)).Nonempty := by
  obtain ⟨y, hy⟩ := hdrop
  have hydata := (M.mem_dropSet_iff phi t y).mp hy
  let U := M.survivalSet phi t
  let yU : Subtype U := ⟨y, hydata.1⟩
  have hlocalFalse0 : Not ((M.restrict U).Satisfies yU phi) := by
    intro hlocal
    apply hydata.2
    have hshift :=
      (M.restrict_survivalSet_shift_satisfies_iff phi t 0 yU phi).mp hlocal
    simpa [U] using hshift
  have hstart : Pattern.HoldsBit (Pattern.zeroOnesZero k hk).first
      ((M.restrict U).trace yU phi 0) := by
    simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit, Model.trace]
      using hlocalFalse0
  have hreal := hvalid (M.restrict U) (M.restrict_isS5 hM U) yU hstart
  have hends := Pattern.realizesTrace_zeroOnesZero_ends hk hreal
  have hglobalTrue : (M.iterateUpdate phi (t + k)).Satisfies y phi :=
    (M.restrict_survivalSet_shift_satisfies_iff phi t k yU phi).mp hends.2.1
  have hglobalFalse :
      Not ((M.iterateUpdate phi (t + (k + 1))).Satisfies y phi) := by
    intro hglobal
    apply hends.2.2
    exact (M.restrict_survivalSet_shift_satisfies_iff
      phi t (k + 1) yU phi).mpr hglobal
  have hnextFalse :
      Not ((M.iterateUpdate phi ((t + k) + 1)).Satisfies y phi) := by
    simpa [Nat.add_assoc] using hglobalFalse
  apply M.dropSet_nonempty_of_satisfaction_change phi y phi
  intro hiff
  exact hnextFalse (hiff.mp hglobalTrue)

/-- Finite-model core of the paper's nonexistence of `0^k1` validity on S5.
Every `0^k1`-valid formula is true at every point of every finite S5 model. -/
theorem finite_s5_valid_zerosOne_true
    {World : Type u} [Finite World] (M : Model World Atom Agent)
    (hM : IsS5 M) (phi : Formula Atom Agent) (k : Nat) (hk : 2 <= k)
    (hvalid : Sigma.Valid
      (Classes.S5 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent) phi
      (Pattern.zerosOne k hk)) (x : World) :
    M.Satisfies x phi := by
  by_contra hx
  have hstart : Pattern.HoldsBit (Pattern.zerosOne k hk).first
      (M.trace x phi 0) := by
    simpa [Pattern.HoldsBit, Model.trace] using hx
  have hreal := hvalid M hM x hstart
  have hlast := Pattern.realizesTrace_zerosOne_last hk hreal
  have hnextTrue : (M.iterateUpdate phi ((k - 1) + 1)).Satisfies x phi := by
    have hidx : (k - 1) + 1 = k := by omega
    rw [hidx]
    exact hlast.2
  have hfirst : (M.dropSet phi (k - 1)).Nonempty := by
    apply M.dropSet_nonempty_of_satisfaction_change phi x phi
    intro hiff
    exact hlast.1 (hiff.mpr hnextTrue)
  exact no_finite_periodic_drops M phi (k - 1) (by omega) hfirst
    (fun t ht => s5_zerosOne_drop_next M hM phi k hk hvalid t ht)

/-- Finite-model core of the paper's S5 `01^k0` nonexistence lemma. -/
theorem finite_s5_valid_zeroOnesZero_true
    {World : Type u} [Finite World] (M : Model World Atom Agent)
    (hM : IsS5 M) (phi : Formula Atom Agent) (k : Nat) (hk : 1 <= k)
    (hvalid : Sigma.Valid
      (Classes.S5 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent) phi
      (Pattern.zeroOnesZero k hk)) (x : World) :
    M.Satisfies x phi := by
  by_contra hx
  have hstart : Pattern.HoldsBit (Pattern.zeroOnesZero k hk).first
      (M.trace x phi 0) := by
    simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit, Model.trace]
      using hx
  have hreal := hvalid M hM x hstart
  have hends := Pattern.realizesTrace_zeroOnesZero_ends hk hreal
  have hnextFalse :
      Not ((M.iterateUpdate phi (k + 1)).Satisfies x phi) := hends.2.2
  have hfirst : (M.dropSet phi k).Nonempty := by
    apply M.dropSet_nonempty_of_satisfaction_change phi x phi
    intro hiff
    exact hnextFalse (hiff.mp hends.2.1)
  exact no_finite_periodic_drops M phi k (by omega) hfirst
    (fun t ht => s5_zeroOnesZero_drop_next M hM phi k hk hvalid t ht)

/-- The paper's special single-agent observation: under `01^k0`-validity,
one update of a KD45 model is still serial (transitivity and Euclideanness are
always preserved).  If seriality failed, a successor would become a dead end;
at a dead end truth cannot later return to zero as the pattern requires. -/
theorem single_kd45_update_isKD45_of_valid_zeroOnesZero
    {World : Type u} (M : Model World Atom Unit) (hM : IsKD45 M)
    (phi : Formula Atom Unit) (k : Nat) (hk : 1 <= k)
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Unit) : FrameClass.{u} Atom Unit) phi
      (Pattern.zeroOnesZero k hk)) :
    IsKD45 (M.update phi) := by
  intro i
  have hk45 := M.update_isK45 hM.isK45 phi i
  refine ⟨?_, hk45.1, hk45.2⟩
  intro x
  by_contra hno
  have hdeadX : forall z, Not ((M.update phi).rel i x z) := by
    intro z hxz
    exact hno ⟨z, hxz⟩
  obtain ⟨y, hxy⟩ := (hM i).1 x
  have hyFalse : Not (M.Satisfies y phi) := by
    intro hy
    exact hdeadX y ⟨hxy, hy⟩
  have hdeadYi : forall z, Not ((M.update phi).rel i y z) := by
    intro z hyz
    apply hdeadX z
    refine ⟨?_, hyz.2⟩
    exact (Frame.successor_eq_of_transitive_euclidean
      (R := M.rel i) (x := x) (y := y)
      (hM i).2.1 (hM i).2.2 hxy z).mpr hyz.1
  have hdeadY : forall j z, Not ((M.update phi).rel j y z) := by
    intro j z
    simpa [Subsingleton.elim j i] using hdeadYi z
  have hstart : Pattern.HoldsBit (Pattern.zeroOnesZero k hk).first
      (M.trace y phi 0) := by
    simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit, Model.trace]
      using hyFalse
  have hreal := hvalid M hM y hstart
  have hnow : (M.update phi).Satisfies y phi := by
    exact Pattern.realizesTrace_zeroOnesZero_one hk hreal
  have hfinal := (Pattern.realizesTrace_zeroOnesZero_ends hk hreal).2.2
  have hlaterFalse :
      Not (((M.update phi).iterateUpdate phi k).Satisfies y phi) := by
    intro hlater
    apply hfinal
    have hleft :
        ((M.iterateUpdate phi 1).iterateUpdate phi k).Satisfies y phi := hlater
    have hright := (Model.satisfies_congr
      (M.iterateUpdate_add phi 1 k) y phi).mpr hleft
    simpa [Model.trace, Nat.add_comm] using hright
  exact hlaterFalse
    ((iterateUpdate_satisfies_iff_of_deadEnd
      (M.update phi) y hdeadY phi phi k).mpr hnow)

/-- Hence every iterate of a single-agent KD45 model remains KD45 under a
globally `01^k0`-valid announcement. -/
theorem single_kd45_iterateUpdate_isKD45_of_valid_zeroOnesZero
    {World : Type u} (M : Model World Atom Unit) (hM : IsKD45 M)
    (phi : Formula Atom Unit) (k : Nat) (hk : 1 <= k)
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Unit) : FrameClass.{u} Atom Unit) phi
      (Pattern.zeroOnesZero k hk)) :
    forall n, IsKD45 (M.iterateUpdate phi n)
  | 0 => hM
  | n + 1 => single_kd45_update_isKD45_of_valid_zeroOnesZero
      (M.iterateUpdate phi n)
      (single_kd45_iterateUpdate_isKD45_of_valid_zeroOnesZero
        M hM phi k hk hvalid n)
      phi k hk hvalid

/-- Finite-model core of the single-agent KD45 `01^k0` nonexistence lemma. -/
theorem finite_single_kd45_valid_zeroOnesZero_true
    {World : Type u} [Finite World] (M : Model World Atom Unit)
    (hM : IsKD45 M) (phi : Formula Atom Unit) (k : Nat) (hk : 1 <= k)
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Unit) : FrameClass.{u} Atom Unit) phi
      (Pattern.zeroOnesZero k hk)) (x : World) :
    M.Satisfies x phi := by
  by_contra hx
  have hframes :=
    single_kd45_iterateUpdate_isKD45_of_valid_zeroOnesZero
      M hM phi k hk hvalid
  have hfalse_mul : forall r : Nat,
      Not (M.trace x phi (r * (k + 1))) := by
    intro r
    induction r with
    | zero => simpa [Model.trace] using hx
    | succ r ihr =>
        let t := r * (k + 1)
        have hstart : Pattern.HoldsBit
            (Pattern.zeroOnesZero k hk).first
            ((M.iterateUpdate phi t).trace x phi 0) := by
          simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit,
            Model.trace, t] using ihr
        have hreal := hvalid (M.iterateUpdate phi t) (hframes t) x hstart
        have hlocal : Not ((M.iterateUpdate phi t).trace x phi (k + 1)) :=
          (Pattern.realizesTrace_zeroOnesZero_ends hk hreal).2.2
        have hglobal : Not (M.trace x phi (t + (k + 1))) := by
          simpa only [Model.trace, M.iterateUpdate_add] using hlocal
        simpa [t, Nat.succ_mul] using hglobal
  obtain ⟨n, hstable⟩ := M.exists_trace_eventually_constant phi
  let t := n * (k + 1)
  have hnt : n <= t := Nat.le_mul_of_pos_right n (by omega)
  have htfalse : Not (M.trace x phi t) := by
    simpa [t] using hfalse_mul n
  have hstart : Pattern.HoldsBit
      (Pattern.zeroOnesZero k hk).first
      ((M.iterateUpdate phi t).trace x phi 0) := by
    simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit,
      Model.trace] using htfalse
  have hreal := hvalid (M.iterateUpdate phi t) (hframes t) x hstart
  have hlocalTrue : (M.iterateUpdate phi t).trace x phi k :=
    (Pattern.realizesTrace_zeroOnesZero_ends hk hreal).2.1
  have hglobalTrue : M.trace x phi (t + k) := by
    simpa only [Model.trace, M.iterateUpdate_add] using hlocalTrue
  have htToN := hstable t hnt x
  have htkToN := hstable (t + k) (Nat.le_trans hnt (Nat.le_add_right t k)) x
  exact htfalse (htToN.mpr (htkToN.mp hglobalTrue))

/-- Finite-model core of the `01^k0` nonexistence lemma for K45.

If `phi` is `01^k0`-valid on all K45 models, it is true at every point of
every finite K45 model.  The proof repeatedly reapplies validity to updated
K45 models and contradicts finite trace stabilization. -/
theorem finite_k45_valid_zeroOnesZero_true
    {World : Type u} [Finite World] (M : Model World Atom Agent)
    (hM : IsK45 M) (phi : Formula Atom Agent) (k : Nat) (hk : 1 <= k)
    (hvalid : Sigma.Valid
      (Classes.K45 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent) phi
      (Pattern.zeroOnesZero k hk)) (x : World) :
    M.Satisfies x phi := by
  by_contra hx
  have hfalse_mul : forall r : Nat,
      Not (M.trace x phi (r * (k + 1))) := by
    intro r
    induction r with
    | zero => simpa [Model.trace] using hx
    | succ r ihr =>
        let t := r * (k + 1)
        have hstart : Pattern.HoldsBit
            (Pattern.zeroOnesZero k hk).first
            ((M.iterateUpdate phi t).trace x phi 0) := by
          simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit,
            Model.trace, t] using ihr
        have hreal := hvalid (M.iterateUpdate phi t)
          (M.iterateUpdate_isK45 hM phi t) x hstart
        have hlocal : Not ((M.iterateUpdate phi t).trace x phi (k + 1)) :=
          (Pattern.realizesTrace_zeroOnesZero_ends hk hreal).2.2
        have hglobal : Not (M.trace x phi (t + (k + 1))) := by
          simpa only [Model.trace, M.iterateUpdate_add] using hlocal
        simpa [t, Nat.succ_mul] using hglobal
  obtain ⟨n, hstable⟩ := M.exists_trace_eventually_constant phi
  let t := n * (k + 1)
  have hnt : n <= t := by
    exact Nat.le_mul_of_pos_right n (by omega)
  have htfalse : Not (M.trace x phi t) := by
    simpa [t] using hfalse_mul n
  have hstart : Pattern.HoldsBit
      (Pattern.zeroOnesZero k hk).first
      ((M.iterateUpdate phi t).trace x phi 0) := by
    simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit,
      Model.trace] using htfalse
  have hreal := hvalid (M.iterateUpdate phi t)
    (M.iterateUpdate_isK45 hM phi t) x hstart
  have hlocalTrue : (M.iterateUpdate phi t).trace x phi k :=
    (Pattern.realizesTrace_zeroOnesZero_ends hk hreal).2.1
  have hglobalTrue : M.trace x phi (t + k) := by
    simpa only [Model.trace, M.iterateUpdate_add] using hlocalTrue
  have htToN := hstable t hnt x
  have htkToN := hstable (t + k) (Nat.le_trans hnt (Nat.le_add_right t k)) x
  exact htfalse (htToN.mpr (htkToN.mp hglobalTrue))

/-- Full K45 form of the paper's `01^k0` result.  The filtration theorem
turns any counterexample to `phi` into a finite K45 counterexample, which the
finite dynamics theorem excludes. -/
theorem k45_valid_zeroOnesZero_true
    (phi : Formula Atom Agent) (k : Nat) (hk : 1 <= k)
    (hvalid : Sigma.Valid
      (Classes.K45 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      phi (Pattern.zeroOnesZero k hk)) :
    forall {World : Type u} (M : Model World Atom Agent), IsK45 M ->
      forall x, M.Satisfies x phi := by
  intro World M hM x
  by_contra hx
  obtain ⟨FiniteWorld, hFinite, N, hN, z, hz⟩ :=
    Filtration.exists_finite_countermodel_isK45 M hM phi x hx
  letI : Finite FiniteWorld := hFinite
  exact hz (finite_k45_valid_zeroOnesZero_true N hN phi k hk hvalid z)

/-- Full S5 form of the paper's nonexistence argument for `0^k1`. -/
theorem s5_valid_zerosOne_true
    (phi : Formula Atom Agent) (k : Nat) (hk : 2 <= k)
    (hvalid : Sigma.Valid
      (Classes.S5 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      phi (Pattern.zerosOne k hk)) :
    forall {World : Type u} (M : Model World Atom Agent), IsS5 M ->
      forall x, M.Satisfies x phi := by
  intro World M hM x
  by_contra hx
  obtain ⟨FiniteWorld, hFinite, N, hN, z, hz⟩ :=
    Filtration.exists_finite_countermodel_isS5 M hM phi x hx
  letI : Finite FiniteWorld := hFinite
  exact hz (finite_s5_valid_zerosOne_true N hN phi k hk hvalid z)

/-- Full S5 form of the paper's nonexistence argument for `01^k0`. -/
theorem s5_valid_zeroOnesZero_true
    (phi : Formula Atom Agent) (k : Nat) (hk : 1 <= k)
    (hvalid : Sigma.Valid
      (Classes.S5 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      phi (Pattern.zeroOnesZero k hk)) :
    forall {World : Type u} (M : Model World Atom Agent), IsS5 M ->
      forall x, M.Satisfies x phi := by
  intro World M hM x
  by_contra hx
  obtain ⟨FiniteWorld, hFinite, N, hN, z, hz⟩ :=
    Filtration.exists_finite_countermodel_isS5 M hM phi x hx
  letI : Finite FiniteWorld := hFinite
  exact hz (finite_s5_valid_zeroOnesZero_true N hN phi k hk hvalid z)

/-- Full single-agent KD45 form of the paper's `01^k0` result. -/
theorem single_kd45_valid_zeroOnesZero_true
    (phi : Formula Atom Unit) (k : Nat) (hk : 1 <= k)
    (hvalid : Sigma.Valid
      (Classes.KD45 (Atom := Atom) (Agent := Unit) : FrameClass.{u} Atom Unit)
      phi (Pattern.zeroOnesZero k hk)) :
    forall {World : Type u} (M : Model World Atom Unit), IsKD45 M ->
      forall x, M.Satisfies x phi := by
  intro World M hM x
  by_contra hx
  obtain ⟨FiniteWorld, hFinite, N, hN, z, hz⟩ :=
    Filtration.exists_finite_countermodel_isKD45 M hM phi x hx
  letI : Finite FiniteWorld := hFinite
  exact hz
    (finite_single_kd45_valid_zeroOnesZero_true N hN phi k hk hvalid z)

/-- Paper Lemma `lem:nonexistence_of_01k0-validity`, K45 case. -/
theorem k45_not_nontriviallyValid_zeroOnesZero
    (phi : Formula Atom Agent) (k : Nat) (hk : 1 <= k) :
    Not (Sigma.NontriviallyValid
      (Classes.K45 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      phi (Pattern.zeroOnesZero k hk)) := by
  rintro ⟨hvalid, World, M, hM, x, hreal⟩
  have htrue := k45_valid_zeroOnesZero_true phi k hk hvalid M hM x
  have hfirst := Pattern.realizesTrace_first hreal
  have hfalse : Not (M.Satisfies x phi) := by
    simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit, Model.trace]
      using hfirst
  exact hfalse htrue

/-- Paper Lemma `lem:nonexistence_of_0k1-validity`, S5 case. -/
theorem s5_not_nontriviallyValid_zerosOne
    (phi : Formula Atom Agent) (k : Nat) (hk : 2 <= k) :
    Not (Sigma.NontriviallyValid
      (Classes.S5 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      phi (Pattern.zerosOne k hk)) := by
  rintro ⟨hvalid, World, M, hM, x, hreal⟩
  have htrue := s5_valid_zerosOne_true phi k hk hvalid M hM x
  have hfirst := Pattern.realizesTrace_first hreal
  have hfalse : Not (M.Satisfies x phi) := by
    simpa [Pattern.HoldsBit, Model.trace] using hfirst
  exact hfalse htrue

/-- Paper Lemma `lem:nonexistence_of_01k0-validity`, S5 case. -/
theorem s5_not_nontriviallyValid_zeroOnesZero
    (phi : Formula Atom Agent) (k : Nat) (hk : 1 <= k) :
    Not (Sigma.NontriviallyValid
      (Classes.S5 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      phi (Pattern.zeroOnesZero k hk)) := by
  rintro ⟨hvalid, World, M, hM, x, hreal⟩
  have htrue := s5_valid_zeroOnesZero_true phi k hk hvalid M hM x
  have hfirst := Pattern.realizesTrace_first hreal
  have hfalse : Not (M.Satisfies x phi) := by
    simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit, Model.trace]
      using hfirst
  exact hfalse htrue

/-- Paper Lemma `lem:nonexistence_of_01k0-validity`, single-agent KD45 case. -/
theorem single_kd45_not_nontriviallyValid_zeroOnesZero
    (phi : Formula Atom Unit) (k : Nat) (hk : 1 <= k) :
    Not (Sigma.NontriviallyValid
      (Classes.KD45 (Atom := Atom) (Agent := Unit) : FrameClass.{u} Atom Unit)
      phi (Pattern.zeroOnesZero k hk)) := by
  rintro ⟨hvalid, World, M, hM, x, hreal⟩
  have htrue := single_kd45_valid_zeroOnesZero_true phi k hk hvalid M hM x
  have hfirst := Pattern.realizesTrace_first hreal
  have hfalse : Not (M.Satisfies x phi) := by
    simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit, Model.trace]
      using hfirst
  exact hfalse htrue

/-- Exact pattern-level K45 nonexistence statement. -/
theorem k45_zeroOnesZero_not_admissible (k : Nat) (hk : 1 <= k) :
    Not (Sigma.Admissible
      (Classes.K45 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnesZero k hk)) := by
  rintro ⟨phi, hphi⟩
  exact k45_not_nontriviallyValid_zeroOnesZero phi k hk hphi

/-- Exact pattern-level S5 nonexistence statement for `0^k1`. -/
theorem s5_zerosOne_not_admissible (k : Nat) (hk : 2 <= k) :
    Not (Sigma.Admissible
      (Classes.S5 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      (Pattern.zerosOne k hk)) := by
  rintro ⟨phi, hphi⟩
  exact s5_not_nontriviallyValid_zerosOne phi k hk hphi

/-- Exact pattern-level S5 nonexistence statement for `01^k0`. -/
theorem s5_zeroOnesZero_not_admissible (k : Nat) (hk : 1 <= k) :
    Not (Sigma.Admissible
      (Classes.S5 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnesZero k hk)) := by
  rintro ⟨phi, hphi⟩
  exact s5_not_nontriviallyValid_zeroOnesZero phi k hk hphi

/-- Exact pattern-level single-agent KD45 nonexistence statement. -/
theorem single_kd45_zeroOnesZero_not_admissible
    (k : Nat) (hk : 1 <= k) :
    Not (Sigma.Admissible
      (Classes.KD45 (Atom := Atom) (Agent := Unit) : FrameClass.{u} Atom Unit)
      (Pattern.zeroOnesZero k hk)) := by
  rintro ⟨phi, hphi⟩
  exact single_kd45_not_nontriviallyValid_zeroOnesZero phi k hk hphi

/-- No K45 formula is both globally `01^k0`-valid and realized with a finite
witness model. -/
theorem k45_not_finitelyNontriviallyValid_zeroOnesZero
    (phi : Formula Atom Agent) (k : Nat) (hk : 1 <= k) :
    Not (Sigma.FinitelyNontriviallyValid
      (Classes.K45 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      phi (Pattern.zeroOnesZero k hk)) := by
  rintro ⟨hvalid, World, hFinite, M, hM, x, hreal⟩
  letI : Finite World := hFinite
  have htrue := finite_k45_valid_zeroOnesZero_true M hM phi k hk hvalid x
  have hfirst := Pattern.realizesTrace_first hreal
  have hfalse : Not (M.Satisfies x phi) := by
    simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit, Model.trace]
      using hfirst
  exact hfalse htrue

/-- No S5 formula is both globally `0^k1`-valid and realized with a finite
witness model. -/
theorem s5_not_finitelyNontriviallyValid_zerosOne
    (phi : Formula Atom Agent) (k : Nat) (hk : 2 <= k) :
    Not (Sigma.FinitelyNontriviallyValid
      (Classes.S5 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      phi (Pattern.zerosOne k hk)) := by
  rintro ⟨hvalid, World, hFinite, M, hM, x, hreal⟩
  letI : Finite World := hFinite
  have htrue := finite_s5_valid_zerosOne_true M hM phi k hk hvalid x
  have hfirst := Pattern.realizesTrace_first hreal
  have hfalse : Not (M.Satisfies x phi) := by
    simpa [Pattern.HoldsBit, Model.trace] using hfirst
  exact hfalse htrue

/-- No S5 formula is both globally `01^k0`-valid and realized with a finite
witness model. -/
theorem s5_not_finitelyNontriviallyValid_zeroOnesZero
    (phi : Formula Atom Agent) (k : Nat) (hk : 1 <= k) :
    Not (Sigma.FinitelyNontriviallyValid
      (Classes.S5 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      phi (Pattern.zeroOnesZero k hk)) := by
  rintro ⟨hvalid, World, hFinite, M, hM, x, hreal⟩
  letI : Finite World := hFinite
  have htrue := finite_s5_valid_zeroOnesZero_true M hM phi k hk hvalid x
  have hfirst := Pattern.realizesTrace_first hreal
  have hfalse : Not (M.Satisfies x phi) := by
    simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit, Model.trace]
      using hfirst
  exact hfalse htrue

/-- No single-agent KD45 formula is both globally `01^k0`-valid and realized
with a finite witness model. -/
theorem single_kd45_not_finitelyNontriviallyValid_zeroOnesZero
    (phi : Formula Atom Unit) (k : Nat) (hk : 1 <= k) :
    Not (Sigma.FinitelyNontriviallyValid
      (Classes.KD45 (Atom := Atom) (Agent := Unit) : FrameClass.{u} Atom Unit)
      phi (Pattern.zeroOnesZero k hk)) := by
  rintro ⟨hvalid, World, hFinite, M, hM, x, hreal⟩
  letI : Finite World := hFinite
  have htrue :=
    finite_single_kd45_valid_zeroOnesZero_true M hM phi k hk hvalid x
  have hfirst := Pattern.realizesTrace_first hreal
  have hfalse : Not (M.Satisfies x phi) := by
    simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit, Model.trace]
      using hfirst
  exact hfalse htrue

/-- Pattern-level finite-witness nonexistence for K45. -/
theorem k45_zeroOnesZero_not_finitelyAdmissible (k : Nat) (hk : 1 <= k) :
    Not (Sigma.FinitelyAdmissible
      (Classes.K45 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnesZero k hk)) := by
  rintro ⟨phi, hphi⟩
  exact k45_not_finitelyNontriviallyValid_zeroOnesZero phi k hk hphi

/-- Pattern-level finite-witness nonexistence for `0^k1` on S5. -/
theorem s5_zerosOne_not_finitelyAdmissible (k : Nat) (hk : 2 <= k) :
    Not (Sigma.FinitelyAdmissible
      (Classes.S5 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      (Pattern.zerosOne k hk)) := by
  rintro ⟨phi, hphi⟩
  exact s5_not_finitelyNontriviallyValid_zerosOne phi k hk hphi

/-- Pattern-level finite-witness nonexistence for `01^k0` on S5. -/
theorem s5_zeroOnesZero_not_finitelyAdmissible (k : Nat) (hk : 1 <= k) :
    Not (Sigma.FinitelyAdmissible
      (Classes.S5 (Atom := Atom) (Agent := Agent) : FrameClass.{u} Atom Agent)
      (Pattern.zeroOnesZero k hk)) := by
  rintro ⟨phi, hphi⟩
  exact s5_not_finitelyNontriviallyValid_zeroOnesZero phi k hk hphi

/-- Pattern-level finite-witness nonexistence for single-agent KD45. -/
theorem single_kd45_zeroOnesZero_not_finitelyAdmissible
    (k : Nat) (hk : 1 <= k) :
    Not (Sigma.FinitelyAdmissible
      (Classes.KD45 (Atom := Atom) (Agent := Unit) : FrameClass.{u} Atom Unit)
      (Pattern.zeroOnesZero k hk)) := by
  rintro ⟨phi, hphi⟩
  exact single_kd45_not_finitelyNontriviallyValid_zeroOnesZero phi k hk hphi

end Nonexistence

end ClassificationSigmaValidity
