import ClassificationSigmaValidity.Unravelling
import Mathlib.Data.Fintype.Option

/-!
# Reduction to the agents occurring in a formula

The unravelling argument is finite in the agent coordinate.  A formula,
however, may be written over an arbitrary ambient type of agents.  This file
formalizes the paper's reduction to the finite set of agents occurring in the
candidate formula.

We adjoin one dummy agent to the support.  This makes the finite replacement
agent type inhabited even when the formula is purely propositional.  The
dummy is never used by the supported formula.  In the reverse direction it is
interpreted by an arbitrary ambient agent, which is the sole reason for the
`Nonempty Agent` hypothesis on the global transfer theorems.
-/

namespace ClassificationSigmaValidity

universe u v w

namespace Formula

variable {Atom : Type v} {Agent : Type w}

/-- The list of agent symbols occurring in a formula.  Unlike `agents`, this
representation does not require decidable equality. -/
def agentList : Formula Atom Agent -> List Agent
  | .atom _ => []
  | .neg phi => agentList phi
  | .conj phi psi => agentList phi ++ agentList psi
  | .box i phi => i :: agentList phi

/-- The finite type of occurring agents. -/
abbrev AgentSupport (phi : Formula Atom Agent) :=
  {i : Agent // i ∈ phi.agentList}

/-- The finite inhabited agent type used by the support reduction.  `none` is
the dummy agent and `some i` records an actually occurring agent. -/
abbrev SupportedAgent (phi : Formula Atom Agent) := Option (AgentSupport phi)

noncomputable instance agentSupportFintype (phi : Formula Atom Agent) :
    Fintype (AgentSupport phi) :=
  (List.finite_toSet phi.agentList).fintype

/-- Send every occurring ambient agent to its tagged copy; arbitrary
non-occurring inputs go to the dummy agent. -/
noncomputable def toSupported (phi : Formula Atom Agent) :
    Agent -> SupportedAgent phi := by
  classical
  exact fun i => if hi : i ∈ phi.agentList then some ⟨i, hi⟩ else none

/-- Interpret supported agents back in an inhabited ambient agent type. -/
noncomputable def fromSupported [Nonempty Agent] (phi : Formula Atom Agent) :
    SupportedAgent phi -> Agent
  | none => Classical.choice inferInstance
  | some i => i.1

/-- Rename a formula to its finite inhabited support type. -/
noncomputable def onSupport (phi : Formula Atom Agent) :
    Formula Atom (SupportedAgent phi) :=
  phi.map id phi.toSupported

@[simp] theorem toSupported_of_mem (phi : Formula Atom Agent) (i : Agent)
    (hi : i ∈ phi.agentList) : phi.toSupported i = some ⟨i, hi⟩ := by
  simp [toSupported, hi]

@[simp] theorem fromSupported_toSupported [Nonempty Agent]
    (phi : Formula Atom Agent) (i : Agent) (hi : i ∈ phi.agentList) :
    phi.fromSupported (phi.toSupported i) = i := by
  simp [fromSupported, toSupported, hi]

/-- Mapping agent names forward and then backward is the identity provided
the two maps are inverse on every symbol that actually occurs. -/
theorem map_map_eq_self_of_leftInverse_on_agentList
    {Agent' : Type u} (phi : Formula Atom Agent)
    (f : Agent -> Agent') (g : Agent' -> Agent)
    (hfg : ∀ i, i ∈ phi.agentList -> g (f i) = i) :
    (phi.map id f).map id g = phi := by
  induction phi with
  | atom p => rfl
  | neg phi ih =>
      simp only [map, agentList] at hfg ⊢
      exact congrArg Formula.neg (ih hfg)
  | conj phi psi ihPhi ihPsi =>
      simp only [map, agentList] at hfg ⊢
      congr 1
      · exact ihPhi (fun i hi => hfg i (List.mem_append_left _ hi))
      · exact ihPsi (fun i hi => hfg i (List.mem_append_right _ hi))
  | box i phi ih =>
      simp only [map, agentList] at hfg ⊢
      have hi : g (f i) = i := hfg i (by simp)
      rw [hi]
      exact congrArg (Formula.box i) (ih (fun j hj => hfg j (by simp [hj])))

/-- The support renaming followed by inclusion into the ambient agent type
recovers the original formula exactly. -/
theorem map_onSupport_fromSupported [Nonempty Agent]
    (phi : Formula Atom Agent) :
    (phi.onSupport.map id phi.fromSupported) = phi := by
  apply map_map_eq_self_of_leftInverse_on_agentList
  intro i hi
  exact fromSupported_toSupported phi i hi

end Formula

namespace AgentSupport

variable {Atom : Type v} {Agent : Type w}

private theorem holdsBit_iff {b : Bool} {p q : Prop} (h : p ↔ q) :
    Pattern.HoldsBit b p ↔ Pattern.HoldsBit b q := by
  cases b <;> simp [Pattern.HoldsBit, h]

/-- Expanding a model on the finite support back to all ambient agents
preserves the complete update trace of the original formula. -/
theorem expanded_trace_iff
    {World : Type u} (phi : Formula Atom Agent)
    (P : Model World Atom (Formula.SupportedAgent phi))
    (x : World) (n : Nat) :
    (P.reindex id phi.toSupported).trace x phi n ↔
      P.trace x phi.onSupport n := by
  exact P.reindex_trace id phi.toSupported phi x n

/-- Restricting an ambient model to the finite support preserves the complete
trace of the supported formula. -/
theorem restricted_trace_iff [Nonempty Agent]
    {World : Type u} (phi : Formula Atom Agent)
    (M : Model World Atom Agent) (x : World) (n : Nat) :
    (M.reindex id phi.fromSupported).trace x phi.onSupport n ↔
      M.trace x phi n := by
  rw [M.reindex_trace id phi.fromSupported phi.onSupport x n,
    Formula.map_onSupport_fromSupported]

/-- Sigma-validity of an ambient formula transfers to the same formula
renamed to its finite support. -/
theorem valid_onSupport
    (phi : Formula Atom Agent) (sigma : Pattern)
    (hvalid : Sigma.Valid
      (Classes.KD45 : FrameClass.{max u w} Atom Agent) phi sigma) :
    Sigma.Valid
      (Classes.KD45 :
        FrameClass.{max u w} Atom (Formula.SupportedAgent phi))
      phi.onSupport sigma := by
  intro World P hP x hx
  let M : Model World Atom Agent := P.reindex id phi.toSupported
  have hM : IsKD45 M := Model.reindex_isKD45 hP id phi.toSupported
  have hx' : Pattern.HoldsBit sigma.first (M.trace x phi 0) := by
    exact (holdsBit_iff (expanded_trace_iff phi P x 0)).mpr hx
  have hreal := hvalid M hM x hx'
  cases sigma with
  | finite bits hlen =>
      intro n hn
      exact (holdsBit_iff (expanded_trace_iff phi P x n)).mp (hreal n hn)
  | infinite bits =>
      intro n
      exact (holdsBit_iff (expanded_trace_iff phi P x n)).mp (hreal n)

/-- Finite-support transfer for the `0^k1` nonexistence argument: over an
arbitrary inhabited ambient agent type, `0^k1`-validity forces truth at every
point of every KD45 model. -/
theorem kd45_valid_zerosOne_true [Nonempty Agent]
    (phi : Formula Atom Agent) (k : Nat) (hk : 2 <= k)
    (hvalid : Sigma.Valid
      (Classes.KD45 : FrameClass.{max u w} Atom Agent)
      phi (Pattern.zerosOne k hk)) :
    ∀ {World : Type max u w} (M : Model World Atom Agent),
      IsKD45 M -> ∀ x, M.Satisfies x phi := by
  intro World M hM x
  let phiS := phi.onSupport
  let N : Model World Atom (Formula.SupportedAgent phi) :=
    M.reindex id phi.fromSupported
  have hN : IsKD45 N := Model.reindex_isKD45 hM id phi.fromSupported
  have hvalidS : Sigma.Valid
      (Classes.KD45 :
        FrameClass.{max u w} Atom (Formula.SupportedAgent phi))
      phiS (Pattern.zerosOne k hk) :=
    @valid_onSupport.{max u w, v, w} Atom Agent phi
      (Pattern.zerosOne k hk) hvalid
  have hxS := Unravelling.finiteAgent_kd45_valid_zerosOne_true
    phiS k hk hvalidS N hN x
  exact (restricted_trace_iff phi M x 0).mp hxS

/-- Finite-support transfer for the `01^k0` nonexistence argument. -/
theorem kd45_valid_zeroOnesZero_true [Nonempty Agent]
    (phi : Formula Atom Agent) (k : Nat) (hk : 1 <= k)
    (hvalid : Sigma.Valid
      (Classes.KD45 : FrameClass.{max u w} Atom Agent)
      phi (Pattern.zeroOnesZero k hk)) :
    ∀ {World : Type max u w} (M : Model World Atom Agent),
      IsKD45 M -> ∀ x, M.Satisfies x phi := by
  intro World M hM x
  let phiS := phi.onSupport
  let N : Model World Atom (Formula.SupportedAgent phi) :=
    M.reindex id phi.fromSupported
  have hN : IsKD45 N := Model.reindex_isKD45 hM id phi.fromSupported
  have hvalidS : Sigma.Valid
      (Classes.KD45 :
        FrameClass.{max u w} Atom (Formula.SupportedAgent phi))
      phiS (Pattern.zeroOnesZero k hk) :=
    @valid_onSupport.{max u w, v, w} Atom Agent phi
      (Pattern.zeroOnesZero k hk) hvalid
  have hxS := Unravelling.finiteAgent_kd45_valid_zeroOnesZero_true
    phiS k hk hvalidS N hN x
  exact (restricted_trace_iff phi M x 0).mp hxS

/-- Paper Lemma `lem:nonexistence_of_0k1-validity_multi_kd45`, for an
arbitrary inhabited ambient type of agents. -/
theorem kd45_not_nontriviallyValid_zerosOne [Nonempty Agent]
    (phi : Formula Atom Agent) (k : Nat) (hk : 2 <= k) :
    ¬Sigma.NontriviallyValid
      (Classes.KD45 : FrameClass.{max u w} Atom Agent)
      phi (Pattern.zerosOne k hk) := by
  rintro ⟨hvalid, World, M, hM, x, hreal⟩
  have htrue := kd45_valid_zerosOne_true phi k hk hvalid M hM x
  have hfirst := Pattern.realizesTrace_first hreal
  have hfalse : ¬M.Satisfies x phi := by
    simpa [Pattern.HoldsBit, Model.trace] using hfirst
  exact hfalse htrue

/-- Paper Lemma `lem:nonexistence_of_01k0-validity_multi_kd45`, for an
arbitrary inhabited ambient type of agents. -/
theorem kd45_not_nontriviallyValid_zeroOnesZero [Nonempty Agent]
    (phi : Formula Atom Agent) (k : Nat) (hk : 1 <= k) :
    ¬Sigma.NontriviallyValid
      (Classes.KD45 : FrameClass.{max u w} Atom Agent)
      phi (Pattern.zeroOnesZero k hk) := by
  rintro ⟨hvalid, World, M, hM, x, hreal⟩
  have htrue := kd45_valid_zeroOnesZero_true phi k hk hvalid M hM x
  have hfirst := Pattern.realizesTrace_first hreal
  have hfalse : ¬M.Satisfies x phi := by
    simpa [Pattern.zeroOnesZero, Pattern.first, Pattern.HoldsBit, Model.trace]
      using hfirst
  exact hfalse htrue

/-- Pattern-level multi-agent KD45 nonadmissibility of `0^k1`, with no
finiteness assumption on the ambient type of agents. -/
theorem kd45_zerosOne_not_admissible [Nonempty Agent]
    (k : Nat) (hk : 2 <= k) :
    ¬Sigma.Admissible
      (Classes.KD45 : FrameClass.{max u w} Atom Agent)
      (Pattern.zerosOne k hk) := by
  rintro ⟨phi, hphi⟩
  exact kd45_not_nontriviallyValid_zerosOne phi k hk hphi

/-- Pattern-level multi-agent KD45 nonadmissibility of `01^k0`, with no
finiteness assumption on the ambient type of agents. -/
theorem kd45_zeroOnesZero_not_admissible [Nonempty Agent]
    (k : Nat) (hk : 1 <= k) :
    ¬Sigma.Admissible
      (Classes.KD45 : FrameClass.{max u w} Atom Agent)
      (Pattern.zeroOnesZero k hk) := by
  rintro ⟨phi, hphi⟩
  exact kd45_not_nontriviallyValid_zeroOnesZero phi k hk hphi

end AgentSupport

end ClassificationSigmaValidity
