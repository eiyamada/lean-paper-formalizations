import ClassificationSigmaValidity.Collapse
import ClassificationSigmaValidity.Locality

/-!
# Single-agent KD45 collapse

This file proves the single-agent half of the paper's `00`-validity collapse.
The explicit assumptions `[Nonempty Agent] [Subsingleton Agent]` expose what
"single-agent" means without fixing a particular singleton type.
-/

namespace ClassificationSigmaValidity

universe u v w

namespace Model

variable {World : Type u} {Atom : Type v} {Agent : Type w}

/-- In a single-agent transitive frame, every state reachable from `root` is
either `root` itself or a direct successor of it. -/
theorem reachable_eq_or_rel [Subsingleton Agent] {M : Model World Atom Agent}
    (hM : IsK45 M) {root z : World} (hz : M.Reachable root z) :
    z = root \/ exists i, M.rel i root z := by
  induction hz with
  | refl => exact Or.inl rfl
  | @tail y z hy hyz ih =>
      rcases hyz with ⟨j, hyz⟩
      rcases ih with rfl | ⟨i, hri⟩
      · exact Or.inr ⟨j, hyz⟩
      · have hij : j = i := Subsingleton.elim _ _
        subst j
        exact Or.inr ⟨i, (hM i).1 hri hyz⟩

/-- If the root of a single-agent K45 generated submodel has a successor, the
generated submodel is serial and hence KD45. -/
theorem generatedSubmodel_isKD45_of_successor [Subsingleton Agent]
    {M : Model World Atom Agent} (hM : IsK45 M) (root : World)
    {i : Agent} {y : World} (hxy : M.rel i root y) :
    IsKD45 (M.generatedSubmodel root) := by
  have hK := M.generatedSubmodel_isK45 hM root
  intro j
  refine ⟨?_, (hK j).1, (hK j).2⟩
  intro z
  let yG : Subtype (M.generatedSet root) :=
    ⟨y, Relation.ReflTransGen.single ⟨i, hxy⟩⟩
  refine ⟨yG, ?_⟩
  have hji : j = i := Subsingleton.elim _ _
  subst j
  rcases M.reachable_eq_or_rel hM z.property with hz | ⟨a, hza⟩
  · simpa [generatedSubmodel, yG, hz] using hxy
  · have hai : a = i := Subsingleton.elim _ _
    subst a
    simpa [generatedSubmodel, yG] using (hM i).2 hza hxy

/-- One false step of a globally `00`-valid formula remains false even when a
single-agent KD45 update has lost seriality. -/
theorem singleAgent_false_persists
    [Nonempty Agent] [Subsingleton Agent]
    {M : Model World Atom Agent} (hM : IsK45 M)
    (phi : Formula Atom Agent)
    (hvalid : Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      phi Pattern.zeroZero)
    (x : World) (hx : Not (M.Satisfies x phi)) :
    Not ((M.update phi).Satisfies x phi) := by
  by_cases hout : exists (i : Agent) (y : World), M.rel i x y
  · rcases hout with ⟨i, y, hxy⟩
    let U : Set World := M.generatedSet x
    let G : Model (Subtype U) Atom Agent := M.generatedSubmodel x
    let gx : Subtype U := M.generatedPoint x
    have hG : IsKD45 G := M.generatedSubmodel_isKD45_of_successor hM x hxy
    have hxG : Not (G.Satisfies gx phi) := by
      intro hs
      exact hx ((M.generatedSubmodel_root_satisfies_iff x phi).mp hs)
    have hreal := hvalid G hG gx (by simpa [Pattern.zeroZero] using hxG)
    have hnextG : Not ((G.update phi).Satisfies gx phi) :=
      (Sigma.realizes_bits2_iff G gx phi false false).mp hreal |>.2
    intro hnext
    apply hnextG
    have hU : M.ForwardClosed U := M.generatedSet_forwardClosed x
    have hrestricted : ((M.update phi).restrict U).Satisfies gx phi :=
      ((M.update phi).restrict_satisfies_iff U (M.forwardClosed_update hU phi) gx phi).mpr
        hnext
    have heq : (M.update phi).restrict U = G.update phi := by
      simpa [G, U, generatedSubmodel] using M.restrict_update_eq U hU phi
    exact (Model.satisfies_congr heq gx phi).mp hrestricted
  · have hnone : forall (i : Agent) (y : World), Not (M.rel i x y) := by
      intro i y hxy
      exact hout ⟨i, y, hxy⟩
    let U : Set World := {x}
    have hU : M.ForwardClosed U := by
      intro z hz i y hzy
      have hzx : z = x := Set.mem_singleton_iff.mp hz
      subst z
      exact (hnone i y hzy).elim
    have hUupdate : (M.update phi).ForwardClosed U := M.forwardClosed_update hU phi
    have hagree : M.LocallyAgrees (M.update phi) U := by
      constructor
      · intro p z hz
        rfl
      · intro i z hz y hy
        have hzx : z = x := Set.mem_singleton_iff.mp hz
        subst z
        constructor
        · intro hxy
          exact (hnone i y hxy).elim
        · exact fun hxy => hxy.1
    have hiff := M.satisfies_iff_of_locallyAgrees hU hUupdate hagree x
      (Set.mem_singleton x) phi
    exact fun hnext => hx (hiff.mpr hnext)

end Model

namespace Collapse

variable {Atom : Type v} {Agent : Type w}

/-- Paper Lemma `lem:00-validity_collapse`, single-agent KD45 half. -/
theorem singleAgentKD45_valid_zeroZero_implies_zerosInf
    [Nonempty Agent] [Subsingleton Agent]
    (phi : Formula Atom Agent)
    (hvalid : Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      phi Pattern.zeroZero) :
    Sigma.Valid (Classes.KD45 : FrameClass.{u} Atom Agent)
      phi Pattern.zerosInf := by
  intro World M hM x hx
  have hx0 : Not (M.Satisfies x phi) := by simpa [Pattern.zeroZero] using hx
  have hK : IsK45 M := hM.isK45
  intro n
  simp only [Pattern.HoldsBit]
  induction n with
  | zero => exact hx0
  | succ n ih =>
      have hKn : IsK45 (M.iterateUpdate phi n) := M.iterateUpdate_isK45 hK phi n
      exact (M.iterateUpdate phi n).singleAgent_false_persists hKn phi hvalid x ih

end Collapse

end ClassificationSigmaValidity
