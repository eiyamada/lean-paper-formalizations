import SourcesOfUnknowability.DNF

/-!
# A finite DNF for the single-agent basic modal language

For the single-agent language, every modal formula has a finite semantic DNF
whose clauses have propositional alpha parts.  The positive and negative
normalizations are defined together, so a negated box becomes a diamond of
the negated scope.
-/

namespace SourcesOfUnknowability
namespace DNFNormalization

open ClassificationSigmaValidity
open DNF

universe u v

variable {Atom : Type v}

/-- The empty modal component with a true propositional part. -/
def truthClause [Inhabited Atom] : Clause Atom Unit where
  alpha := Formula.verum
  boxes := []
  diamonds := []
  alpha_modalFree := by simp [Formula.verum, Formula.falsum, Formula.modalDepth]

def atomClause (p : Atom) : Clause Atom Unit where
  alpha := .atom p
  boxes := []
  diamonds := []
  alpha_modalFree := rfl

def negAtomClause (p : Atom) : Clause Atom Unit where
  alpha := .neg (.atom p)
  boxes := []
  diamonds := []
  alpha_modalFree := rfl

def boxClause [Inhabited Atom] (φ : Formula Atom Unit) : Clause Atom Unit where
  alpha := Formula.verum
  boxes := [φ]
  diamonds := []
  alpha_modalFree := by simp [Formula.verum, Formula.falsum, Formula.modalDepth]

def notBoxClause [Inhabited Atom] (φ : Formula Atom Unit) : Clause Atom Unit where
  alpha := Formula.verum
  boxes := []
  diamonds := [.neg φ]
  alpha_modalFree := by simp [Formula.verum, Formula.falsum, Formula.modalDepth]

/-- Conjunction of two DNF clauses. -/
def join (c d : Clause Atom Unit) : Clause Atom Unit where
  alpha := .conj c.alpha d.alpha
  boxes := c.boxes ++ d.boxes
  diamonds := c.diamonds ++ d.diamonds
  alpha_modalFree := by
    simp [Formula.modalDepth, c.alpha_modalFree, d.alpha_modalFree]

theorem holds_join {World : Type u} (M : Model World Atom Unit) (x : World)
    (c d : Clause Atom Unit) :
    (join c d).Holds M x () ↔ c.Holds M x () ∧ d.Holds M x () := by
  simp only [Clause.Holds, Clause.ModalPart, join, Model.satisfies_and,
    List.mem_append]
  constructor
  · rintro ⟨⟨hcα, hdα⟩, hboxes, hdias⟩
    constructor
    · refine ⟨hcα, ?_, ?_⟩
      · intro β hβ; exact hboxes β (Or.inl hβ)
      · intro γ hγ; exact hdias γ (Or.inl hγ)
    · refine ⟨hdα, ?_, ?_⟩
      · intro β hβ; exact hboxes β (Or.inr hβ)
      · intro γ hγ; exact hdias γ (Or.inr hγ)
  · rintro ⟨⟨hcα, hcbox, hcdia⟩, ⟨hdα, hdbox, hddia⟩⟩
    refine ⟨⟨hcα, hdα⟩, ?_, ?_⟩
    · intro β hβ
      rcases hβ with hβ | hβ
      · exact hcbox β hβ
      · exact hdbox β hβ
    · intro γ hγ
      rcases hγ with hγ | hγ
      · exact hcdia γ hγ
      · exact hddia γ hγ

theorem holds_atomClause {World : Type u} (M : Model World Atom Unit)
    (x : World) (p : Atom) :
    (atomClause p).Holds M x () ↔ M.Satisfies x (.atom p) := by
  simp [Clause.Holds, Clause.ModalPart, atomClause]

theorem holds_negAtomClause {World : Type u} (M : Model World Atom Unit)
    (x : World) (p : Atom) :
    (negAtomClause p).Holds M x () ↔ ¬ M.Satisfies x (.atom p) := by
  simp [Clause.Holds, Clause.ModalPart, negAtomClause, Model.Satisfies]

theorem holds_boxClause [Inhabited Atom] {World : Type u}
    (M : Model World Atom Unit) (x : World) (φ : Formula Atom Unit) :
    (boxClause φ).Holds M x () ↔ M.Satisfies x (.box () φ) := by
  simp [Clause.Holds, Clause.ModalPart, boxClause]

theorem holds_notBoxClause [Inhabited Atom] {World : Type u}
    (M : Model World Atom Unit) (x : World) (φ : Formula Atom Unit) :
    (notBoxClause φ).Holds M x () ↔ ¬ M.Satisfies x (.box () φ) := by
  classical
  simp [Clause.Holds, Clause.ModalPart, notBoxClause, Model.satisfies_dia,
    Model.Satisfies, not_forall, Classical.not_imp]

/-- Conjunction distributes over finite semantic disjunctions. -/
def conjunction (xs ys : List (Clause Atom Unit)) : List (Clause Atom Unit) :=
  xs.flatMap (fun c => ys.map (join c))

theorem holds_append {World : Type u} (M : Model World Atom Unit)
    (x : World) (xs ys : List (Clause Atom Unit)) :
    Holds (xs ++ ys) M x () ↔ Holds xs M x () ∨ Holds ys M x () := by
  simp only [Holds, List.mem_append]
  constructor
  · rintro ⟨c, hc, hholds⟩
    rcases hc with hx | hy
    · exact Or.inl ⟨c, hx, hholds⟩
    · exact Or.inr ⟨c, hy, hholds⟩
  · rintro (⟨c, hc, hholds⟩ | ⟨c, hc, hholds⟩)
    · exact ⟨c, Or.inl hc, hholds⟩
    · exact ⟨c, Or.inr hc, hholds⟩

theorem holds_conjunction {World : Type u} (M : Model World Atom Unit)
    (x : World) (xs ys : List (Clause Atom Unit)) :
    Holds (conjunction xs ys) M x () ↔
      Holds xs M x () ∧ Holds ys M x () := by
  simp only [Holds, conjunction, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨e, ⟨c, hc, d, hd, he⟩, hehold⟩
    subst e
    obtain ⟨hcHold, hdHold⟩ := (holds_join M x c d).1 hehold
    exact ⟨⟨c, hc, hcHold⟩, ⟨d, hd, hdHold⟩⟩
  · rintro ⟨⟨c, hc, hcHold⟩, ⟨d, hd, hdHold⟩⟩
    exact ⟨join c d, ⟨c, hc, d, hd, rfl⟩,
      (holds_join M x c d).2 ⟨hcHold, hdHold⟩⟩

mutual

/-- Positive single-agent K-DNF. -/
def positive [Inhabited Atom] : Formula Atom Unit → List (Clause Atom Unit)
  | .atom p => [atomClause p]
  | .neg φ => negative φ
  | .conj φ ψ => conjunction (positive φ) (positive ψ)
  | .box _ φ => [boxClause φ]

/-- Negative single-agent K-DNF, equivalent to negation of the input. -/
def negative [Inhabited Atom] : Formula Atom Unit → List (Clause Atom Unit)
  | .atom p => [negAtomClause p]
  | .neg φ => positive φ
  | .conj φ ψ => negative φ ++ negative ψ
  | .box _ φ => [notBoxClause φ]

end

theorem holds_singleton {World : Type u} (M : Model World Atom Unit)
    (x : World) (c : Clause Atom Unit) :
    Holds [c] M x () ↔ c.Holds M x () := by
  simp [Holds]

/-- The positive and negative normalizers are both semantically correct. -/
theorem normalizers_correct [Inhabited Atom] (φ : Formula Atom Unit) :
    (∀ {World : Type u} (M : Model World Atom Unit) (x : World),
      Holds (positive φ) M x () ↔ M.Satisfies x φ) ∧
    (∀ {World : Type u} (M : Model World Atom Unit) (x : World),
      Holds (negative φ) M x () ↔ ¬ M.Satisfies x φ) := by
  classical
  induction φ with
  | atom p =>
      constructor
      · intro World M x
        simpa [positive] using
          (holds_singleton M x (atomClause p)).trans (holds_atomClause M x p)
      · intro World M x
        simpa [negative] using
          (holds_singleton M x (negAtomClause p)).trans
            (holds_negAtomClause M x p)
  | neg ψ ih =>
      constructor
      · intro World M x
        simpa [positive, Model.Satisfies] using ih.2 M x
      · intro World M x
        simpa [negative, Model.Satisfies] using ih.1 M x
  | conj ψ χ ihψ ihχ =>
      constructor
      · intro World M x
        rw [positive, holds_conjunction, ihψ.1 M x, ihχ.1 M x]
        rfl
      · intro World M x
        rw [negative, holds_append, ihψ.2 M x, ihχ.2 M x]
        change (¬ M.Satisfies x ψ ∨ ¬ M.Satisfies x χ) ↔
          ¬ (M.Satisfies x ψ ∧ M.Satisfies x χ)
        constructor
        · intro h hboth
          rcases h with hψ | hχ
          · exact hψ hboth.1
          · exact hχ hboth.2
        · intro h
          by_cases hψ : M.Satisfies x ψ
          · exact Or.inr (fun hχ => h ⟨hψ, hχ⟩)
          · exact Or.inl hψ
  | box i ψ ih =>
      cases i
      constructor
      · intro World M x
        simpa [positive] using
          (holds_singleton M x (boxClause ψ)).trans (holds_boxClause M x ψ)
      · intro World M x
        simpa [negative] using
          (holds_singleton M x (notBoxClause ψ)).trans
            (holds_notBoxClause M x ψ)

/-- Every single-agent formula is equivalent, over all K models, to its
explicit finite list of DNF clauses. -/
theorem positive_equivalent [Inhabited Atom] (φ : Formula Atom Unit)
    {World : Type u} (M : Model World Atom Unit) (x : World) :
    M.Satisfies x φ ↔ Holds (positive φ) M x () :=
  (normalizers_correct φ).1 M x |>.symm

/-- Object-language conjunction of the box requirements. -/
def renderBoxes (B : List (Formula Atom Unit)) (tail : Formula Atom Unit) :
    Formula Atom Unit :=
  B.foldr (fun β acc => .conj (.box () β) acc) tail

/-- Object-language conjunction of the diamond requirements. -/
def renderDiamonds (Γ : List (Formula Atom Unit)) (tail : Formula Atom Unit) :
    Formula Atom Unit :=
  Γ.foldr (fun γ acc => .conj (Formula.dia () γ) acc) tail

def renderClause (c : Clause Atom Unit) : Formula Atom Unit :=
  renderBoxes c.boxes (renderDiamonds c.diamonds c.alpha)

def render [Inhabited Atom] : List (Clause Atom Unit) → Formula Atom Unit
  | [] => Formula.falsum
  | c :: cs => Formula.or (renderClause c) (render cs)

theorem satisfies_renderBoxes {World : Type u} (M : Model World Atom Unit)
    (x : World) (B : List (Formula Atom Unit)) (tail : Formula Atom Unit) :
    M.Satisfies x (renderBoxes B tail) ↔
      (∀ β ∈ B, M.Satisfies x (.box () β)) ∧ M.Satisfies x tail := by
  induction B with
  | nil => simp [renderBoxes]
  | cons β B ih =>
      change (M.Satisfies x (.box () β) ∧
        M.Satisfies x (renderBoxes B tail)) ↔
        (∀ a ∈ β :: B, M.Satisfies x (.box () a)) ∧ M.Satisfies x tail
      rw [ih]
      simp [List.mem_cons, and_assoc]

theorem satisfies_renderDiamonds {World : Type u} (M : Model World Atom Unit)
    (x : World) (Γ : List (Formula Atom Unit)) (tail : Formula Atom Unit) :
    M.Satisfies x (renderDiamonds Γ tail) ↔
      (∀ γ ∈ Γ, M.Satisfies x (Formula.dia () γ)) ∧ M.Satisfies x tail := by
  induction Γ with
  | nil => simp [renderDiamonds]
  | cons γ Γ ih =>
      change (M.Satisfies x (Formula.dia () γ) ∧
        M.Satisfies x (renderDiamonds Γ tail)) ↔
        (∀ a ∈ γ :: Γ, M.Satisfies x (Formula.dia () a)) ∧ M.Satisfies x tail
      rw [ih]
      simp [List.mem_cons, and_assoc]

theorem satisfies_renderClause {World : Type u} (M : Model World Atom Unit)
    (x : World) (c : Clause Atom Unit) :
    M.Satisfies x (renderClause c) ↔ c.Holds M x () := by
  rw [renderClause, satisfies_renderBoxes, satisfies_renderDiamonds]
  constructor
  · rintro ⟨hB, hD, hα⟩
    exact ⟨hα, hB, hD⟩
  · rintro ⟨hα, hB, hD⟩
    exact ⟨hB, hD, hα⟩

theorem satisfies_render [Inhabited Atom] {World : Type u}
    (M : Model World Atom Unit) (x : World)
    (cs : List (Clause Atom Unit)) :
    M.Satisfies x (render cs) ↔ Holds cs M x () := by
  induction cs with
  | nil => simp [render, Holds]
  | cons c cs ih =>
      rw [render, Model.satisfies_or, satisfies_renderClause, ih]
      constructor
      · intro h
        rcases h with hc | hcs
        · exact ⟨c, by simp, hc⟩
        · obtain ⟨d, hd, hdHolds⟩ := hcs
          exact ⟨d, by simp [hd], hdHolds⟩
      · rintro ⟨d, hd, hdHolds⟩
        rcases List.mem_cons.mp hd with rfl | htail
        · exact Or.inl hdHolds
        · exact Or.inr ⟨d, htail, hdHolds⟩

/-- The normalized object-language formula is equivalent to the input in
every single-agent K model. -/
theorem rendered_positive_equivalent [Inhabited Atom]
    (φ : Formula Atom Unit) {World : Type u}
    (M : Model World Atom Unit) (x : World) :
    M.Satisfies x φ ↔ M.Satisfies x (render (positive φ)) :=
  (positive_equivalent φ M x).trans (satisfies_render M x (positive φ)).symm

/-- Theorem 2(1) with the normal form constructed from the input formula. -/
theorem unknowable_K_iff_normalized {A : Type} [Inhabited A]
    (φ : Formula A Unit) :
    (¬ ∃ (V : Type) (M : Model V A Unit) (x : V),
      M.Satisfies x φ ∧ M.Satisfies x (.box () φ)) ↔
    (∀ c ∈ positive φ,
      ¬ DNF.SatisfiableK.{0} c.alpha ∨
        ∃ γ ∈ c.diamonds,
          ¬ DNF.CompatibleK.{0} c.boxes [φ, γ]) :=
  DNF.unknowable_K_iff (positive φ) φ ()
    (fun M x => positive_equivalent φ M x)

/-- Theorem 2(2) with the normal form constructed from the input formula. -/
theorem unknowable_KD_iff_normalized {A : Type} [Inhabited A]
    (φ : Formula A Unit) :
    (¬ ∃ (V : Type) (M : Model V A Unit) (x : V),
      Frame.Serial (M.rel ()) ∧
      M.Satisfies x φ ∧ M.Satisfies x (.box () φ)) ↔
    (∀ c ∈ positive φ,
      ¬ DNF.SatisfiableKD.{0} () c.alpha ∨
        ¬ DNF.CompatibleKD.{0} () c.boxes [φ] ∨
        ∃ γ ∈ c.diamonds,
          ¬ DNF.CompatibleKD.{0} () c.boxes [φ, γ]) :=
  DNF.unknowable_KD_iff (positive φ) φ ()
    (fun M x => positive_equivalent φ M x)

end DNFNormalization
end SourcesOfUnknowability
