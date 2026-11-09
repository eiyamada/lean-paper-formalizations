import PropertiesOfPALAndBPALOperators.Algebra

/-! Definition 8 for the two full dynamic languages. In PAL the announcement
modality retains its executability implication, including in the false-input
notions. These definitions are not silently replaced by BPAL postconditions. -/

namespace PropertiesOfPALAndBPALOperators

open ClassificationSigmaValidity

universe u v w
variable {Atom : Type v} {Agent : Type w}

def PalSuccessful (φ : PALFormula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent) x, PAL.InitiallySatisfies M x φ →
    PAL.InitiallySatisfies M x (.announce φ φ)

def PalSelfRefuting (φ : PALFormula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent) x, PAL.InitiallySatisfies M x φ →
    PAL.InitiallySatisfies M x (.announce φ (.neg φ))

def PalTrueLie (φ : PALFormula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent) x, ¬ PAL.InitiallySatisfies M x φ →
    PAL.InitiallySatisfies M x (.announce φ φ)

def PalImpossibleLie (φ : PALFormula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent) x, ¬ PAL.InitiallySatisfies M x φ →
    PAL.InitiallySatisfies M x (.announce φ (.neg φ))

def BpalSuccessful (φ : BPALFormula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent) x, BPAL.InitiallySatisfies M x φ →
    BPAL.InitiallySatisfies M x (.announce φ φ)

def BpalSelfRefuting (φ : BPALFormula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent) x, BPAL.InitiallySatisfies M x φ →
    BPAL.InitiallySatisfies M x (.announce φ (.neg φ))

def BpalTrueLie (φ : BPALFormula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent) x, ¬ BPAL.InitiallySatisfies M x φ →
    BPAL.InitiallySatisfies M x (.announce φ φ)

def BpalImpossibleLie (φ : BPALFormula Atom Agent) : Prop :=
  ∀ (W : Type u) (M : Model W Atom Agent) x, ¬ BPAL.InitiallySatisfies M x φ →
    BPAL.InitiallySatisfies M x (.announce φ (.neg φ))

theorem palSuccessful_iff_idempotent (φ : PALFormula Atom Agent) :
    PalSuccessful.{u} φ ↔ ∀ (W : Type u) (M : Model W Atom Agent),
      palUpdate M φ (palUpdate M φ Set.univ) = palUpdate M φ Set.univ := by
  simp only [pal_idempotent_iff_success, PalSuccessful, PAL.InitiallySatisfies,
    PAL.satisfies_announce]
  constructor
  · intro h W M x _ hφ
    exact h W M x hφ hφ
  · intro h W M x hφ _
    exact h W M x trivial hφ

theorem palSelfRefuting_iff_square_zero (φ : PALFormula Atom Agent) :
    PalSelfRefuting.{u} φ ↔ ∀ (W : Type u) (M : Model W Atom Agent),
      palUpdate M φ (palUpdate M φ Set.univ) = ∅ := by
  simp only [pal_square_zero_iff, PalSelfRefuting, PAL.InitiallySatisfies,
    PAL.satisfies_announce, PAL.satisfies_neg]
  constructor
  · intro h W M x _ hφ
    exact h W M x hφ hφ
  · intro h W M x hφ _
    exact h W M x trivial hφ

end PropertiesOfPALAndBPALOperators
