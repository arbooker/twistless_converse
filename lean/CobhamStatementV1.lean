module

public import AutomaticSequencesV1
public import EventuallyPeriodicV1
public import IndependentBasesV1

@[expose] public section

namespace ClassicalCobham

/-- Ordinary Cobham for finite-valued sequences. Kept separate from the
common-factor application, so the theorem does not import that application. -/
def Statement : Prop := ∀ (A : Type) [Fintype A] (k l : ℕ),
  2≤k → 2≤l → IndependentBases.Independent k l → ∀ x : ℕ → A,
  AutomaticSequences.Automatic k x → AutomaticSequences.Automatic l x →
    ∃ p, 0<p ∧ BKKCommonFactor.EventuallyPeriodic p x

end ClassicalCobham
