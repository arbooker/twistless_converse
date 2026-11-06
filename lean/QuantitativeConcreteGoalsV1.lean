module

public import AsymptoticClassicalNewCuspV1
public import AsymptoticArithmeticNewCoefficientV1
public import AsymptoticSectorComparisonV1
public import FinitenessOriginalInputV1
public import GridAdmissibleGapV1
public import MaassEulerInputV1
public import QuantitativeHolomorphicShiftedScaleV1
public import QuantitativeMaassParametersV1

set_option autoImplicit false
@[expose] public noncomputable section

open Filter Asymptotics
open scoped Topology

/-!
Literal target statements for the two quantitative counting results.
The definitions in this file are propositions, not declarations asserting
them. The only theorem below is an explicitly conditional bridge. A complete
formalization must supply its concrete trace-bound input and prove the Maass
claim from the original Euler-product conditions.
-/

namespace QuantitativeConcreteGoals

def holomorphicError (N : ℕ) (hN : 0 < N) (k : ℕ) : ℝ :=
  ((FinitenessOriginalInput.S N k).ncard : ℝ) -
    (Module.finrank ℂ (AsymptoticClassicalCusp.newSpace N hN (k : ℤ)) : ℝ)

def HolomorphicCountClaim (N : ℕ) (hN : 0 < N) (δ : ℝ) : Prop :=
  holomorphicError N hN =O[AsymptoticSectorComparison.evenWeights]
    (fun k : ℕ => QuantitativeHolomorphic.shiftedRemainderScale δ (k : ℝ))

/-- The principal parameter is recorded as well as the coefficient sequence.
The restriction to nonnegative parameters avoids counting `r` and `-r` twice. -/
def maassWindow (N σ : ℕ) (t ε : ℝ) : Set (ℝ × (ℕ → ℂ)) :=
  {p | 0 ≤ p.1 ∧ p.1 ∈ Set.Icc t (t + ε) ∧
    MaassOriginal.IsEulerSolution N (.principal p.1) σ p.2}

/-- Eventual finiteness is part of the claim: `Set.ncard` alone would be
zero on an infinite set, which cannot express the counting theorem faithfully. -/
def MaassWindowClaim (N σ : ℕ) (ε : ℝ → ℝ) : Prop :=
  (∀ᶠ t in atTop, (maassWindow N σ t (ε t)).Finite) ∧
  Tendsto (fun t : ℝ => ((maassWindow N σ t (ε t)).ncard : ℝ) / (t * ε t))
    atTop (𝓝 (AsymptoticTotalNewCorner.arithmeticCoefficient N))

def RequestedHolomorphicCountTheorem : Prop :=
  ∀ (N : ℕ) (hN : GridAdmissibleGap.Admissible N) (δ : ℝ), δ < 1 / 2 →
    HolomorphicCountClaim N hN.1 δ

def RequestedMaassWindowTheorem : Prop :=
  ∀ (N : ℕ), GridAdmissibleGap.Admissible N → ∀ σ : ℕ, (σ = 0 ∨ σ = 1) →
    ∀ ε : ℝ → ℝ, (∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1) →
      Tendsto (fun t => ε t * QuantitativeMaass.slowScale t) atTop atTop →
      MaassWindowClaim N σ ε

/-- This reduction is deliberately conditional. The quantitative trace
estimate for the literal Euler count is the input still to be constructed. -/
theorem holomorphic_claim_of_trace_bound (N : ℕ) (hN : 0 < N) {δ : ℝ}
    (hδ : δ < 1 / 2)
    (hbound : QuantitativeHolomorphic.HasTwoParameterBoundAlong
      AsymptoticSectorComparison.evenWeights (holomorphicError N hN) δ) :
    HolomorphicCountClaim N hN δ :=
  (QuantitativeHolomorphic.isBigO_shiftedRemainderScale_iff inf_le_left
    (holomorphicError N hN) δ).mp
    (QuantitativeHolomorphic.isBigO_of_two_parameter_bound_along
      inf_le_left hδ hbound)

#print axioms holomorphic_claim_of_trace_bound

end QuantitativeConcreteGoals
