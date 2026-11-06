module

public import AsymptoticClassicalNewDimensionRepeatedV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalDimension

open AsymptoticCongruenceStrip

/-- The finite difference in the full dimension coefficient contributed by
 successively imposing the two old directions at each simply ramified prime. -/
def simpleDifference : List ℕ → (ℕ → ℝ) → ℕ → ℝ
  | [], C, N => C N
  | p :: ps, C, N => simpleDifference ps C N - 2 * simpleDifference ps C (N / p)

/-- The full classical cusp-space leading coefficient. -/
def fullLeading (N : ℕ) : ℝ := ((gamma N).relIndex (gamma 1) : ℝ) / 12

/-- The repeated-2 leading coefficient, formed from full cusp dimensions. -/
def twoLeading (N : ℕ) : ℝ :=
  (((gamma N).relIndex (gamma 1) : ℝ) -
    2 * ((gamma (N / 2)).relIndex (gamma 1) : ℝ) +
    ((gamma (N / 4)).relIndex (gamma 1) : ℝ)) / 12

end AsymptoticClassicalDimension
