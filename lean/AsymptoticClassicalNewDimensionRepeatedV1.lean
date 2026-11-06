module

public import AsymptoticClassicalMultiplicityRepeatedV1
public import AsymptoticClassicalFullDimensionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalDimension

open UpperHalfPlane Filter Asymptotics AsymptoticSectorComparison
open AsymptoticClassicalCusp AsymptoticCongruenceStrip
open scoped Topology

/-- The actual repeated-prime trace kernel has the classical second-difference
 leading coefficient. This statement uses only full cusp dimensions. -/
theorem twoKernel_dimension_littleO (L : ℕ) (hL : 0 < L) :
    (fun k : ℕ =>
      (Module.finrank ℂ (primeTraceKernel (2 * (2 * L)) (by omega) (k : ℤ)
        (repeatedPrime L 2 Nat.prime_two)) : ℝ) -
      (((gamma (2 * (2 * L))).relIndex (gamma 1) : ℝ) -
        2 * ((gamma (2 * L)).relIndex (gamma 1) : ℝ) +
        ((gamma L).relIndex (gamma 1) : ℝ)) * k / 12)
      =o[evenWeights] (fun k => (k : ℝ)) := by
  let I (N : ℕ) : ℝ := (gamma N).relIndex (gamma 1)
  let B (N : ℕ) : ℝ := I N * (I N + 1) + 1
  apply bounded_error_littleO _ (B (2 * (2 * L)) + 2 * B (2 * L) + B L)
  have hp : ∀ᶠ k in evenWeights, Even k :=
    Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr (fun _ h => h))
  have hlarge (N : ℕ) : ∀ᶠ k in evenWeights,
      12 * (gamma N).relIndex (gamma 1) ≤ k :=
    (eventually_ge_atTop _).filter_mono inf_le_left
  filter_upwards [hp, hlarge (2 * (2 * L)), hlarge (2 * L), hlarge L] with k hk hN hM hL'
  have htop := cusp_dimension_error (2 * (2 * L)) (by omega) k hk hN
  have hmid := cusp_dimension_error (2 * L) (by omega) k hk hM
  have hbot := cusp_dimension_error L hL k hk hL'
  have he := twoKernel_finrank L hL (k : ℤ)
  have heR :
      (Module.finrank ℂ (primeTraceKernel (2 * (2 * L)) (by omega) (k : ℤ)
        (repeatedPrime L 2 Nat.prime_two)) : ℝ) +
        2 * (Module.finrank ℂ (CuspForm (level (2 * L)) (k : ℤ)) : ℝ) =
      (Module.finrank ℂ (CuspForm (level (2 * (2 * L))) (k : ℤ)) : ℝ) +
        (Module.finrank ℂ (CuspForm (level L) (k : ℤ)) : ℝ) := by exact_mod_cast he
  change |_ - (I (2 * (2 * L)) - 2 * I (2 * L) + I L) * (k : ℝ) / 12| ≤ _
  change |_ - I (2 * (2 * L)) * (k : ℝ) / 12| ≤ B (2 * (2 * L)) at htop
  change |_ - I (2 * L) * (k : ℝ) / 12| ≤ B (2 * L) at hmid
  change |_ - I L * (k : ℝ) / 12| ≤ B L at hbot
  rw [abs_le] at htop hmid hbot ⊢
  constructor <;> nlinarith [htop.1, htop.2, hmid.1, hmid.2, hbot.1, hbot.2]

#print axioms twoKernel_dimension_littleO

end AsymptoticClassicalDimension
