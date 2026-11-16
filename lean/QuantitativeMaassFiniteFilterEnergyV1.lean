module

public import QuantitativeMaassFiniteEnergyPerturbationV1
public import QuantitativeMaassFiniteBandHilbertSchmidtV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Module

namespace QuantitativeMaass

theorem finiteBandEnergy_half_filter_le {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] [Fintype ι]
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric)
    (heig : ∀ i,0≤hS.eigenvalues rfl i ∧ hS.eigenvalues rfl i≤2)
    (m : ℕ) (b : OrthonormalBasis ι ℂ E) :
    finiteBandEnergy b (((1-(1/2:ℂ) • S)^m).toContinuousLinearMap-S.ker.starProjection) ≤
      (LinearMap.trace ℂ E ((1-(1/2:ℂ) • S)^m)).re-(finrank ℂ S.ker:ℝ) := by
  let D : E →L[ℂ] E := ((1-(1/2:ℂ) • S)^m).toContinuousLinearMap-S.ker.starProjection
  have hh := (finite_band_squared_sum_eq_trace D b).trans
    (finite_band_squared_sum_eq_trace D (hS.eigenvectorBasis rfl)).symm
  change finiteBandEnergy b D = _ at hh
  change finiteBandEnergy b D ≤ _
  rw [hh]
  exact half_filter_squared_error_le_trace S hS heig m

#print axioms finiteBandEnergy_half_filter_le

end QuantitativeMaass
