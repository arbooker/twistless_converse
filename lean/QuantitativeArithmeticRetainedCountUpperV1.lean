module

public import QuantitativeArithmeticRetainedSectorEndpointV1
public import QuantitativeEulerEndpointEvenWeightV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight FinitenessOriginalInput
open AsymptoticSectorSigns AsymptoticSectorComparison AsymptoticCylinder Filter
open QuantitativeEulerEndpointHorizon
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A)

include A P

/-- The literal Euler count has the endpoint upper error over the exact
summed local-new coefficient. Original solutions, cover, independence,
and all analytic transfers are discharged. -/
theorem actual_count_endpoint_upper (hR₀ : ∀p∈R₀,p.Prime) (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) (hN2 : 2≤N) :
    ∃ B : ℝ,0≤B ∧ ∀ᶠ k : ℕ in evenWeights,
      ((S N k).ncard:ℝ)≤AsymptoticTotalNewCorner.coefficient N (NeZero.pos N)*(k:ℝ)+
        B*(k:ℝ)/Real.log (Real.log (k:ℝ)) := by
  obtain ⟨B,hB,hbound⟩ := actual_total_sector_endpoint A P hR₀ hdiv hbad hN2
  refine ⟨2*B,by positivity,?_⟩
  apply endpoint_upper_of_even_index _ _ B hB
  filter_upwards [hbound] with h hh
  have hc : ((S N (2*(h+1))).ncard:ℝ)≤
      ∑ e : Sector N,(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h
        (h+1+P.s) e):ℝ) := by
    have hcount := (QuantitativeArithmeticRetainedEulerCylinder.euler_count_le_cylinder_sectors A hR₀
      (NeZero.pos N) P hdiv hbad h (P.s+3) (by omega)).2
    simp only [QuantitativeArithmeticRetainedSectorReconstruction.cylinderSector_finrank] at hcount
    exact_mod_cast hcount
  exact (div_le_div_of_nonneg_right hc (by positivity : (0:ℝ)≤2*h+2)).trans hh

#print axioms actual_count_endpoint_upper
end QuantitativeArithmeticRetainedIteration
