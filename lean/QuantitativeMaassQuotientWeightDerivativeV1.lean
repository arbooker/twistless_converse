module

public import QuantitativeMaassQuotientWeightPlaneV1
public import Mathlib.Analysis.Calculus.Rademacher

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Rademacher's theorem applies to the actual orbit weight in coordinates
on the upper half-plane. -/
theorem quotientWeightPlane_ae_differentiable (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    ∀ᵐ Z : ℝ×ℝ ∂volume,0<Z.2 → DifferentiableAt ℝ (quotientWeightPlane N ε v) Z := by
  have hh (n : ℕ) : ∀ᵐ Z : ℝ×ℝ ∂volume, Z∈{Z : ℝ×ℝ | 1/(n+1:ℝ)<Z.2} →
      DifferentiableWithinAt ℝ (quotientWeightPlane N ε v)
        {Z : ℝ×ℝ | 1/(n+1:ℝ)<Z.2} Z :=
    (quotientWeightPlane_lipschitzOn N hε hv (by positivity : 0<1/(n+1:ℝ))).ae_differentiableWithinAt_of_mem
  filter_upwards [ae_all_iff.mpr hh] with Z hZ hpos
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hpos
  exact (hZ n hn).differentiableAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hn)

/-- The coordinate derivative has a uniform hyperbolically scaled bound.
At nondifferentiability points the library derivative is zero; actual
differentiability almost everywhere is supplied separately above. -/
theorem quotientWeightPlane_derivative_bound (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (Z : ℝ×ℝ) (hZ : 0<Z.2) :
    Z.2*‖fderiv ℝ (quotientWeightPlane N ε v) Z‖≤4*quotientWeightBound ε*(2*v:ℝ) := by
  have hr : 0<Z.2/2 := by positivity
  have hm : {W : ℝ×ℝ | Z.2/2<W.2}∈𝓝 Z :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds (by dsimp; linarith)
  have hh := norm_fderiv_le_of_lipschitzOn ℝ hm (quotientWeightPlane_lipschitzOn N hε hv hr)
  change ‖fderiv ℝ (quotientWeightPlane N ε v) Z‖≤2*quotientWeightBound ε*(2*v:ℝ)/(Z.2/2) at hh
  have he := (le_div_iff₀ hr).mp hh
  nlinarith

#print axioms quotientWeightPlane_ae_differentiable
#print axioms quotientWeightPlane_derivative_bound

end QuantitativeMaass
