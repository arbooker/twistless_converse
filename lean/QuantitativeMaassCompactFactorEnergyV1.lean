module

public import QuantitativeMaassRectangularKernelIdealV1
public import QuantitativeMaassFiniteEnergyCompositionV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped ENNReal

namespace QuantitativeMaass

/-- A compact-input column factor supplies all finiteness in the
cross-quotient kernel estimate. No global L2 hypothesis on the original
infinite-volume source columns is introduced. -/
theorem kernel_compact_factor_column_energy_le {α β H ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Countable ι]
    (μ : Measure α) (ν : Measure β) (basis : HilbertBasis ι ℂ H)
    (K : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (c : α → Lp ℂ 2 μ)
    (hc : ∀ v : Lp ℂ 2 μ, K v=ᵐ[μ](fun z => inner ℂ (c z) v))
    (q : β → H) (hq : MemLp q 2 ν) (C : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) :
    (∫⁻ z, ENNReal.ofReal
      (‖(finiteEnergyColumnOperator ν q hq).adjoint (C.adjoint (c z))‖^2) ∂μ) ≤
      ENNReal.ofReal (‖K‖^2)*ENNReal.ofReal (‖C‖^2)*
        ∫⁻ w, ENNReal.ofReal (‖q w‖^2) ∂ν := by
  let R := finiteEnergyColumnOperator ν q hq
  have he := column_input_energy_trace μ basis K c hc (C.comp R)
  simp only [adjoint_comp,comp_apply] at he
  rw [← he]
  have hcenergy := finiteEnergyColumn_composition_energy ν q hq basis 1 C
  simp only [one_apply_eq_self,adjoint_one] at hcenergy
  calc
    _ ≤ ENNReal.ofReal (‖K‖^2)*(∑' i, ENNReal.ofReal (‖C (R (basis i))‖^2)) := by
      rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro i
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_pow,comp_apply] using
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
          (K.le_opNorm (C (R (basis i))))
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcenergy
        (show 0≤ENNReal.ofReal (‖K‖^2) from zero_le)

/-- A concrete restriction-packet operator can be substituted from its
pointwise kernel representation, rather than assumed equal to a model. -/
theorem finiteEnergyColumnOperator_eq_of_kernel {β H : Type*} [MeasurableSpace β]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ν : Measure β) (q : β → H) (hq : MemLp q 2 ν)
    (R : H →L[ℂ] Lp ℂ 2 ν)
    (hR : ∀ v, R v=ᵐ[ν](fun z => inner ℂ (q z) v)) :
    finiteEnergyColumnOperator ν q hq=R := by
  ext v : 1
  apply Lp.ext
  exact (finiteEnergyColumnOperator_coeFn ν q hq v).trans (hR v).symm

#print axioms kernel_compact_factor_column_energy_le
#print axioms finiteEnergyColumnOperator_eq_of_kernel

end QuantitativeMaass
