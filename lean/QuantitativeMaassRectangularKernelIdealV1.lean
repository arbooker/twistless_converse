module

public import QuantitativeMaassColumnInputTraceV1
public import QuantitativeMaassRectangularIdealV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped ENNReal

namespace QuantitativeMaass

/-- A bounded kernel operator acts on a Hilbert-Schmidt input with only
its operator norm as cost. The original column family need not have
finite total energy on the infinite-volume source. -/
theorem kernel_transformed_column_energy_le {α H ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Countable ι]
    (μ : Measure α) (basis : HilbertBasis ι ℂ H)
    (K : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (c : α → Lp ℂ 2 μ)
    (hc : ∀ v : Lp ℂ 2 μ, K v=ᵐ[μ](fun z => inner ℂ (c z) v))
    (A : H →L[ℂ] Lp ℂ 2 μ) (hA : Summable (fun i => ‖A (basis i)‖^2)) :
    (∫⁻ z, ENNReal.ofReal (‖A.adjoint (c z)‖^2) ∂μ) ≤
      ENNReal.ofReal (‖K‖^2*(∑' i, ‖A (basis i)‖^2)) := by
  rw [← column_input_energy_trace μ basis K c hc A]
  have hpoint (i : ι) : ‖K (A (basis i))‖^2 ≤ ‖K‖^2*‖A (basis i)‖^2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (K.le_opNorm (A (basis i)))
  calc
    _ ≤ ∑' i, ENNReal.ofReal (‖K‖^2*‖A (basis i)‖^2) :=
      ENNReal.tsum_le_tsum (fun i => ENNReal.ofReal_le_ofReal (hpoint i))
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hA.mul_left (‖K‖^2)),tsum_mul_left]

/-- The compact input factor can be estimated from the opposite side
without identifying the source and target Hilbert spaces. -/
theorem kernel_transformed_column_energy_le_adjoint {α H ι κ : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Countable ι]
    (μ : Measure α) (basis : HilbertBasis ι ℂ H)
    (sourceBasis : HilbertBasis κ ℂ (Lp ℂ 2 μ))
    (K : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (c : α → Lp ℂ 2 μ)
    (hc : ∀ v : Lp ℂ 2 μ, K v=ᵐ[μ](fun z => inner ℂ (c z) v))
    (B : Lp ℂ 2 μ →L[ℂ] H) (hB : Summable (fun j => ‖B (sourceBasis j)‖^2)) :
    (∫⁻ z, ENNReal.ofReal (‖B (c z)‖^2) ∂μ) ≤
      ENNReal.ofReal (‖K‖^2*(∑' j, ‖B (sourceBasis j)‖^2)) := by
  obtain ⟨hs,he⟩ := rectangular_adjoint_energy_eq sourceBasis basis B hB
  have hh := kernel_transformed_column_energy_le μ basis K c hc B.adjoint hs
  simpa only [adjoint_adjoint,he] using hh

#print axioms kernel_transformed_column_energy_le
#print axioms kernel_transformed_column_energy_le_adjoint

end QuantitativeMaass
