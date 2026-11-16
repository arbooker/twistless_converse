module

public import QuantitativeMaassColumnInputTraceV1
public import QuantitativeMaassIsometricCompressionV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory ContinuousLinearMap
open scoped ENNReal

namespace QuantitativeMaass

variable {α H ι : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Countable ι]

/-- Finiteness of the explicit projected-column integral suffices for
square summability of the actual operator after its input map. -/
theorem column_input_summable (μ : Measure α) (basis : HilbertBasis ι ℂ H)
    (K : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (c : α → Lp ℂ 2 μ)
    (hc : ∀ v : Lp ℂ 2 μ,K v=ᵐ[μ](fun x => inner ℂ (c x) v))
    (A : H →L[ℂ] Lp ℂ 2 μ)
    (hfinite : (∫⁻ x,ENNReal.ofReal (‖A.adjoint (c x)‖^2) ∂μ)<∞) :
    Summable (fun i => ‖K (A (basis i))‖^2) := by
  have ht : (∑' i,ENNReal.ofReal (‖K (A (basis i))‖^2))≠∞ := by
    rw [column_input_energy_trace μ basis K c hc A]
    exact hfinite.ne
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal ht

/-- Contractive output compression preserves the concrete column bound.
This is conditional on the displayed integral estimate, not a proof of it. -/
theorem column_compression_energy_bound (μ : Measure α) (basis : HilbertBasis ι ℂ H)
    (K : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (c : α → Lp ℂ 2 μ)
    (hc : ∀ v : Lp ℂ 2 μ,K v=ᵐ[μ](fun x => inner ℂ (c x) v))
    (A : H →L[ℂ] Lp ℂ 2 μ) (C : Lp ℂ 2 μ →L[ℂ] H) (hC : ‖C‖≤1)
    (hfinite : (∫⁻ x,ENNReal.ofReal (‖A.adjoint (c x)‖^2) ∂μ)<∞) :
    Summable (fun i => ‖C (K (A (basis i)))‖^2) ∧
      ENNReal.ofReal (hilbertSchmidtEnergy basis (C.comp (K.comp A)))≤
        ∫⁻ x,ENNReal.ofReal (‖A.adjoint (c x)‖^2) ∂μ := by
  have hp (i : ι) : ‖C (K (A (basis i)))‖^2≤‖K (A (basis i))‖^2 := by
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc
      ‖C (K (A (basis i)))‖≤‖C‖*‖K (A (basis i))‖ := C.le_opNorm _
      _≤1*‖K (A (basis i))‖ := mul_le_mul_of_nonneg_right hC (norm_nonneg _)
      _=‖K (A (basis i))‖ := one_mul _
  have hs := column_input_summable μ basis K c hc A hfinite
  have hsC := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hp hs
  refine ⟨hsC,?_⟩
  rw [←column_input_energy_trace μ basis K c hc A]
  unfold hilbertSchmidtEnergy
  simp only [ContinuousLinearMap.comp_apply]
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsC]
  exact ENNReal.tsum_le_tsum (fun i => ENNReal.ofReal_le_ofReal (hp i))

#print axioms column_input_summable
#print axioms column_compression_energy_bound

end QuantitativeMaass
