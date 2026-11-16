module

public import QuantitativeMaassFiniteEnergyPerturbationV1
public import Mathlib.Analysis.InnerProductSpace.Trace

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open scoped BigOperators

namespace QuantitativeMaass

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Fintype ι]

/-- Finite-band trace error is controlled by its squared Hilbert--Schmidt
error and the band dimension. -/
theorem finiteBandEnergy_trace_square (b : OrthonormalBasis ι ℂ E) (A : E →L[ℂ] E) :
    ((LinearMap.trace ℂ E A.toLinearMap).re)^2 ≤
      (Fintype.card ι:ℝ)*finiteBandEnergy b A := by
  classical
  have ht : |(LinearMap.trace ℂ E A.toLinearMap).re|≤∑ i,‖A (b i)‖ := by
    rw [LinearMap.trace_eq_sum_inner _ b,Complex.re_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Complex.abs_re_le_norm _).trans
    have hh := norm_inner_le_norm (𝕜 := ℂ) (b i) (A (b i))
    simpa only [ContinuousLinearMap.coe_coe,b.orthonormal.norm_eq_one i,one_mul] using hh
  have hh := pow_le_pow_left₀ (abs_nonneg _) ht 2
  rw [sq_abs] at hh
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : ι => (1:ℝ)) (fun i => ‖A (b i)‖)
  exact hh.trans (by simpa [finiteBandEnergy] using hc)

theorem finiteBandEnergy_observed_trace_square [CompleteSpace E]
    (b : OrthonormalBasis ι ℂ E) (T A : E →L[ℂ] E) :
    ((LinearMap.trace ℂ E (T*A).toLinearMap).re)^2 ≤
      (Fintype.card ι:ℝ)*‖T‖^2*finiteBandEnergy b A := by
  exact (finiteBandEnergy_trace_square b (T*A)).trans
    ((mul_le_mul_of_nonneg_left (finiteBandEnergy_left b T A) (Nat.cast_nonneg _)).trans_eq
      (by ring))

#print axioms finiteBandEnergy_trace_square
#print axioms finiteBandEnergy_observed_trace_square

end QuantitativeMaass
