module

public import QuantitativeMaassWindowWideSharpCuspTailV1
public import QuantitativeMaassCuspidalProjectedTailV1
public import QuantitativeMaassLVCuspidalProjectionV1
public import QuantitativeMaassCuspColumnMeanV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand
open scoped Topology MatrixGroups SchwartzMap FourierTransform ENNReal

namespace QuantitativeMaass

/-- The actual cusp projection satisfies the sharp full cusp-tail estimate
needed by the finite eigenmoment cutoff comparison. -/
theorem cuspidal_window_column_sharp_tail (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B : ℝ,0<B ∧ ∀ (N : ℕ) [NeZero N],∀ hN : 0<N,∀ (R : ℝ) (hR : 0<R) (a b : ℝ)
      (A : SL(2,ℤ)) (H : ℝ),0<H → B*R<Real.log H →
      (∫⁻ z in cuspTailSet N H,
        ENNReal.ofReal (‖localCuspidalProjection N hN
          (windowAbelColumn N K he hc R hR a b (cuspAction A z))‖^2))≤
        ENNReal.ofReal (2*(Fintype.card (cuspAdmissibleResidues N A):ℝ))*
          ((N:ℝ≥0∞)*(ENNReal.ofReal H⁻¹*ENNReal.ofReal (windowTimeSquareProfile K hc R hR a b 1).re)) := by
  obtain ⟨B,hB,hbound⟩ := windowAbelColumn_centered_sharp_wide_cusp_tail K he hc
  refine ⟨B,hB,?_⟩
  intro N _ hN R hR a b A H hH hheight
  apply le_trans _ (hbound N hN R hR a b A H hH hheight)
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (norm_nonneg _)
    (localCuspidalProjection_window_column_bound N hN K he hc R hR a b A
      (Real.log z.im) (cuspAction A z)) 2

#print axioms cuspidal_window_column_sharp_tail

end QuantitativeMaass
