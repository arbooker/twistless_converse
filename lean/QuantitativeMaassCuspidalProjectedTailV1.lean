module

public import QuantitativeMaassWindowSharpCuspTailV1
public import QuantitativeMaassLVCuspidalProjectionV1
public import QuantitativeMaassCuspColumnMeanV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology MatrixGroups SchwartzMap FourierTransform ENNReal

namespace QuantitativeMaass

theorem localCuspidalProjection_window_mean_zero (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (A : SL(2,ℤ)) (u : ℝ) :
    localCuspidalProjection N hN (cuspColumnMean N (windowAbelColumn N K he hc R hR a b) A u)=0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  intro v hv
  simpa only [sub_zero] using windowAbelColumn_mean_orthogonal N hN K he hc R hR a b A u v hv

theorem localCuspidalProjection_window_column_bound (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (A : SL(2,ℤ)) (u : ℝ) (z : ℍ) :
    ‖localCuspidalProjection N hN (windowAbelColumn N K he hc R hR a b z)‖≤
      ‖windowAbelColumn N K he hc R hR a b z-cuspColumnMean N (windowAbelColumn N K he hc R hR a b) A u‖ := by
  have hh := (localCuspidalSpace N hN).norm_starProjection_apply_le
    (windowAbelColumn N K he hc R hR a b z-cuspColumnMean N (windowAbelColumn N K he hc R hR a b) A u)
  change ‖localCuspidalProjection N hN (_-_)‖≤_ at hh
  rw [map_sub,localCuspidalProjection_window_mean_zero N hN K he hc R hR a b A u,sub_zero] at hh
  exact hh

/-- The actual cusp projection satisfies the sharp chart-tail estimate
needed by the finite eigenmoment cutoff comparison. -/
theorem cuspidal_window_column_sharp_chart_tail (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B : ℝ,0<B ∧ ∀ (N : ℕ) [NeZero N],∀ hN : 0<N,∀ (R : ℝ) (hR : 0<R) (a b : ℝ)
      (A : SL(2,ℤ)) (H : ℝ),0<H → B*R<Real.log H →
      (∫⁻ z in AsymptoticHyperbolicArea.closedTerminal H,
        ENNReal.ofReal (‖localCuspidalProjection N hN
          (windowAbelColumn N K he hc R hR a b (cuspLogPoint N A (Real.log z.im) z.re))‖^2))≤
        ENNReal.ofReal (2*(Fintype.card (cuspAdmissibleResidues N A):ℝ))*
          (ENNReal.ofReal H⁻¹*ENNReal.ofReal (windowTimeSquareProfile K hc R hR a b 1).re) := by
  obtain ⟨B,hB,hbound⟩ := windowAbelColumn_centered_sharp_cusp_tail K he hc
  refine ⟨B,hB,?_⟩
  intro N _ hN R hR a b A H hH hheight
  apply le_trans _ (hbound N hN R hR a b A H hH hheight)
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (norm_nonneg _)
    (localCuspidalProjection_window_column_bound N hN K he hc R hR a b A
      (Real.log z.im) (cuspLogPoint N A (Real.log z.im) z.re)) 2

#print axioms localCuspidalProjection_window_mean_zero
#print axioms localCuspidalProjection_window_column_bound
#print axioms cuspidal_window_column_sharp_chart_tail

end QuantitativeMaass
