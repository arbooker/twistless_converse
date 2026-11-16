module

public import QuantitativeMaassWindowVariationGrowthV1
public import QuantitativeMaassWindowCenteredVariationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace MatrixGroups SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- Unconditional quantitative high-cusp bound for the centered actual window
column. Every constant precedes the level, cusp and window parameters. -/
theorem windowAbelColumn_high_centered_growth (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ H B D : ℝ,0<H ∧ 0<B ∧ 0<D ∧ ∀ (N : ℕ) [NeZero N],0<N →
      ∀ R : ℝ,∀ hR : 1≤R,∀ ε : ℝ,0≤ε → ε≤1 → ∀ t : ℝ,1≤t →
      ∀ (A : SL(2,ℤ)) (u : ℝ),H*R<u → ∀ x : ℝ,
      ‖windowAbelColumn N K he hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) (cuspLogPoint N A u x)-
        cuspColumnMean N (windowAbelColumn N K he hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)) A u‖^2≤
      (Fintype.card (cuspAdmissibleResidues N A):ℝ)*D*R^2*ε^2*
        ((Real.cosh (B*R)+1)^2+t*Real.sqrt t*(Real.sqrt (B*R)+1)) := by
  obtain ⟨H,hH,hcenter⟩ := windowAbelColumn_high_centered_variation K he hc
  obtain ⟨B,D,hB,hD,hvar⟩ := windowTimeSquareProfile_variation_growth K he hc
  refine ⟨H,B,2*D,hH,hB,by positivity,?_⟩
  intro N _ hN R hR ε hε hε1 t ht A u hu x
  have hh := hcenter N hN R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) A u hu x
  apply hh.trans
  have hv := mul_le_mul_of_nonneg_left (hvar R hR ε hε hε1 t ht)
    (show 0≤2*(Fintype.card (cuspAdmissibleResidues N A):ℝ) by positivity)
  convert hv using 1
  ring

#print axioms windowAbelColumn_high_centered_growth

end QuantitativeMaass
