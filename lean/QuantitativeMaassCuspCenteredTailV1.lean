module

public import QuantitativeMaassCuspTailVolumeV1
public import QuantitativeMaassCenteredWindowGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand
open scoped Topology ContDiff InnerProductSpace MatrixGroups SchwartzMap FourierTransform ENNReal

namespace QuantitativeMaass

/-- Recover every actual cusp-chart point from logarithmic period coordinates. -/
theorem cuspLogPoint_recover (N : ℕ) (hN : 0<N) (A : SL(2,ℤ)) (z : ℍ) :
    cuspLogPoint N A (Real.log z.im) (z.re/(N:ℝ))=cuspAction A z := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hp : horocyclePoint ((N:ℝ)*(z.re/(N:ℝ))) (Real.exp (Real.log z.im))
      (Real.exp_pos (Real.log z.im))=z := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change (N:ℝ)*(z.re/(N:ℝ))=z.re
      field_simp
    · change Real.exp (Real.log z.im)=z.im
      exact Real.exp_log z.im_pos
  unfold cuspLogPoint
  rw [hp]
  rfl

/-- Any bounded nonnegative energy on the actual cusp strip has an inverse-height
integral bound in genuine hyperbolic measure. No coordinate measure is substituted. -/
theorem cuspTail_lintegral_bounded (W : ℕ) (Y C : ℝ) (hY : 0<Y) (hC : 0≤C)
    (F : ℍ → ℝ) (hb : ∀ z∈cuspTailSet W Y,F z≤C) :
    (∫⁻ z in cuspTailSet W Y,ENNReal.ofReal (F z))≤ENNReal.ofReal (C*(W:ℝ)/Y) := by
  calc
    _ ≤ ∫⁻ _z in cuspTailSet W Y,ENNReal.ofReal C := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (cuspTailSet_measurable W Y)] with z hz
      exact ENNReal.ofReal_le_ofReal (hb z hz)
    _ = ENNReal.ofReal C*volume (cuspTailSet W Y) := by
      rw [lintegral_const,Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal ((W:ℝ)/Y) :=
      by gcongr;exact cuspTailSet_volume_bound W Y hY
    _ = _ := by
      rw [← ENNReal.ofReal_mul hC]
      congr 1
      ring

/-- Quantitative integrated energy for the centered actual window column on
an entire infinite cusp tail, at every positive level and every integral cusp. -/
theorem windowAbelColumn_centered_tail_growth (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ H B D : ℝ,0<H ∧ 0<B ∧ 0<D ∧ ∀ (N : ℕ) [NeZero N],0<N →
      ∀ R : ℝ,∀ hR : 1≤R,∀ ε : ℝ,0≤ε → ε≤1 → ∀ t : ℝ,1≤t →
      ∀ (A : SL(2,ℤ)) (Y : ℝ),0<Y → H*R<Real.log Y →
      (∫⁻ z in cuspTailSet N Y,ENNReal.ofReal (
        ‖windowAbelColumn N K he hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) (cuspAction A z)-
          cuspColumnMean N (windowAbelColumn N K he hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)) A (Real.log z.im)‖^2))≤
        ENNReal.ofReal ((Fintype.card (cuspAdmissibleResidues N A):ℝ)*D*R^2*ε^2*
          ((Real.cosh (B*R)+1)^2+t*Real.sqrt t*(Real.sqrt (B*R)+1))*(N:ℝ)/Y) := by
  obtain ⟨H,B,D,hH,hB,hD,hbound⟩ := windowAbelColumn_high_centered_growth K he hc
  refine ⟨H,B,D,hH,hB,hD,?_⟩
  intro N _ hN R hR ε hε hε1 t ht A Y hY hhigh
  apply cuspTail_lintegral_bounded N Y _ hY (by positivity)
  intro z hz
  have hlog : Real.log Y≤Real.log z.im := Real.log_le_log hY hz.2
  have hh := hbound N hN R hR ε hε hε1 t ht A (Real.log z.im) (hhigh.trans_le hlog) (z.re/(N:ℝ))
  rw [cuspLogPoint_recover N hN A z] at hh
  exact hh

#print axioms cuspLogPoint_recover
#print axioms cuspTail_lintegral_bounded
#print axioms windowAbelColumn_centered_tail_growth

end QuantitativeMaass
