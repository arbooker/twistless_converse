module

public import QuantitativeMaassIntegralMatrixMotionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeArithmeticMaassOverlap
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- Actual hyperbolic volume integral bound for the original window along every
fixed positive integral correspondence. All matrix-size factors are explicit. -/
theorem windowIntegralRemainder_raw_integrated_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀ (N : ℕ) [NeZero N]
      (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
      (o : ℍ) (L R ε t : ℝ) (hR : 1≤R),0≤ε → ε≤1 → 1≤t →
    IntegrableOn (windowIntegralRemainder N M hM K hc R
      (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)) (Metric.closedBall o L) ∧
    (∫ z in Metric.closedBall o L,‖windowIntegralRemainder N M hM K hc R
      (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z‖)≤
      (energyMultiplicity o 0 (2*(U*R)+2*L+dist (positiveIntegralGL M hM • o) o):ℝ)*
        (C*Real.sqrt t*R^2*ε^2)*
        (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L
          (2*(U*R)+2*L+dist (positiveIntegralGL M hM • o) o+2*Real.log (2*integralMatrixHeight M)))) := by
  obtain ⟨U,hU,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  obtain ⟨C,hC,hbound⟩ := windowTimeSquare_abel_decay K he hc
  refine ⟨U,C,hU,hC,?_⟩
  intro N _ M hM o L R ε t hR hε hε1 ht
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hheight := integralMatrixHeight_bounds M
  have hB : 0< integralMatrixHeight M := lt_of_lt_of_le zero_lt_one hheight.1
  let f := windowTimeSchwartz K hc R hRp (t-ε) (t+ε)
  have hfs : Function.support (f : ℝ → ℂ)⊆Icc (-(U*R)) (U*R) := hs R hRp (t-ε) (t+ε)
  have hgs : Function.support (timeConvolution f f : ℝ → ℂ)⊆Icc (-(2*(U*R))) (2*(U*R)) := by
    simpa only [two_mul] using timeConvolution_support f f (U*R) (U*R) hfs hfs
  have hps : Function.support (windowSquareProfile K hc R hRp ε t)⊆Iic (Real.cosh (2*(U*R))) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity) hgs)
  apply radialIntegralRemainder_integral_bound N M hM (integralMatrixHeight M) hB hheight.2
    o L (2*(U*R)) (by positivity) (windowSquareProfile K hc R hRp ε t)
    (windowSquareProfile_continuous K he hc R hRp ε t) hps (C*Real.sqrt t*R^2*ε^2) (by positivity)
  intro d hd
  exact hbound R ε t d hR hε hε1 ht hd

/-- Uniform geometry with all correspondence dependence retained in the exponential. -/
theorem correspondence_geometry_uniform_exp (o : ℍ) :
    ∃ C : ℝ,0<C ∧ ∀ L D δ b : ℝ,0≤L → 0≤D → 0≤δ → 0≤b →
      (energyMultiplicity o 0 (D+δ):ℝ)*
        (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L (D+δ+b)))≤
      C*Real.exp (10*(D+L+δ+b)) := by
  obtain ⟨A,hA,ha⟩ := energyMultiplicity_exp o
  obtain ⟨B,hB,hbound⟩ := hyperbolicSublevelConstant_exp o
  refine ⟨A*Real.pi*(Real.pi+B),by positivity,?_⟩
  intro L D δ b hL hD hδ hb
  have hDp : 0≤D+δ+b := by positivity
  have he4 : Real.exp (4*(D+δ))≤Real.exp (4*(D+δ+b+L)) := Real.exp_le_exp.mpr (by linarith)
  have heL : Real.exp (4*L)≤Real.exp (6*(D+δ+b+L)) := Real.exp_le_exp.mpr (by linarith)
  have hv := (centre_ball_volume_exp o L).trans (mul_le_mul_of_nonneg_left heL Real.pi_pos.le)
  have hQ := hyperbolicSublevelConstant_nonneg o L (D+δ+b)
  calc
    _ ≤ (A*Real.exp (4*(D+δ+b+L)))*(Real.pi*((Real.pi+B)*Real.exp (6*(D+δ+b+L)))) := by
      apply mul_le_mul ((ha (D+δ) (by positivity)).trans (mul_le_mul_of_nonneg_left he4 hA.le)) _
        (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      nlinarith [hbound L (D+δ+b) hL hDp]
    _ = (A*Real.pi*(Real.pi+B))*(Real.exp (4*(D+δ+b+L))*Real.exp (6*(D+δ+b+L))) := by ring
    _ = _ := by
      rw [←Real.exp_add]
      congr 1
      congr 1
      ring

#print axioms windowIntegralRemainder_raw_integrated_bound
#print axioms correspondence_geometry_uniform_exp

end QuantitativeMaass
