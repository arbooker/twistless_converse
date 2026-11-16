module

public import QuantitativeMaassWeightedEnergyCalculusV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Weighted

open QuantitativeArithmeticMaassGradient QuantitativeArithmeticMaassWave

private theorem rate_algebra {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a c d gx gy vx vy : H) (F : ℂ)
    (h : inner ℂ a d=inner ℂ vx gx+inner ℂ vy gy+2*F) :
    2*(inner ℂ a ((1/4 : ℂ) • c-d)).re+
      2*(inner ℂ gx vx).re+2*(inner ℂ gy vy).re+2*(inner ℂ c a).re=
      (5/2 : ℝ)*(inner ℂ c a).re-4*F.re := by
  have hr := congrArg Complex.re h
  have ha : (inner ℂ a c).re=(inner ℂ c a).re := by
    simpa only [RCLike.re_to_complex] using (inner_re_symm (𝕜 := ℂ) a c)
  have hx : (inner ℂ gx vx).re=(inner ℂ vx gx).re := by
    simpa only [RCLike.re_to_complex] using (inner_re_symm (𝕜 := ℂ) gx vx)
  have hy : (inner ℂ gy vy).re=(inner ℂ vy gy).re := by
    simpa only [RCLike.re_to_complex] using (inner_re_symm (𝕜 := ℂ) gy vy)
  simp only [inner_sub_right,inner_smul_right,Complex.sub_re,Complex.mul_re,Complex.add_re] at hr ⊢
  norm_num at hr ⊢
  linarith

/-- Exact weighted energy cancellation. The remaining terms are the mass
coupling and the first-order cutoff flux; no Laplacian term remains. -/
theorem energyRate_wave (N : ℕ) (b : Cutoff N) (u v : QuotientEnergySpace N)
    (y : AutomorphicSpace N) (hy : FriedrichsGraph N (energyInclusion N u) y) :
    energyRate N b u v (energyInclusion N v) ((1/4 : ℂ) • energyInclusion N u-y)=
      (5/2 : ℝ)*(inner ℂ (multiplier N b (ambientInclusion N u))
        (multiplier N b (ambientInclusion N v))).re-
      4*(inner ℂ (gradientMultiplier N b true (ambientInclusion N v))
          (multiplier N b (quotientGradient N true u))+
        inner ℂ (gradientMultiplier N b false (ambientInclusion N v))
          (multiplier N b (quotientGradient N false u))).re := by
  have he : graphEnergyLift N (energyInclusion N u) y=u :=
    energyInclusion_injective N (graphEnergyLift_value N hy)
  have hgreen := weighted_green N b hy v
  rw [he] at hgreen
  unfold energyRate
  simp only [Submodule.coe_sub,Submodule.coe_smul,map_sub,map_smul]
  exact rate_algebra
    (multiplier N b (ambientInclusion N v)) (multiplier N b (ambientInclusion N u))
    (multiplier N b y.val)
    (multiplier N b (quotientGradient N true u)) (multiplier N b (quotientGradient N false u))
    (multiplier N b (quotientGradient N true v)) (multiplier N b (quotientGradient N false v)) _ hgreen

#print axioms energyRate_wave

end QuantitativeMaass.Weighted
