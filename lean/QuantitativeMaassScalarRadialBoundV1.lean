module

public import QuantitativeMaassClassicalRadialEquationV1
public import QuantitativeMaassPositiveTimeSeminormV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Compact radial convolution only uses a bound on the corresponding ball. -/
theorem radial_convolution_norm_bound (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ) (B : ℝ)
    (hb : ∀ y ∈ Metric.closedBall x R,‖f y‖≤B) :
    ‖∫ y : ℍ,g (Real.cosh (dist y x))*f y‖≤
      (2*Real.pi*(∫ q in Ioi (1:ℝ),‖g q‖))*B := by
  have hi := radial_convolution_integrable g hg R hR hs f hf x
  have hj := hyperbolic_radial_integrable g hg.continuous x R hR hs
  calc
    _ ≤ ∫ y : ℍ,‖g (Real.cosh (dist y x))*f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℍ,‖g (Real.cosh (dist y x))‖*B := by
      apply integral_mono hi.norm (hj.norm.mul_const B)
      intro y
      dsimp only
      rw [norm_mul]
      by_cases hz : g (Real.cosh (dist y x))=0
      · simp [hz]
      · apply mul_le_mul_of_nonneg_left (hb y ?_) (norm_nonneg _)
        have hh := Real.cosh_le_cosh.mp (hs hz)
        rw [abs_of_nonneg dist_nonneg,abs_of_nonneg hR] at hh
        exact hh
    _ = _ := by rw [integral_mul_const,integral_hyperbolic_radial_norm]

/-- Literal pointwise convolution against a positive-time Abel test. -/
def scalarPositiveAbel (f : ℍ → ℂ) (x : ℍ) (ψ : PositiveTimeTest) : ℂ :=
  ∫ y : ℍ,abelProfile ψ.lift (Real.cosh (dist y x))*f y

theorem scalarPositiveAbel_congr (f : ℍ → ℂ) (x : ℍ)
    (ψ θ : PositiveTimeTest) (he : ψ.toFun=θ.toFun) :
    scalarPositiveAbel f x ψ=scalarPositiveAbel f x θ := by
  have hl : ψ.lift=θ.lift := congrArg coshTestLift he
  simp only [scalarPositiveAbel,hl]

theorem scalarPositiveAbel_norm_common (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ)
    (ψ : PositiveTimeTest) (δ R C B : ℝ) (hδ : 0<δ) (hR : 0≤R) (hB : 0≤B)
    (hs : Function.support ψ.toFun⊆Icc δ R) (hb : ∀ t,‖deriv ψ.toFun t‖≤C)
    (hfB : ∀ y ∈ Metric.closedBall x R,‖f y‖≤B) :
    ‖scalarPositiveAbel f x ψ‖≤(B*positiveTimeNormConstant δ R)*C := by
  have hsF : Function.support ψ.lift⊆Iic (Real.cosh R) :=
    fun _ h => (coshTestLift_support ψ.toFun δ R hδ hR hs h).2
  have h := radial_convolution_norm_bound (abelProfile ψ.lift)
    (abelProfile_smooth _ ψ.lift_smooth ψ.lift_compact) R hR
    (abelProfile_support _ _ hsF) f hf x B hfB
  have hm := abelProfile_absolute_mass_bound ψ.lift (Real.cosh R)
    (C/Real.sinh δ) (Real.one_le_cosh R) hsF
    (coshTestLift_deriv_bound ψ.toFun ψ.smooth δ R C hδ hs hb)
  calc
    _ ≤ _ := h
    _ ≤ (2*Real.pi*((Real.sqrt 2/Real.pi)*((C/Real.sinh δ)*(Real.cosh R+1))*
        (Real.cosh R-1)))*B := mul_le_mul_of_nonneg_right hm hB
    _ = _ := by unfold positiveTimeNormConstant; ring

theorem scalarPositiveAbel_scaledSub (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ)
    (ψ θ : PositiveTimeTest) (c : ℝ) :
    scalarPositiveAbel f x (ψ.scaledSub θ c)=
      c • scalarPositiveAbel f x ψ-scalarPositiveAbel f x θ := by
  have he : (ψ.scaledSub θ c).lift=(fun q => (c:ℂ)*ψ.lift q-θ.lift q) :=
    coshTestLift_scaledSub _ _ _
  have hp (q : ℝ) : abelProfile (ψ.scaledSub θ c).lift q=
      (c:ℂ)*abelProfile ψ.lift q-abelProfile θ.lift q := by
    rw [he,abelProfile_sub _ _ (contDiff_const.mul ψ.lift_smooth) θ.lift_smooth
      ψ.lift_compact.mul_left θ.lift_compact,abelProfile_const_mul]
  have hi := radial_convolution_integrable (abelProfile ψ.lift)
    (abelProfile_smooth _ ψ.lift_smooth ψ.lift_compact) ψ.right ψ.right_nonneg
    (abelProfile_support _ _ ψ.lift_support) f hf x
  have hj := radial_convolution_integrable (abelProfile θ.lift)
    (abelProfile_smooth _ θ.lift_smooth θ.lift_compact) θ.right θ.right_nonneg
    (abelProfile_support _ _ θ.lift_support) f hf x
  simp only [scalarPositiveAbel,hp,sub_mul,mul_assoc]
  rw [integral_sub (hi.const_mul (c:ℂ)) hj,integral_const_mul]
  rfl

theorem continuous_ball_norm_bound (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ) (R : ℝ) :
    ∃ B : ℝ,0≤B ∧ ∀ y ∈ Metric.closedBall x R,‖f y‖≤B := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall x R).bddAbove_image hf.norm.continuousOn
  exact ⟨max C 0,le_max_right _ _,fun y hy => (hC (mem_image_of_mem _ hy)).trans (le_max_left _ _)⟩

#print axioms radial_convolution_norm_bound
#print axioms scalarPositiveAbel_congr
#print axioms scalarPositiveAbel_norm_common
#print axioms scalarPositiveAbel_scaledSub
#print axioms continuous_ball_norm_bound

end QuantitativeMaass
