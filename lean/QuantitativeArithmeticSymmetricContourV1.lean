module
public import FinitenessContourShiftV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSymmetricContour
open Complex MeasureTheory Filter FinitenessContourShift
open scoped Topology

/-- Cauchy's rectangle argument needs only symmetric vertical limits;
absolute convergence of the entire regular part is unnecessary. -/
theorem equal_limits {F : ℂ → ℂ} (hF : Differentiable ℂ F) (a b : ℝ)
    (A B : ℂ)
    (ha : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T,F ((a:ℂ)+(t:ℂ)*I)) atTop (𝓝 A))
    (hb : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T,F ((b:ℂ)+(t:ℂ)*I)) atTop (𝓝 B))
    (hu : Tendsto (horizontal F a b) atTop (𝓝 0))
    (hd : Tendsto (fun T : ℝ => horizontal F a b (-T)) atTop (𝓝 0)) : A=B := by
  let V (x T : ℝ) : ℂ := ∫ t : ℝ in -T..T,F ((x:ℂ)+(t:ℂ)*I)
  have he (T : ℝ) : horizontal F a b (-T)-horizontal F a b T+I*V b T-I*V a T=0 := by
    have hh := integral_boundary_rect_eq_zero_of_differentiableOn F
      ((a:ℂ)+((-T:ℝ):ℂ)*I) ((b:ℂ)+(T:ℂ)*I) hF.differentiableOn
    simpa [horizontal,V,smul_eq_mul] using hh
  have hl := ((hd.sub hu).add (hb.const_mul I)).sub (ha.const_mul I)
  have hz : Tendsto (fun T : ℝ => horizontal F a b (-T)-horizontal F a b T+I*V b T-I*V a T)
      atTop (𝓝 0) := by simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0))
  have hh := tendsto_nhds_unique hl hz
  simp only [sub_self,zero_add] at hh
  have hm : I*(B-A)=0 := by simpa only [mul_sub] using hh
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left I_ne_zero)).symm

/-- Uniform decay along the horizontal edges, only for sufficiently large
height, is enough. -/
theorem horizontal_zero_of_eventual_bound {F : ℂ → ℂ} {a b : ℝ} (hab : a≤b)
    (B : ℝ → ℝ) (hB : Tendsto B atTop (𝓝 0))
    (h : ∀ᶠ T : ℝ in atTop,∀ x : ℝ,a≤x → x≤b → ‖F ((x:ℂ)+(T:ℂ)*I)‖≤B T) :
    Tendsto (horizontal F a b) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa using hB.mul_const |b-a|)
  filter_upwards [h] with T hT
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  rw [Set.uIoc_of_le hab] at hx
  exact hT x hx.1.le hx.2
#print axioms equal_limits
#print axioms horizontal_zero_of_eventual_bound
end QuantitativeArithmeticSymmetricContour
