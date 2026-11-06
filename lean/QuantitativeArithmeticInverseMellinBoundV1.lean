module
public import FinitenessMellinContourV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticInverseMellinBound
open Complex MeasureTheory Filter Asymptotics FinitenessMellinContour
open scoped Topology

theorem line_bound (F : ℂ → ℂ) (a : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ y : ℝ,0<y → ‖mellinInv a F y‖≤C*y^(-a) := by
  let C : ℝ := (1/(2*Real.pi))*(∫ t : ℝ,‖F ((a:ℂ)+(t:ℂ)*I)‖)
  have hC : 0≤C := mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _))
  refine ⟨C,hC,?_⟩
  intro y hy
  have hh := norm_integral_le_integral_norm (μ:=volume) (fun t : ℝ => kernel F (Real.log y) ((a:ℂ)+(t:ℂ)*I))
  simp only [kernel_norm,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] at hh
  rw [integral_const_mul] at hh
  rw [mellinInv_eq hy,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(1/(2*Real.pi):ℝ))]
  change (1/(2*Real.pi))*‖∫ t : ℝ,kernel F (Real.log y) ((a:ℂ)+(t:ℂ)*I)‖≤_
  have he : Real.exp (-Real.log y*a)=y^(-a) := by
    rw [Real.rpow_def_of_pos hy]
    congr 1
    ring
  rw [he] at hh
  have h := mul_le_mul_of_nonneg_left hh (by positivity : 0≤(1/(2*Real.pi):ℝ))
  dsimp [C]
  nlinarith

theorem line_isBigO (F : ℂ → ℂ) (a : ℝ) :
    (fun y : ℝ => mellinInv a F y)=O[𝓝[>] 0] (fun y : ℝ => y^(-a)) := by
  obtain ⟨C,_,h⟩ := line_bound F a
  apply IsBigO.of_bound C
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : 0<y := hy
  simpa only [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hy' _)] using h y hy'
#print axioms line_bound
#print axioms line_isBigO
end QuantitativeArithmeticInverseMellinBound
