module
public import QuantitativeArithmeticSimplePoleVerticalV1
public import QuantitativeArithmeticSimplePoleHorizontalV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSimplePoleContour
open Complex MeasureTheory Filter
open QuantitativeArithmeticSimplePoleVertical QuantitativeArithmeticSimplePoleHorizontal
open QuantitativeArithmeticSymmetricContour
open scoped Topology

theorem vertical_regular_part_limit (F E : ℂ → ℂ) (r : ℂ) (k σ : ℝ)
    (hσ : σ≠k) (hF : VerticalIntegrable F σ)
    (he : ∀ z : ℂ,z≠(k:ℂ) → E z=F z-r/(z-(k:ℂ))) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T,E ((σ:ℂ)+(t:ℂ)*I)) atTop
      (𝓝 ((∫ t : ℝ,F ((σ:ℂ)+(t:ℂ)*I))-
        r*((((σ-k)⁻¹*(Real.pi/|(σ-k)⁻¹|)):ℝ):ℂ))) := by
  have hz (t : ℝ) : (σ:ℂ)+(t:ℂ)*I≠(k:ℂ) := by
    intro hh
    apply hσ
    simpa using congrArg Complex.re hh
  have hr (t : ℝ) : E ((σ:ℂ)+(t:ℂ)*I)=F ((σ:ℂ)+(t:ℂ)*I)-
      r*(((σ-k:ℝ):ℂ)+(t:ℂ)*I)⁻¹ := by
    rw [he _ (hz t),div_eq_mul_inv]
    congr 2
    push_cast
    ring
  have hi := intervalIntegral_tendsto_integral hF tendsto_neg_atTop_atBot tendsto_id
  have hp := (symmetric_inverse_limit (σ-k) (sub_ne_zero.mpr hσ)).const_mul r
  have hcont := (inverse_continuous (σ-k) (sub_ne_zero.mpr hσ)).const_mul r
  have hh := hi.sub hp
  have hei (T : ℝ) : (∫ t : ℝ in -T..T,E ((σ:ℂ)+(t:ℂ)*I))=
      (∫ t : ℝ in -T..T,F ((σ:ℂ)+(t:ℂ)*I))-
        r*(∫ t : ℝ in -T..T,(((σ-k:ℝ):ℂ)+(t:ℂ)*I)⁻¹) := by
    simp_rw [hr]
    rw [intervalIntegral.integral_sub hF.intervalIntegrable
      (hcont.intervalIntegrable (μ:=volume) (-T) T),intervalIntegral.integral_const_mul]
  simpa only [hei,id_eq] using hh

theorem pole_value_positive (a : ℝ) (ha : 0<a) : a⁻¹*(Real.pi/|a⁻¹|)=Real.pi := by
  rw [abs_of_pos (inv_pos.mpr ha)]
  field_simp [ne_of_gt ha]

theorem pole_value_negative (a : ℝ) (ha : a<0) : a⁻¹*(Real.pi/|a⁻¹|)= -Real.pi := by
  rw [abs_of_neg (inv_lt_zero'.mpr ha)]
  field_simp [ne_of_lt ha]

/-- The single-pole contour shift, obtained using symmetric integrals of
the subtracted principal part. It requires no global finite-order bound. -/
theorem vertical_difference (F E : ℂ → ℂ) (r : ℂ) (k a b C : ℝ)
    (ha : a<k) (hb : k<b) (hE : Differentiable ℂ E)
    (he : ∀ z : ℂ,z≠(k:ℂ) → E z=F z-r/(z-(k:ℂ)))
    (hF : ∀ z : ℂ,a≤z.re → z.re≤b → 1≤|z.im| → ‖F z‖≤C/(1+z.im^2))
    (hia : VerticalIntegrable F a) (hib : VerticalIntegrable F b) :
    (∫ t : ℝ,F ((b:ℂ)+(t:ℂ)*I))=
      (∫ t : ℝ,F ((a:ℂ)+(t:ℂ)*I))+2*(Real.pi:ℂ)*r := by
  have hla := vertical_regular_part_limit F E r k a (ne_of_lt ha) hia he
  have hlb := vertical_regular_part_limit F E r k b (ne_of_gt hb) hib he
  rw [pole_value_negative (a-k) (sub_neg.mpr ha),Complex.ofReal_neg] at hla
  rw [pole_value_positive (b-k) (sub_pos.mpr hb)] at hlb
  obtain ⟨hu,hd⟩ := regular_part_horizontal_zero F E r k a b C (ha.trans hb).le he hF
  have hh := equal_limits hE a b _ _ hla hlb hu hd
  linear_combination -hh
#print axioms vertical_difference
end QuantitativeArithmeticSimplePoleContour
