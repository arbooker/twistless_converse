module

public import QuantitativeArithmeticMaassMajorantAbelBoundsV1
public import QuantitativeMaassCompactTailScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The upper-height remainder in the original compact excess bound
vanishes for the literal normalized majorant. -/
theorem originalMajorant_compact_tail_limit
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (ν : ℕ) (C : ℝ) (hC : 1≤C)
    (T : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0)) :
    Tendsto (fun t =>
      let R := C*radius ε t
      let J := ⌈(ν:ℝ)*R+1⌉₊
      let H := Real.exp (Strong.strongScale t/2-R)
      let f := QuantitativeNinaMaass.originalWindowMajorant K hc ε t
      ‖T‖*(((((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2)*
        (H⁻¹*|(abelProfile (evenCoshLift (timeConvolution f f)) 1).re|))/(t*ε t))
      atTop (𝓝 0) := by
  obtain ⟨B,hB,hdiag⟩ := originalMajorantSquare_abel_diagonal_bound K he hc hK hm
  have hlim := (inverse_band_half_height_tail_cost ε hε hp ν C hC).const_mul (‖T‖*B)
  rw [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    have he0 := heps.1.le
    positivity
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ),hdiag ε hε hp] with t heps ht hdiag
    let J := ⌈(ν:ℝ)*(C*radius ε t)+1⌉₊
    let H := Real.exp (Strong.strongScale t/2-C*radius ε t)
    let f := QuantitativeNinaMaass.originalWindowMajorant K hc ε t
    have hv : |(abelProfile (evenCoshLift (timeConvolution f f)) 1).re|≤B*t*ε t :=
      (Complex.abs_re_le_norm _).trans hdiag
    change ‖T‖*(((((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2)*
      (H⁻¹*|(abelProfile (evenCoshLift (timeConvolution f f)) 1).re|))/(t*ε t)≤_
    calc
      _≤‖T‖*(((((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2)*(H⁻¹*(B*t*ε t)))/(t*ε t) := by
        apply div_le_div_of_nonneg_right _ (mul_pos ht heps.1).le
        gcongr
      _=_ := by
        dsimp only [J,H]
        field_simp [ht.ne',heps.1.ne']

#print axioms originalMajorant_compact_tail_limit
end QuantitativeMaass.Scheduled
