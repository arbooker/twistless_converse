module
public import FinitenessAllLevelAxisDecayV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTranslatedRay
open Complex Filter Asymptotics FinitenessPolynomialSeries FinitenessFourierConstruction
open scoped Topology

/-- Every fixed polynomial multiple of a translated Fourier ray decays
faster than every power at infinity. -/
theorem weighted_rapid {a : ℕ→ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (k : ℕ) (r s : ℝ) :
    (fun y : ℝ => (y:ℂ)^k*fourier a ((r:ℂ)+(y:ℂ)*Complex.I))=O[atTop]
      (fun y : ℝ => y^s) := by
  obtain ⟨C,_,hb⟩:=FinitenessAllLevelAxisDecay.fourier_exponential ha ha0 (by norm_num : (0:ℝ)<1)
  have hbound : (fun y : ℝ => (y:ℂ)^k*fourier a ((r:ℂ)+(y:ℂ)*Complex.I))=O[atTop]
      (fun y : ℝ => Real.exp (-2*Real.pi*y)*y^k) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    have hy0 : 0≤y:=by linarith
    have hh:=hb ((r:ℂ)+(y:ℂ)*Complex.I) (by simpa using hy)
    have hz : ((r:ℂ)+(y:ℂ)*Complex.I).im=y := by simp
    rw [hz] at hh
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hy0,
      Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤Real.exp (-2*Real.pi*y)*y^k)]
    calc
      y^k*‖fourier a ((r:ℂ)+(y:ℂ)*Complex.I)‖ ≤ y^k*(C*Real.exp (-2*Real.pi*y)) :=
        mul_le_mul_of_nonneg_left hh (pow_nonneg hy0 _)
      _ = _ := by ring
  have he : (fun y : ℝ => Real.exp (-2*Real.pi*y)*y^k)=O[atTop]
      (fun y : ℝ => Real.exp (-Real.pi*y)) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_exp_mul_rpow_of_lt (k:ℝ) (a := -2*Real.pi) (b := -Real.pi)
        (by nlinarith [Real.pi_pos])).isBigO
  exact hbound.trans (he.trans (isLittleO_exp_neg_mul_rpow_atTop Real.pi_pos s).isBigO)

/-- Exact inversion of a rapidly decreasing ray produces a first-order
remainder at the zero endpoint. -/
theorem inverted_weighted_first_order {a : ℕ→ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (k : ℕ) (r : ℝ) {c : ℝ} (hc : 0<c) :
    (fun t : ℝ => ((1/(c*t):ℝ):ℂ)^k*
      fourier a ((r:ℂ)+((1/(c*t):ℝ):ℂ)*Complex.I))=O[𝓝[>] 0]
      (fun t : ℝ => t^(1:ℝ)) := by
  have ht : Tendsto (fun t : ℝ => 1/(c*t)) (𝓝[>] 0) atTop := by
    have hh:=(tendsto_inv_nhdsGT_zero : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop)
    convert hh.const_mul_atTop (one_div_pos.mpr hc) using 1
    funext t
    field_simp
  have hh:=(weighted_rapid ha ha0 k r (-1)).comp_tendsto ht
  dsimp only [Function.comp_def] at hh
  have he : (fun t : ℝ => (1/(c*t))^(-1:ℝ))=ᶠ[𝓝[>] 0] (fun t : ℝ => c*t) := by
    filter_upwards [] with t
    simp [Real.rpow_neg_one]
  have hb : (fun t : ℝ => c*t)=O[𝓝[>] 0] (fun t : ℝ => t^(1:ℝ)) := by
    simpa only [Real.rpow_one] using (isBigO_refl (fun t : ℝ => t) (𝓝[>] 0)).const_mul_left c
  exact (hh.congr' Filter.EventuallyEq.rfl he).trans hb

#print axioms weighted_rapid
#print axioms inverted_weighted_first_order
end SmallLevelTranslatedRay
