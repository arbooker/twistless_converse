module

public import SmallLevelTaylorRemainderV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor

open Complex Filter Asymptotics Set FinitenessPolynomialSeries FinitenessFourierConstruction

theorem deformed_family_exponential (k : ℕ) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) {c : ℝ} (hc : 0<c) :
    ∃ D : ℝ, 0≤D ∧ ∀ β y : ℝ, 8*c≤y → ∀ u : ℂ, ‖u‖≤1/2 →
      ‖deformed k a β c y u‖≤D*Real.exp (-(2*Real.pi/(8*c))*y) := by
  obtain ⟨C,hC,hbound⟩ := FinitenessAllLevelAxisDecay.fourier_exponential ha ha0 (by norm_num : (0:ℝ)<1)
  refine ⟨2^k*C,by positivity,?_⟩
  intro β y hy u hu
  have hypos : 0<y := lt_of_lt_of_le (by positivity) hy
  have hheight := deformPoint_height β hc hypos hu
  have hheight1 : 1≤(deformPoint β c y u).im := by
    have h : 1≤y/(8*c) := (le_div_iff₀ (by positivity)).mpr (by simpa using hy)
    exact h.trans hheight
  have hpref : ‖((1+u)^k)⁻¹‖≤(2:ℝ)^k := by
    rw [← inv_pow,norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (one_add_inv_norm_le hu) k
  calc
    ‖deformed k a β c y u‖=‖((1+u)^k)⁻¹‖*‖fourier a (deformPoint β c y u)‖ := norm_mul _ _
    _≤2^k*(C*Real.exp (-2*Real.pi*(deformPoint β c y u).im)) :=
      mul_le_mul hpref (hbound _ hheight1) (norm_nonneg _) (by positivity)
    _≤2^k*(C*Real.exp (-2*Real.pi*(y/(8*c)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    _=(2^k*C)*Real.exp (-(2*Real.pi/(8*c))*y) := by
      have he : -2*Real.pi*(y/(8*c))=-(2*Real.pi/(8*c))*y := by ring
      rw [he]
      ring

theorem cauchy_term_rapid (k : ℕ) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) (β r : ℝ) {c : ℝ} (hc : 0<c)
    (n : ℕ) (s : ℝ) :
    (fun y : ℝ => cauchyPowerSeries (deformed k a β c y) 0 (1/2) n
      (fun _ => ((y/r:ℝ):ℂ)*I))=O[atTop] (fun y : ℝ => y^s) := by
  obtain ⟨D,hD,hbound⟩ := deformed_family_exponential k ha ha0 hc
  let κ : ℝ := 2*Real.pi/(8*c)
  have hκ : 0<κ := by dsimp [κ]; positivity
  have hterm : (fun y : ℝ => cauchyPowerSeries (deformed k a β c y) 0 (1/2) n
      (fun _ => ((y/r:ℝ):ℂ)*I))=O[atTop] (fun y : ℝ => Real.exp (-κ*y)*y^n) := by
    apply IsBigO.of_bound (D*(2/|r|)^n)
    filter_upwards [eventually_ge_atTop (8*c)] with y hy
    have hypos : 0<y := lt_of_lt_of_le (by positivity) hy
    have hp := cauchy_coefficient_bound (hbound β y hy) n
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤Real.exp (-κ*y)*y^n)]
    calc
      _≤‖cauchyPowerSeries (deformed k a β c y) 0 (1/2) n‖*
          ‖((y/r:ℝ):ℂ)*I‖^n := by
        simpa only [Finset.prod_const,Finset.card_fin] using
          (cauchyPowerSeries (deformed k a β c y) 0 (1/2) n).le_opNorm (fun _ => ((y/r:ℝ):ℂ)*I)
      _≤(D*Real.exp (-κ*y)*2^n)*(y/|r|)^n := by
        rw [deformation_parameter_norm hypos.le]
        exact mul_le_mul_of_nonneg_right hp (by positivity)
      _=(D*(2/|r|)^n)*(Real.exp (-κ*y)*y^n) := by
        simp only [div_pow]
        ring
  have hexp : (fun y : ℝ => Real.exp (-κ*y)*y^n)=O[atTop]
      (fun y : ℝ => Real.exp ((-κ/2)*y)) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_exp_mul_rpow_of_lt (n:ℝ) (a := -κ) (b := -κ/2) (by linarith)).isBigO
  have hrapid : (fun y : ℝ => Real.exp ((-κ/2)*y))=O[atTop] (fun y : ℝ => y^s) := by
    simpa only [neg_div] using (isLittleO_exp_neg_mul_rpow_atTop (show 0<κ/2 by positivity) s).isBigO
  exact hterm.trans (hexp.trans hrapid)

#print axioms deformed_family_exponential
#print axioms cauchy_term_rapid

end SmallLevelTaylor
