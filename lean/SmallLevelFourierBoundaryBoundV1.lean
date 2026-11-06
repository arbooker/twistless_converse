module

public import SmallLevelAdditiveMellinV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor

open Complex Filter Asymptotics Set FinitenessPolynomialSeries FinitenessFourierConstruction

theorem pow_mul_exp_neg_le (K : ℕ) {t : ℝ} (ht : 0≤t) :
    t^K*Real.exp (-t)≤(K.factorial:ℝ) := by
  have hf : (0:ℝ)<K.factorial := by exact_mod_cast Nat.factorial_pos K
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp t ht K)
  calc
    t^K*Real.exp (-t)≤(Real.exp t*(K.factorial:ℝ))*Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _=(K.factorial:ℝ) := by
      rw [mul_right_comm,← Real.exp_add]
      simp

theorem exp_neg_le_factorial_div_pow (K : ℕ) {t : ℝ} (ht : 0<t) :
    Real.exp (-t)≤(K.factorial:ℝ)/t^K := by
  apply (le_div_iff₀ (pow_pos ht K)).mpr
  simpa only [mul_comm] using pow_mul_exp_neg_le K ht.le

/-- A Dirichlet absolute-convergence bound controls the Fourier series
uniformly in its real part, all the way down to the real boundary. -/
theorem fourier_norm_le {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (K : ℕ) (hs : Summable (fun n : ℕ => ‖a (n+1)‖/((n+1:ℕ):ℝ)^K))
    {z : ℂ} (hz : 0<z.im) :
    ‖fourier a z‖≤((K.factorial:ℝ)/(2*Real.pi)^K*
      (∑' n : ℕ, ‖a (n+1)‖/((n+1:ℕ):ℝ)^K))/z.im^K := by
  let D : ℝ := (K.factorial:ℝ)/(2*Real.pi)^K/z.im^K
  have hseries := FinitenessOriginalFourier.exp_summable ha hz
  have hnorm (n : ℕ) :
      ‖a (n+1)*Complex.exp (2*Real.pi*I*((n+1:ℕ):ℂ)*z)‖≤
        D*(‖a (n+1)‖/((n+1:ℕ):ℝ)^K) := by
    rw [norm_mul,Complex.norm_exp]
    have he : (2*(Real.pi:ℂ)*I*((n+1:ℕ):ℂ)*z).re=
        -(2*Real.pi*((n+1:ℕ):ℝ)*z.im) := by
      simp [Complex.mul_re,Complex.mul_im]
    rw [he]
    have ht : 0<2*Real.pi*((n+1:ℕ):ℝ)*z.im := by positivity
    calc
      _≤‖a (n+1)‖*((K.factorial:ℝ)/(2*Real.pi*((n+1:ℕ):ℝ)*z.im)^K) :=
        mul_le_mul_of_nonneg_left (exp_neg_le_factorial_div_pow K ht) (norm_nonneg _)
      _=D*(‖a (n+1)‖/((n+1:ℕ):ℝ)^K) := by
        simp only [D,mul_pow,div_eq_mul_inv,mul_inv_rev]
        ring
  have hn := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnorm (hs.mul_left D)
  rw [fourier_eq_exp,hseries.tsum_eq_zero_add,ha0,zero_mul,zero_add]
  calc
    _≤∑' n : ℕ, ‖a (n+1)*Complex.exp (2*Real.pi*I*((n+1:ℕ):ℂ)*z)‖ :=
      norm_tsum_le_tsum_norm hn
    _≤∑' n : ℕ, D*(‖a (n+1)‖/((n+1:ℕ):ℝ)^K) := hn.tsum_le_tsum hnorm (hs.mul_left D)
    _=_ := by rw [tsum_mul_left]; dsimp [D]; ring

/-- Polynomial Fourier coefficients give one uniform power bound on the
entire upper half-plane. The exponent and constant are individual to a. -/
theorem fourier_boundary_bound {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0) :
    ∃ K : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ z : ℂ, 0<z.im → ‖fourier a z‖≤C/z.im^K := by
  obtain ⟨d,hd⟩ := FinitenessAllLevelMellinDirichlet.polynomial_growth ha
  have hs : Summable (fun n : ℕ => ‖a (n+1)‖/((n+1:ℕ):ℝ)^(d+2)) := by
    have h := FinitenessAllLevelMellinDirichlet.summable_norm_div hd
      (u := ((d+2:ℕ):ℝ)) (by push_cast; linarith)
    simpa only [Real.rpow_natCast] using h
  refine ⟨d+2,((d+2).factorial:ℝ)/(2*Real.pi)^(d+2)*
    (∑' n : ℕ, ‖a (n+1)‖/((n+1:ℕ):ℝ)^(d+2)),?_,fun z hz => fourier_norm_le ha ha0 _ hs hz⟩
  exact mul_nonneg (by positivity) (tsum_nonneg (fun n => by positivity))

#print axioms pow_mul_exp_neg_le
#print axioms fourier_norm_le
#print axioms fourier_boundary_bound

end SmallLevelTaylor
