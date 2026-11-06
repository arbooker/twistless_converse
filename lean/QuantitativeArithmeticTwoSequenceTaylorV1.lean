module

public import SmallLevelTaylorMellinRowsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTwoSequenceTaylor
open SmallLevelTaylor Complex Filter Asymptotics Set MeasureTheory FinitenessFourierConstruction FinitenessPolynomialSeries
open scoped Topology

theorem two_deformed {L r y : ℝ} (hL : 0<L) (hr : r≠0) (hy : 0<y)
    (k : ℕ) (a b : ℕ → ℂ) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier b (-1/((L:ℂ)*z))) :
    fourier a ((r:ℂ)+(y:ℂ)*I)=
      (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*
        deformed k b (-1/(L*r)) (L*r^2) y (((y/r:ℝ):ℂ)*I) := by
  rw [hF _ (by simpa using hy),deformed,fricke_deformation_point hL hr hy]
  have hfactor : (Real.sqrt L:ℂ)*((r:ℂ)+(y:ℂ)*I)=
      ((Real.sqrt L:ℂ)*(r:ℂ))*(1+((y/r:ℝ):ℂ)*I) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hr]
  rw [hfactor,mul_pow]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring
theorem two_error_point {L r y : ℝ} (hL : 0<L) (hr : r≠0) (hy : 0<y)
    (k : ℕ) (a b : ℕ → ℂ) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier b (-1/((L:ℂ)*z))) (M : ℕ) :
    fourier a ((r:ℂ)+(y:ℂ)*I)-
      (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*frickeTaylorPolynomial k b L r M y=
      (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*taylorRemainder k b (-1/(L*r)) (L*r^2) r M y := by
  rw [two_deformed hL hr hy k a b χ hF]
  simp only [frickeTaylorPolynomial,taylorRemainder,mul_sub]

theorem two_error_small {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (k : ℕ) (a : ℕ → ℂ) {b : ℕ → ℂ} (hb : PolynomialBound b) (hb0 : b 0=0) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier b (-1/((L:ℂ)*z))) :
    ∃ K : ℕ, ∀ M : ℕ,
      (fun y : ℝ => fourier a ((r:ℂ)+(y:ℂ)*I)-
        (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*frickeTaylorPolynomial k b L r M y)
        =O[𝓝[>] 0] (fun y : ℝ => y^((M:ℝ)-(K:ℝ))) := by
  obtain ⟨K,hK⟩ := taylorRemainder_small hb hb0 k (mul_pos hL (sq_pos_of_ne_zero hr))
  refine ⟨K,fun M => ?_⟩
  have h := (hK (-1/(L*r)) r hr M).const_mul_left (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (two_error_point hL hr hy k a b χ hF M).symm


def twoError (k : ℕ) (a b : ℕ → ℂ) (L r : ℝ) (χ : ℂ) (M : ℕ) (y : ℝ) : ℂ :=
  fourier a ((r:ℂ)+(y:ℂ)*I)-
    (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*frickeTaylorPolynomial k b L r M y

theorem two_error_local (k : ℕ) {a b : ℕ → ℂ}
    (ha : PolynomialBound a) (hb : PolynomialBound b)
    {L r : ℝ} (hL : 0<L) (hr : r≠0) (χ : ℂ) (M : ℕ) :
    LocallyIntegrableOn (twoError k a b L r χ M) (Ioi 0) := by
  have hf : ContinuousOn (fun y : ℝ => fourier a ((r:ℂ)+(y:ℂ)*I)) (Ioi 0) := by
    intro y hy
    exact ((FinitenessFourierConstruction.holomorphic ha (by simpa using hy)).continuousAt.comp
      (by fun_prop)).continuousWithinAt
  exact (hf.sub ((frickeTaylorPolynomial_continuous k hb hL hr M).const_mul _)).locallyIntegrableOn measurableSet_Ioi

theorem two_error_rapid (k : ℕ) {a b : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) (hb : PolynomialBound b) (hb0 : b 0=0)
    {L r : ℝ} (hL : 0<L) (hr : r≠0) (χ : ℂ) (M : ℕ) (s : ℝ) :
    twoError k a b L r χ M=O[atTop] (fun y : ℝ => y^s) :=
  (fourier_ray_rapid ha ha0 r s).sub
    ((frickeTaylorPolynomial_rapid k hb hb0 hL hr M s).const_mul_left _)

/-- Full movable-half-plane remainder for a Fricke relation between two
possibly distinct Fourier series. No additive continuation is assumed. -/
theorem two_error_analytic {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (k : ℕ) {a b : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) (hb : PolynomialBound b) (hb0 : b 0=0) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier b (-1/((L:ℂ)*z))) :
    ∃ K : ℕ, ∀ M : ℕ, AnalyticOnNhd ℂ (mellin (twoError k a b L r χ M))
      {s : ℂ | (K:ℝ)-(M:ℝ)<s.re} := by
  obtain ⟨K,hK⟩ := two_error_small hL hr k a hb hb0 χ hF
  refine ⟨K,fun M => ?_⟩
  have hzero : twoError k a b L r χ M=O[𝓝[>] 0]
      (fun y : ℝ => y^(-((K:ℝ)-(M:ℝ)))) := by
    rw [show -((K:ℝ)-(M:ℝ))=(M:ℝ)-(K:ℝ) by ring]
    exact hK M
  have hd : DifferentiableOn ℂ (mellin (twoError k a b L r χ M))
      {s : ℂ | (K:ℝ)-(M:ℝ)<s.re} := by
    intro s hs
    exact (mellin_differentiableAt_of_isBigO_rpow
      (two_error_local k ha hb hL hr χ M)
      (two_error_rapid k ha ha0 hb hb0 hL hr χ M (-(s.re+1)))
      (lt_add_one s.re) hzero hs).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

#print axioms two_deformed
#print axioms two_error_point
#print axioms two_error_small
#print axioms two_error_analytic
end QuantitativeArithmeticTwoSequenceTaylor
