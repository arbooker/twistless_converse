module

public import SmallLevelTaylorContinuityV1
public import SmallLevelTaylorDecayV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor

open Complex Filter Asymptotics Set MeasureTheory FinitenessPolynomialSeries FinitenessFourierConstruction
open scoped Topology

def frickeError (k : ℕ) (a : ℕ → ℂ) (L r : ℝ) (χ : ℂ) (M : ℕ) (y : ℝ) : ℂ :=
  fourier a ((r:ℂ)+(y:ℂ)*I)-
    (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*frickeTaylorPolynomial k a L r M y

theorem frickeTaylorPolynomial_rapid (k : ℕ) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (M : ℕ) (s : ℝ) : frickeTaylorPolynomial k a L r M=O[atTop] (fun y : ℝ => y^s) := by
  unfold frickeTaylorPolynomial FormalMultilinearSeries.partialSum
  apply IsBigO.fun_sum
  intro n _
  exact cauchy_term_rapid k ha ha0 (-1/(L*r)) r (mul_pos hL (sq_pos_of_ne_zero hr)) n s

theorem fourier_ray_rapid {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0) (r s : ℝ) :
    (fun y : ℝ => fourier a ((r:ℂ)+(y:ℂ)*I))=O[atTop] (fun y : ℝ => y^s) := by
  have h := FinitenessAllLevelAxisDecay.axis_rapid (N := 1) (by decide)
    (SmallLevelAdditive.coefficients_polynomial ha r) (SmallLevelAdditive.coefficients_zero ha0 r) s
  rw [show FinitenessAllLevelAxisDecay.axis 1 (SmallLevelAdditive.coefficients a r)=
    (fun y : ℝ => fourier a ((r:ℂ)+(y:ℂ)*I)) from
      funext (SmallLevelAdditive.axis_one_translate a r)] at h
  exact h

theorem frickeError_rapid (k : ℕ) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (χ : ℂ) (M : ℕ) (s : ℝ) : frickeError k a L r χ M=O[atTop] (fun y : ℝ => y^s) :=
  (fourier_ray_rapid ha ha0 r s).sub
    ((frickeTaylorPolynomial_rapid k ha ha0 hL hr M s).const_mul_left _)

/-- The Cauchy Taylor remainder of the actual Fricke transformation has a
Mellin transform analytic on a movable half-plane. All local integrability
and both endpoint estimates are proved; no cutoff or regularity is assumed.
Identifying the Taylor coefficient Mellin integrals with the shifted
additive transforms and their binomial factors remains a separate step. -/
theorem frickeError_mellin_analytic {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier a (-1/((L:ℂ)*z))) :
    ∃ K : ℕ, ∀ M : ℕ, AnalyticOnNhd ℂ (mellin (frickeError k a L r χ M))
      {s : ℂ | (K:ℝ)-(M:ℝ)<s.re} := by
  obtain ⟨K,hK⟩ := fricke_taylor_small hL hr k ha ha0 χ hF
  refine ⟨K,fun M => ?_⟩
  have hzero : frickeError k a L r χ M=O[𝓝[>] 0]
      (fun y : ℝ => y^(-((K:ℝ)-(M:ℝ)))) := by
    rw [show -((K:ℝ)-(M:ℝ))=(M:ℝ)-(K:ℝ) by ring]
    exact hK M
  have hd : DifferentiableOn ℂ (mellin (frickeError k a L r χ M))
      {s : ℂ | (K:ℝ)-(M:ℝ)<s.re} := by
    intro s hs
    exact (mellin_differentiableAt_of_isBigO_rpow
      (fricke_error_locallyIntegrable k ha hL hr χ M)
      (frickeError_rapid k ha ha0 hL hr χ M (-(s.re+1)))
      (lt_add_one s.re) hzero hs).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

theorem original_frickeError_mellin_analytic {N k : ℕ} (hN : 0<N) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) :
    ∃ χ : ℂ, ‖χ‖=1 ∧ ∀ r : ℝ, r≠0 → ∃ K : ℕ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (frickeError k (FinitenessOriginalFourier.fullCoefficients f k) N r χ M))
        {s : ℂ | (K:ℝ)-(M:ℝ)<s.re} := by
  obtain ⟨χ,hχ,hF⟩ := FinitenessOriginalFricke.solution_fricke hN hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  refine ⟨χ,hχ,fun r hr => ?_⟩
  apply frickeError_mellin_analytic (by exact_mod_cast hN) hr k
    (FinitenessOriginalFourier.polynomial_bound hf.zero hg k)
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero k) χ
  simpa only [Complex.ofReal_natCast] using hF

#print axioms frickeTaylorPolynomial_rapid
#print axioms fourier_ray_rapid
#print axioms frickeError_rapid
#print axioms frickeError_mellin_analytic
#print axioms original_frickeError_mellin_analytic

end SmallLevelTaylor
