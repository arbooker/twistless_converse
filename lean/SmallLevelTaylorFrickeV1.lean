module

public import SmallLevelTaylorRemainderV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace SmallLevelTaylor

open Complex Filter Asymptotics Set FinitenessFourierConstruction FinitenessPolynomialSeries
open scoped Topology

theorem fricke_deformation_point {L r y : ℝ} (hL : 0<L) (hr : r≠0) (hy : 0<y) :
    deformPoint (-1/(L*r)) (L*r^2) y (((y/r:ℝ):ℂ)*I)=
      -1/((L:ℂ)*((r:ℂ)+(y:ℂ)*I)) := by
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
  have hLC : (L:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hz : (r:ℂ)+(y:ℂ)*I≠0 := by
    intro he
    have := congrArg Complex.im he
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,
      Complex.zero_im,zero_add] at this
    exact hy.ne' this
  have hu : (1:ℂ)+((y/r:ℝ):ℂ)*I≠0 := by
    intro he
    have := congrArg Complex.re he
    norm_num at this
  unfold deformPoint
  push_cast
  push_cast at hu
  field_simp [hrC,hLC,hu,hz]
  ring

/-- Exact Fricke inversion expressed in the deformation variable used for
the uniform Cauchy estimate. This identity uses no Taylor approximation. -/
theorem fricke_deformed {L r y : ℝ} (hL : 0<L) (hr : r≠0) (hy : 0<y)
    (k : ℕ) (a : ℕ → ℂ) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier a (-1/((L:ℂ)*z))) :
    fourier a ((r:ℂ)+(y:ℂ)*I)=
      (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*
        deformed k a (-1/(L*r)) (L*r^2) y (((y/r:ℝ):ℂ)*I) := by
  rw [hF _ (by simpa using hy),deformed,fricke_deformation_point hL hr hy]
  have hfactor : (Real.sqrt L:ℂ)*((r:ℂ)+(y:ℂ)*I)=
      ((Real.sqrt L:ℂ)*(r:ℂ))*(1+((y/r:ℝ):ℂ)*I) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hr]
  rw [hfactor,mul_pow]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

def frickeTaylorPolynomial (k : ℕ) (a : ℕ → ℂ) (L r : ℝ) (M : ℕ) (y : ℝ) : ℂ :=
  (cauchyPowerSeries (deformed k a (-1/(L*r)) (L*r^2) y) 0 (1/2)).partialSum M
    (((y/r:ℝ):ℂ)*I)

theorem fricke_taylor_error {L r y : ℝ} (hL : 0<L) (hr : r≠0) (hy : 0<y)
    (k : ℕ) (a : ℕ → ℂ) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier a (-1/((L:ℂ)*z))) (M : ℕ) :
    fourier a ((r:ℂ)+(y:ℂ)*I)-
      (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*frickeTaylorPolynomial k a L r M y=
      (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*taylorRemainder k a (-1/(L*r)) (L*r^2) r M y := by
  rw [fricke_deformed hL hr hy k a χ hF]
  simp only [frickeTaylorPolynomial,taylorRemainder,mul_sub]

/-- The actual Fricke transformation has a Taylor remainder of order
y^(M-K) for every M, with K independent of M. The Mellin transform of the
Taylor coefficients is a separate integration-by-parts step. -/
theorem fricke_taylor_small {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier a (-1/((L:ℂ)*z))) :
    ∃ K : ℕ, ∀ M : ℕ,
      (fun y : ℝ => fourier a ((r:ℂ)+(y:ℂ)*I)-
        (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*frickeTaylorPolynomial k a L r M y)
        =O[𝓝[>] 0] (fun y : ℝ => y^((M:ℝ)-(K:ℝ))) := by
  obtain ⟨K,hK⟩ := taylorRemainder_small ha ha0 k (mul_pos hL (sq_pos_of_ne_zero hr))
  refine ⟨K,fun M => ?_⟩
  have h := (hK (-1/(L*r)) r hr M).const_mul_left (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (fricke_taylor_error hL hr hy k a χ hF M).symm

/-- Original Euler input supplies the Fricke law, growth bound, and hence
the movable small-height Taylor error, without extra analytic assumptions. -/
theorem original_fricke_taylor_small {N k : ℕ} (hN : 0<N) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) :
    ∃ χ : ℂ, ‖χ‖=1 ∧ ∀ r : ℝ, r≠0 → ∃ K : ℕ, ∀ M : ℕ,
      (fun y : ℝ => fourier (FinitenessOriginalFourier.fullCoefficients f k) ((r:ℂ)+(y:ℂ)*I)-
        (χ/(((Real.sqrt (N:ℝ):ℂ)*(r:ℂ))^k))*
          frickeTaylorPolynomial k (FinitenessOriginalFourier.fullCoefficients f k) N r M y)
        =O[𝓝[>] 0] (fun y : ℝ => y^((M:ℝ)-(K:ℝ))) := by
  obtain ⟨χ,hχ,hF⟩ := FinitenessOriginalFricke.solution_fricke hN hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  refine ⟨χ,hχ,fun r hr => ?_⟩
  apply fricke_taylor_small (by exact_mod_cast hN) hr k
    (FinitenessOriginalFourier.polynomial_bound hf.zero hg k)
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero k) χ
  simpa only [Complex.ofReal_natCast] using hF

#print axioms fricke_deformation_point
#print axioms fricke_deformed
#print axioms fricke_taylor_error
#print axioms fricke_taylor_small
#print axioms original_fricke_taylor_small

end SmallLevelTaylor
