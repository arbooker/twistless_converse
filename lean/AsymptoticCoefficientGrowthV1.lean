module

public import FinitenessFourierConstructionV1
public import FinitenessCuspBoundsV1
public import FinitenessEnvelopeAssemblyV1
public import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCoefficientGrowth

open Metric Set Complex FinitenessPolynomialSeries
open scoped NNReal

/-- Cauchy's estimate for the coefficients of the original disk series. -/
theorem coefficient_le_circle_bound {a : ℕ → ℂ} (ha : PolynomialBound a)
    {R M : ℝ} (hR : 0<R) (hR1 : R<1)
    (hbound : ∀ w : ℂ, ‖w‖=R → ‖sum a w‖≤M) (n : ℕ) :
    ‖a n‖≤M*R⁻¹^n := by
  let r : ℝ≥0 := ⟨R,hR.le⟩
  have hd : DifferentiableOn ℂ (sum a) (closedBall 0 (r:ℝ)) :=
    (holomorphic ha).mono (closedBall_subset_ball hR1)
  have he := (has_series ha).eq_formalMultilinearSeries
    (hd.hasFPowerSeriesOnBall (show 0<r from hR)).hasFPowerSeriesAt
  change FormalMultilinearSeries.ofScalars ℂ a=cauchyPowerSeries (sum a) 0 R at he
  have hn : ‖a n‖=‖cauchyPowerSeries (sum a) 0 R n‖ := by
    have hh := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => ‖p n‖) he
    simpa only [FormalMultilinearSeries.ofScalars_norm] using hh
  rw [hn]
  apply (norm_cauchyPowerSeries_le _ _ _ _).trans
  rw [abs_of_pos hR]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hc : Continuous (fun θ : ℝ => sum a (circleMap 0 R θ)) :=
    ((holomorphic ha).continuousOn.mono (sphere_subset_ball hR1)).comp_continuous
      (continuous_circleMap 0 R) (circleMap_mem_sphere 0 hR.le)
  have hi := intervalIntegral.integral_mono (f:=fun θ : ℝ => ‖sum a (circleMap 0 R θ)‖)
    (g:=fun _ : ℝ => M) (μ:=MeasureTheory.volume) (by positivity : (0:ℝ)≤2*Real.pi)
    (hc.norm.intervalIntegrable _ _) intervalIntegrable_const
    (fun θ => hbound _ (by simp [norm_circleMap_zero,abs_of_pos hR]))
  have hi' : (∫ θ : ℝ in 0..2*Real.pi, ‖sum a (circleMap 0 R θ)‖)≤2*Real.pi*M := by
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] using hi
  calc
    (2*Real.pi)⁻¹*(∫ θ : ℝ in 0..2*Real.pi, ‖sum a (circleMap 0 R θ)‖)
        ≤(2*Real.pi)⁻¹*(2*Real.pi*M) := mul_le_mul_of_nonneg_left hi' (by positivity)
    _ = M := inv_mul_cancel_left₀ (by positivity) M

/-- A global height bound forces a polynomial coefficient bound of exactly
the same degree. The original individual growth exponent is eliminated. -/
theorem coefficient_le_height_bound {a : ℕ → ℂ} (ha : PolynomialBound a)
    (b : ℕ) {M : ℝ}
    (hM : ∀ z : ℂ, 0<z.im → z.im^b*‖FinitenessFourierConstruction.fourier a z‖≤M)
    (n : ℕ) (hn : 0<n) : ‖a n‖≤(M*Real.exp (2*Real.pi))*(n:ℝ)^b := by
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn
  have hη : 0<(n:ℝ)⁻¹ := inv_pos.mpr hn'
  have hc (w : ℂ) (hw : ‖w‖=Real.exp (-2*Real.pi*(n:ℝ)⁻¹)) :=
    FinitenessCuspBounds.circle_bound
      (FinitenessFourierConstruction.fourier a) (sum a) (fun _ _ => rfl) b hη hM hw
  have he := coefficient_le_circle_bound ha (Real.exp_pos _)
    (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos] : -2*Real.pi*(n:ℝ)⁻¹<0))
    hc n
  have hexp : (Real.exp (-2*Real.pi*(n:ℝ)⁻¹))⁻¹^n=Real.exp (2*Real.pi) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    field_simp
  simpa only [hexp,inv_pow,div_inv_eq_mul,mul_right_comm] using he

/-- Direct-height reconstruction supplies a uniform degree for every
cuspidal Fourier solution of a fixed finite family of twist laws. -/
theorem uniform_degree {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
    (A : FinitenessCertificate.Certificate N Q hQ) (P : FinitenessGlobalHeight.Parameters A)
    (χ : ℕ → ℂ) (m : ℕ) (hχ : ∀ q, q∣Q → ‖χ q‖=1)
    (a : ℕ → ℂ) (ha : PolynomialBound a) (ha0 : a 0=0)
    (hFE : ∀ q : ℕ, q∣Q → ∀ z : ℂ, 0<z.im →
      FinitenessAnalyticReconstruction.twist (FinitenessFourierConstruction.fourier a) q z =
        χ q / (((Real.sqrt (Nat.lcm N (q^2)) : ℝ):ℂ)*z)^(2*m) *
          FinitenessAnalyticReconstruction.twist (FinitenessFourierConstruction.fourier a)
            q (-1/((Nat.lcm N (q^2):ℕ)*z))) :
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 0<n → ‖a n‖≤C*(n:ℝ)^(m+P.s) := by
  obtain ⟨M,hM0,_,hM⟩ := FinitenessEnvelopeAssembly.global_bound hN A P
    (FinitenessFourierConstruction.fourier a) (FinitenessFourierConstruction.periodic a)
    χ m hχ hFE
    (fun y hy => FinitenessCuspBounds.tail (FinitenessFourierConstruction.fourier a)
      (sum a) (holomorphic ha) (zero ha0) (fun _ _ => rfl) (m+P.s) hy)
  exact ⟨M*Real.exp (2*Real.pi),mul_nonneg hM0 (Real.exp_pos _).le,
    coefficient_le_height_bound ha (m+P.s) hM⟩

#print axioms coefficient_le_circle_bound
#print axioms coefficient_le_height_bound
#print axioms uniform_degree

end AsymptoticCoefficientGrowth
