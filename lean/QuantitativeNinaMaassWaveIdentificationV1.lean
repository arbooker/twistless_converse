module

public import QuantitativeNinaMaassNormalizedProfilesV1
public import QuantitativeMaassEulerZeroMeanV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory QuantitativeMaass
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology

/-!
Identification of an actual normalized cusp eigenfunction with the existing
literal Euler Fourier--Bessel wave. Polynomial coefficient growth gives
convergence; the checked Fourier coefficients, cusp constants and parity
then give pointwise equality. No automorphy of the reconstructed wave is
an assumption in this identification.
-/

namespace QuantitativeNinaMaass

theorem lineCharacter_eq_eulerCharacter (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle (1 : ℝ)) = eulerCharacter n x := by
  rw [fourier_coe_apply]
  unfold eulerCharacter
  simp only [Complex.ofReal_one, div_one]
  congr 1
  push_cast
  ring

theorem unitLineFourierCoeff_principalEulerWave {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (r : ℝ) (δ n : ℕ)
    (y : ℝ) (hy : 0 < y) :
    unitLineFourierCoeff (fun x => principalEulerWave b r δ (x, y)) (n + 1) =
      (Real.sqrt y : ℂ) * (b (n + 1) * (MaassKBessel.K r (2 * Real.pi * (n + 1) * y) : ℂ)) := by
  unfold unitLineFourierCoeff
  simp only [lineCharacter_eq_eulerCharacter,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa only [Nat.cast_add, Nat.cast_one, MaassKBessel.moment_zero] using
    principalEulerWave_coefficient hb r δ n y hy

theorem unitLineFourierCoeff_principalEulerWave_zero {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (r : ℝ) (δ : ℕ)
    (y : ℝ) (hy : 0 < y) :
    unitLineFourierCoeff (fun x => principalEulerWave b r δ (x, y)) 0 = 0 := by
  rw [unitLineFourierCoeff_zero,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact principalEulerWave_mean_zero hb r δ y hy

theorem scaledBesselProfile_nat (r k : ℝ) (hk : 0 ≤ k) (n : ℕ)
    (y : ℝ) (_hy : 0 ≤ y) :
    scaledBesselProfile r k ((n : ℝ) * y) =
      (Real.sqrt (n : ℝ) : ℂ) * ((Real.sqrt k : ℂ) *
        ((Real.sqrt y : ℂ) * (MaassKBessel.K r (k * n * y) : ℂ))) := by
  unfold scaledBesselProfile MaassKBessel.W MaassSqrtRescaling.W
  rw [Real.sqrt_mul hk, Real.sqrt_mul (Nat.cast_nonneg n)]
  rw [← mul_assoc k (n : ℝ) y]
  push_cast
  ring

theorem normalized_profile_standard (N : ℕ) (r : ℝ) (ell : ℕ → ℂ)
    (f : UpperHalfPlane → ℂ)
    (hr : PrimeHeightEigenrelations N ell (actualHeightCoefficients f))
    (hfirst : ∀ y : PositiveHeight,
      horocycleFourier f 1 y = scaledBesselProfile r (2 * Real.pi) y.val)
    (n : ℕ) (hn : 0 < n) (y : PositiveHeight) :
    horocycleFourier f n y = (Real.sqrt (2 * Real.pi) : ℂ) *
      ((Real.sqrt y.val : ℂ) * (physicalAmplitudeCoefficients r f n *
        (MaassKBessel.K r (2 * Real.pi * n * y.val) : ℂ))) := by
  have h := normalized_positive_profile N r ell f hr hfirst n hn y
  rw [scaledBesselProfile_nat r (2 * Real.pi) (by positivity) n y.val y.property.le] at h
  apply mul_left_cancel₀ (sqrt_nat_ne_zero n hn)
  calc
    _ = _ := h
    _ = _ := by ring

theorem physicalAmplitudeCoefficients_polynomialGrowth (N : ℕ) (r : ℝ) (ell : ℕ → ℂ)
    (f : UpperHalfPlane → ℂ)
    (hr : PrimeHeightEigenrelations N ell (actualHeightCoefficients f))
    (hfirst : ∀ y : PositiveHeight,
      horocycleFourier f 1 y = scaledBesselProfile r (2 * Real.pi) y.val)
    (hell : ∀ p : ℕ, p.Prime → ‖ell p‖ ≤ (p : ℝ) + 1) :
    MaassOriginal.PolynomialGrowth (physicalAmplitudeCoefficients r f) := by
  rw [physicalAmplitudeCoefficients_eq N r ell f hr hfirst]
  exact ⟨2, (canonicalEulerCoefficients_growth N ell hell).norm_left⟩

/-- The actual normalized representative equals the convergent literal
wave, up to the fixed common sqrt(2*pi) used in the first-profile convention.
All coefficients here are the literal amplitude map of the representative. -/
theorem normalized_representative_eq_eulerWave (N : ℕ) (hN : 0 < N) (r : ℝ) (δ : ℕ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hcf : AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN)
    (hsf : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
      (-1 : ℂ) ^ δ • AutomorphicL2.denseEmbedding _ _ f)
    (ell : ℕ → ℂ) (hr : PrimeHeightEigenrelations N ell (actualHeightCoefficients f.val))
    (hfirst : ∀ y : PositiveHeight,
      horocycleFourier f.val 1 y = scaledBesselProfile r (2 * Real.pi) y.val)
    (hell : ∀ p : ℕ, p.Prime → ‖ell p‖ ≤ (p : ℝ) + 1)
    (x y : ℝ) (hy : 0 < y) :
    f.val (horocyclePoint x y hy) = (Real.sqrt (2 * Real.pi) : ℂ) *
      principalEulerWave (physicalAmplitudeCoefficients r f.val) r δ (x, y) := by
  let b := physicalAmplitudeCoefficients r f.val
  have hb : MaassOriginal.PolynomialGrowth b :=
    physicalAmplitudeCoefficients_polynomialGrowth N r ell f.val hr hfirst hell
  have hw : Continuous (fun u : ℝ => principalEulerWave b r δ (u, y)) :=
    (principalEulerWave_continuousOn hb r δ).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => hy)
  have he := continuous_periodic_eq_of_nonnegative_fourier
    (fun u => f.val (horocyclePoint u y hy))
    (fun u => (Real.sqrt (2 * Real.pi) : ℂ) * principalEulerWave b r δ (u, y))
    (hf.comp (horocyclePoint_continuous y hy)) (continuous_const.mul hw)
    (representative_unit_periodic N f y hy)
    (by
      intro u
      exact congrArg (fun z : ℂ => (Real.sqrt (2 * Real.pi) : ℂ) * z)
        (principalEulerWave_periodic b r δ y u))
    ((-1 : ℂ) ^ δ)
    (fun u => representative_pointwise_parity N f hf _ hsf u y hy)
    (by intro u; rw [principalEulerWave_reflection]; ring) (by
      intro n
      rw [unitLineFourierCoeff_const_mul]
      cases n with
      | zero =>
        simp only [Nat.cast_zero]
        rw [representative_unit_mean_zero N hN f hf hcf,
          unitLineFourierCoeff_principalEulerWave_zero hb r δ y hy, mul_zero]
      | succ n =>
        simp only [Nat.cast_add, Nat.cast_one]
        rw [unitLineFourierCoeff_principalEulerWave hb r δ n y hy]
        have h := normalized_profile_standard N r ell f.val hr hfirst (n + 1) (by omega) ⟨y, hy⟩
        simpa only [horocycleFourier, Nat.cast_add, Nat.cast_one] using h)
  exact congrFun he x

#print axioms lineCharacter_eq_eulerCharacter
#print axioms unitLineFourierCoeff_principalEulerWave
#print axioms unitLineFourierCoeff_principalEulerWave_zero
#print axioms scaledBesselProfile_nat
#print axioms normalized_profile_standard
#print axioms physicalAmplitudeCoefficients_polynomialGrowth
#print axioms normalized_representative_eq_eulerWave

end QuantitativeNinaMaass
