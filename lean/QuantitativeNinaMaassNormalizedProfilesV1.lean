module

public import QuantitativeNinaMaassBesselProfileV1
public import QuantitativeNinaMaassFourierAmplitudesV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory QuantitativeMaass
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology

/-!
Normalization and separation using literal Fourier integrals of actual
continuous cuspidal representatives. The prime recurrences in this chapter
are the explicit intermediate interface supplied by physical prime
eigenrelations; no injectivity or multiplicity-one statement is assumed.
The simultaneous physical eigenfamily and its functional equation are
separate obligations.
-/

namespace QuantitativeNinaMaass

def besselAnchor (r : ℝ) : PositiveHeight :=
  ⟨max 2 ((|r| + 1) / (2 * Real.pi)),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)⟩

theorem besselAnchor_profile_ne_zero (r : ℝ) :
    scaledBesselProfile r (2 * Real.pi) (besselAnchor r).val ≠ 0 := by
  apply scaledBesselProfile_ne_zero r _ _ (by positivity) (besselAnchor r).property
  have hk : 0 < 2 * Real.pi := by positivity
  have h := (div_le_iff₀ hk).mp (le_max_right 2 ((|r| + 1) / (2 * Real.pi)))
  have hh : |r| + 1 ≤ (2 * Real.pi) * (besselAnchor r).val := by
    simpa only [besselAnchor, mul_comm] using h
  have hs := (sq_le_sq₀ (show 0 ≤ |r| + 1 by positivity)
    (mul_pos hk (besselAnchor r).property).le).mpr hh
  nlinarith [sq_abs r, abs_nonneg r]

/-- A literal coefficient map, evaluated at a specified positive height.
Its definition uses the actual Fourier integrals, not chosen eigenvalues. -/
def physicalAmplitudeCoefficients (r : ℝ) (f : UpperHalfPlane → ℂ) : ℕ → ℂ :=
  fun n => scaledHeightCoefficients (actualHeightCoefficients f) (besselAnchor r) n /
    scaledBesselProfile r (2 * Real.pi) (besselAnchor r).val

theorem physicalAmplitudeCoefficients_eq (N : ℕ) (r : ℝ) (ell : ℕ → ℂ)
    (f : UpperHalfPlane → ℂ)
    (hr : PrimeHeightEigenrelations N ell (actualHeightCoefficients f))
    (hfirst : ∀ y : PositiveHeight,
      horocycleFourier f 1 y = scaledBesselProfile r (2 * Real.pi) y.val) :
    physicalAmplitudeCoefficients r f = canonicalEulerCoefficients N ell := by
  funext n
  unfold physicalAmplitudeCoefficients
  rw [scaledHeightCoefficients_factorization N ell _ hr]
  change canonicalEulerCoefficients N ell n * horocycleFourier f 1 (besselAnchor r) / _ = _
  rw [hfirst, mul_div_cancel_right₀ _ (besselAnchor_profile_ne_zero r)]

theorem actualHeightCoefficients_const_mul (c : ℂ) (f : UpperHalfPlane → ℂ) :
    actualHeightCoefficients (fun z => c * f z) = c • actualHeightCoefficients f := by
  funext n y
  exact horocycleFourier_const_mul f c n y

theorem prime_height_relations_smul (N : ℕ) (ell : ℕ → ℂ)
    (c : HeightCoefficients) (hc : PrimeHeightEigenrelations N ell c) (a : ℂ) :
    PrimeHeightEigenrelations N ell (a • c) := by
  intro p hp n y
  have h := hc p hp n y
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs at h ⊢ with hi
  · linear_combination a * h
  · linear_combination a * h

/-- The ODE and energy proof supplies the Bessel profile, and the prime
descent plus actual cusp/parity uniqueness supplies its nonzero amplitude. -/
theorem actual_nonzero_bessel_amplitude (N : ℕ) (hN : 0 < N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hf0 : f ≠ 0)
    (hcf : AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN)
    (s : ℂ)
    (hsf : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
      s • AutomorphicL2.denseEmbedding _ _ f)
    (r : ℝ)
    (heigen : FriedrichsGraph N (AutomorphicL2.denseEmbedding _ _ f)
      (((1 / 4 + r ^ 2 : ℝ) : ℂ) • AutomorphicL2.denseEmbedding _ _ f))
    (ell : ℕ → ℂ) (hr : PrimeHeightEigenrelations N ell (actualHeightCoefficients f.val)) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ y : PositiveHeight,
      horocycleFourier f.val 1 y = C * scaledBesselProfile r (2 * Real.pi) y.val := by
  obtain ⟨C, hC⟩ := actual_first_bessel_profile N f hf r heigen
  have he (y : PositiveHeight) :
      horocycleFourier f.val 1 y = C * scaledBesselProfile r (2 * Real.pi) y.val := by
    have h := hC y.val y.property
    rwa [cartesianFourier_horocycle f.val 1 y.val y.property] at h
  refine ⟨C, ?_, he⟩
  intro hz
  have hzero := prime_height_first_zero N ell (actualHeightCoefficients f.val) hr
    (by intro y; change horocycleFourier f.val 1 y = 0; rw [he, hz, zero_mul])
  apply hf0
  apply physical_positive_coefficients_separate N hN f 0 hf continuous_const hcf
    (by simpa only [map_zero] using (localCuspidalSpace N hN).zero_mem) s hsf
    (by simp only [map_zero, smul_zero])
  funext n y
  have h := hzero (n + 1) (by omega) y
  change _ = unitLineFourierCoeff (fun _ : ℝ => 0) (n + 1)
  simpa only [positiveHorocycleCoefficients, actualHeightCoefficients, horocycleFourier,
    Nat.cast_add, Nat.cast_one, unitLineFourierCoeff, mul_zero, intervalIntegral.integral_zero]
    using h

/-- Normalize by the proved nonzero first Bessel amplitude. All positive
Fourier profiles then carry the same canonical Euler coefficients. -/
theorem normalize_actual_bessel_amplitude (N : ℕ) (r : ℝ) (ell : ℕ → ℂ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hr : PrimeHeightEigenrelations N ell (actualHeightCoefficients f.val))
    (C : ℂ) (hC : C ≠ 0)
    (hfirst : ∀ y : PositiveHeight,
      horocycleFourier f.val 1 y = C * scaledBesselProfile r (2 * Real.pi) y.val) :
    (∀ y : PositiveHeight, horocycleFourier (C⁻¹ • f).val 1 y =
      scaledBesselProfile r (2 * Real.pi) y.val) ∧
    PrimeHeightEigenrelations N ell (actualHeightCoefficients (C⁻¹ • f).val) ∧
    physicalAmplitudeCoefficients r (C⁻¹ • f).val = canonicalEulerCoefficients N ell := by
  have hnorm (y : PositiveHeight) : horocycleFourier (C⁻¹ • f).val 1 y =
      scaledBesselProfile r (2 * Real.pi) y.val := by
    change horocycleFourier (fun z => C⁻¹ * f.val z) 1 y = _
    rw [horocycleFourier_const_mul, hfirst, ← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  have hrel : PrimeHeightEigenrelations N ell (actualHeightCoefficients (C⁻¹ • f).val) := by
    change PrimeHeightEigenrelations N ell (actualHeightCoefficients (fun z => C⁻¹ * f.val z))
    rw [actualHeightCoefficients_const_mul]
    exact prime_height_relations_smul N ell _ hr C⁻¹
  exact ⟨hnorm, hrel, physicalAmplitudeCoefficients_eq N r ell _ hrel hnorm⟩

theorem normalized_positive_profile (N : ℕ) (r : ℝ) (ell : ℕ → ℂ)
    (f : UpperHalfPlane → ℂ)
    (hr : PrimeHeightEigenrelations N ell (actualHeightCoefficients f))
    (hfirst : ∀ y : PositiveHeight,
      horocycleFourier f 1 y = scaledBesselProfile r (2 * Real.pi) y.val)
    (n : ℕ) (hn : 0 < n) (y : PositiveHeight) :
    (Real.sqrt (n : ℝ) : ℂ) * horocycleFourier f n y =
      physicalAmplitudeCoefficients r f n *
        scaledBesselProfile r (2 * Real.pi) ((n : ℝ) * y.val) := by
  have h := prime_height_profile_factorization N ell (actualHeightCoefficients f) hr n hn y
  change (Real.sqrt (n : ℝ) : ℂ) * horocycleFourier f n y =
    canonicalEulerCoefficients N ell n * horocycleFourier f 1 (multiplyHeight n hn y) at h
  rw [hfirst, ← physicalAmplitudeCoefficients_eq N r ell f hr hfirst] at h
  exact h

/-- Distinct normalized actual cusp representatives of the same parameter
and reflection parity have distinct coefficient sequences. This follows
from the proved profile factorization and physical Fourier uniqueness. -/
theorem normalized_physical_amplitudes_separate (N : ℕ) (hN : 0 < N) (r : ℝ)
    (f g : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hg : Continuous g.val)
    (hcf : AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN)
    (hcg : AutomorphicL2.denseEmbedding _ _ g ∈ localCuspidalSpace N hN)
    (s : ℂ)
    (hsf : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
      s • AutomorphicL2.denseEmbedding _ _ f)
    (hsg : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ g) =
      s • AutomorphicL2.denseEmbedding _ _ g)
    (ell eta : ℕ → ℂ)
    (hrf : PrimeHeightEigenrelations N ell (actualHeightCoefficients f.val))
    (hrg : PrimeHeightEigenrelations N eta (actualHeightCoefficients g.val))
    (hfirstf : ∀ y : PositiveHeight,
      horocycleFourier f.val 1 y = scaledBesselProfile r (2 * Real.pi) y.val)
    (hfirstg : ∀ y : PositiveHeight,
      horocycleFourier g.val 1 y = scaledBesselProfile r (2 * Real.pi) y.val)
    (he : physicalAmplitudeCoefficients r f.val = physicalAmplitudeCoefficients r g.val) :
    f = g := by
  apply physical_positive_coefficients_separate N hN f g hf hg hcf hcg s hsf hsg
  funext n y
  have h := normalized_positive_profile N r ell f.val hrf hfirstf (n + 1) (by omega) y
  have k := normalized_positive_profile N r eta g.val hrg hfirstg (n + 1) (by omega) y
  rw [he] at h
  have hk := mul_left_cancel₀ (sqrt_nat_ne_zero (n + 1) (by omega)) (h.trans k.symm)
  simpa only [positiveHorocycleCoefficients, horocycleFourier, Nat.cast_add, Nat.cast_one] using hk

#print axioms besselAnchor_profile_ne_zero
#print axioms physicalAmplitudeCoefficients_eq
#print axioms actualHeightCoefficients_const_mul
#print axioms prime_height_relations_smul
#print axioms actual_nonzero_bessel_amplitude
#print axioms normalize_actual_bessel_amplitude
#print axioms normalized_positive_profile
#print axioms normalized_physical_amplitudes_separate

end QuantitativeNinaMaass
