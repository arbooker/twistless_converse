module

public import QuantitativeNinaMaassWaveIdentificationV1
public import QuantitativeNinaMaassFrickeContinuationV1
public import QuantitativeNinaMaassRamifiedCoefficientsV1
public import QuantitativeNinaMaassHeckeSymmetriesV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory QuantitativeMaass
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip AsymptoticFreshMatrices
open scoped Topology

/-!
Construct the original Euler-product and functional-equation data from an
actual physical eigenform. The bad-prime factors, growth, Euler product,
entire continuation and functional equation are conclusions. Construction
of a full simultaneous eigenfamily in each new-parity band is separate.
-/

namespace QuantitativeNinaMaass

theorem continuous_representative_embedding_ne_zero (N : ℕ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hf0 : f ≠ 0) :
    AutomorphicL2.denseEmbedding _ _ f ≠ 0 := by
  intro h
  apply hf0
  apply continuous_representative_unique N f 0 hf continuous_const
  simpa only [map_zero] using h

theorem representative_fricke_eigen_pointwise (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (χ : ℂ) (hχ : χ * χ = 1)
    (hfr : frickeIsometry N hN (AutomorphicL2.denseEmbedding _ _ f) =
      χ • AutomorphicL2.denseEmbedding _ _ f) (z : UpperHalfPlane) :
    f.val z = χ * f.val (frickeLabel N hN • z) := by
  have he : frickeRepresentative N hN f = χ • f := by
    apply continuous_representative_unique N (frickeRepresentative N hN f) (χ • f)
      (frickeRepresentative_continuous N hN f hf) (continuous_const.mul hf)
    rw [← frickeIsometry_apply, map_smul]
    exact hfr
  have h := congrArg (fun g : AutomorphicL2.representatives (gamma N) (quotientMeasure N) =>
    g.val z) he
  change f.val (frickeLabel N hN • z) = χ * f.val z at h
  rw [h, ← mul_assoc, hχ, one_mul]

theorem normalized_wave_fricke (N : ℕ) [NeZero N] (hN : 0 < N) (r : ℝ) (δ : ℕ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hcf : AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN)
    (hsf : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
      (-1 : ℂ) ^ δ • AutomorphicL2.denseEmbedding _ _ f)
    (ell : ℕ → ℂ) (hr : PrimeHeightEigenrelations N ell (actualHeightCoefficients f.val))
    (hfirst : ∀ y : PositiveHeight,
      horocycleFourier f.val 1 y = scaledBesselProfile r (2 * Real.pi) y.val)
    (hell : ∀ p : ℕ, p.Prime → ‖ell p‖ ≤ (p : ℝ) + 1)
    (χ : ℂ) (hχ : χ * χ = 1)
    (hfr : frickeIsometry N hN (AutomorphicL2.denseEmbedding _ _ f) =
      χ • AutomorphicL2.denseEmbedding _ _ f) :
    ∀ x y : ℝ, 0 < y →
      principalEulerWave (physicalAmplitudeCoefficients r f.val) r δ (x, y) =
        χ * principalEulerWave (physicalAmplitudeCoefficients r f.val) r δ
          (MaassDifferential.F N x y) := by
  let b := physicalAmplitudeCoefficients r f.val
  have hw (z : UpperHalfPlane) : f.val z = (Real.sqrt (2 * Real.pi) : ℂ) *
      principalEulerWave b r δ (z.re, z.im) := by
    have hz : horocyclePoint z.re z.im z.im_pos = z := by
      apply UpperHalfPlane.ext
      exact Complex.eta z
    simpa only [hz] using normalized_representative_eq_eulerWave N hN r δ f hf hcf hsf
      ell hr hfirst hell z.re z.im z.im_pos
  intro x y hy
  let z := horocyclePoint x y hy
  have h := representative_fricke_eigen_pointwise N hN f hf χ hχ hfr z
  rw [hw z, hw (frickeLabel N hN • z), ← frickeLabel_cartesian] at h
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)).ne')
  change (Real.sqrt (2 * Real.pi) : ℂ) * principalEulerWave b r δ (x, y) = _
  calc
    _ = χ * ((Real.sqrt (2 * Real.pi) : ℂ) *
        principalEulerWave b r δ (MaassDifferential.F N x y)) := h
    _ = _ := by ring

/-- All original Euler-solution conditions follow from an actual
normalized simultaneous eigenform, including ramified primes. -/
theorem normalized_eigenform_euler_solution (N : ℕ) [NeZero N] (hN : 0 < N)
    (r : ℝ) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hf0 : f ≠ 0)
    (hcf : AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN)
    (hnew : AutomorphicL2.denseEmbedding _ _ f ∈ newSpace N hN)
    (hsf : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
      (-1 : ℂ) ^ δ • AutomorphicL2.denseEmbedding _ _ f)
    (χ : ℂ) (hχ : χ = 1 ∨ χ = -1)
    (hfr : frickeIsometry N hN (AutomorphicL2.denseEmbedding _ _ f) =
      χ • AutomorphicL2.denseEmbedding _ _ f)
    (ell : ℕ → ℂ)
    (hgood : ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N),
      let : Fact p.Prime := ⟨hp⟩
      ∀ (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1),
        HeckeL2.operator N p hN hpN A B hAB (AutomorphicL2.denseEmbedding _ _ f) =
          ell p • AutomorphicL2.denseEmbedding _ _ f)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), p ∣ N →
      normalizedUpperBranches p hp.pos f.val = fun z => ell p * f.val z)
    (hfirst : ∀ y : PositiveHeight,
      horocycleFourier f.val 1 y = scaledBesselProfile r (2 * Real.pi) y.val) :
    MaassOriginal.IsEulerSolution N (.principal r) δ (physicalAmplitudeCoefficients r f.val) := by
  have hr := physical_prime_height_relations N hN f hf ell hgood hbad
  have hbadquad (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) :
      ell p ^ 2 = if p ^ 2 ∣ N then 0 else (p : ℂ)⁻¹ :=
    ramified_eigenvalue_square N p hN hp hpN f hf hnew hf0 (ell p) (hbad p hp hpN)
  have hell (p : ℕ) (hp : p.Prime) : ‖ell p‖ ≤ (p : ℝ) + 1 := by
    by_cases hpN : p ∣ N
    · exact ramified_eigenvalue_coarse_bound N p hp (ell p) (hbadquad p hp hpN)
    · let : Fact p.Prime := ⟨hp⟩
      have hc : p.Coprime N := hp.coprime_iff_not_dvd.mpr hpN
      have hAB : (p : ℤ) * Nat.gcdA p N + (N : ℤ) * Nat.gcdB p N = 1 := by
        have h := Nat.gcd_eq_gcd_ab p N
        rw [hc.gcd_eq_one, Nat.cast_one] at h
        exact h.symm
      exact hecke_eigenvalue_bound N p hN hpN _ _ hAB _
        (continuous_representative_embedding_ne_zero N f hf hf0) (ell p)
        (hgood p hp hpN _ _ hAB)
  have harith : FinitenessOriginalInput.EulerData N (physicalAmplitudeCoefficients r f.val) := by
    rw [physicalAmplitudeCoefficients_eq N r ell f.val hr hfirst]
    exact canonicalEulerCoefficients_eulerData N ell hell hbadquad
  have hb := physicalAmplitudeCoefficients_polynomialGrowth N r ell f.val hr hfirst hell
  have hχsq : χ * χ = 1 := by rcases hχ with rfl | rfl <;> norm_num
  have hχ0 : χ ≠ 0 := by rcases hχ with rfl | rfl <;> norm_num
  refine { toEulerData := harith, parity := hδ, continuation := ⟨(-1 : ℂ) ^ δ * χ, ?_, ?_⟩ }
  · rcases hδ with rfl | rfl <;> rcases hχ with rfl | rfl <;> norm_num
  · exact eulerWave_continuation_of_fricke hb N (by exact_mod_cast hN) r δ hδ χ hχ0
      (normalized_wave_fricke N hN r δ f hf hcf hsf ell hr hfirst hell χ hχsq hfr)

theorem normalizedUpperBranches_const_mul (p : ℕ) (hp : 0 < p)
    (f : UpperHalfPlane → ℂ) (c : ℂ) :
    normalizedUpperBranches p hp (fun z => c * f z) =
      fun z => c * normalizedUpperBranches p hp f z := by
  funext z
  unfold normalizedUpperBranches
  rw [upperBranchSum_const_mul]
  ring

/-- No first-amplitude assumption is needed for the actual eigenform
constructor: the actual spectral equation, energy, cusp and prime relations
prove nonvanishing and allow normalization internally. -/
theorem actual_eigenform_euler_solution (N : ℕ) [NeZero N] (hN : 0 < N)
    (r : ℝ) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hf0 : f ≠ 0)
    (hcf : AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN)
    (hnew : AutomorphicL2.denseEmbedding _ _ f ∈ newSpace N hN)
    (hsf : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
      (-1 : ℂ) ^ δ • AutomorphicL2.denseEmbedding _ _ f)
    (heigen : FriedrichsGraph N (AutomorphicL2.denseEmbedding _ _ f)
      (((1 / 4 + r ^ 2 : ℝ) : ℂ) • AutomorphicL2.denseEmbedding _ _ f))
    (χ : ℂ) (hχ : χ = 1 ∨ χ = -1)
    (hfr : frickeIsometry N hN (AutomorphicL2.denseEmbedding _ _ f) =
      χ • AutomorphicL2.denseEmbedding _ _ f)
    (ell : ℕ → ℂ)
    (hgood : ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N),
      let : Fact p.Prime := ⟨hp⟩
      ∀ (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1),
        HeckeL2.operator N p hN hpN A B hAB (AutomorphicL2.denseEmbedding _ _ f) =
          ell p • AutomorphicL2.denseEmbedding _ _ f)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), p ∣ N →
      normalizedUpperBranches p hp.pos f.val = fun z => ell p * f.val z) :
    MaassOriginal.IsEulerSolution N (.principal r) δ (canonicalEulerCoefficients N ell) := by
  have hr := physical_prime_height_relations N hN f hf ell hgood hbad
  obtain ⟨C, hC, hfirst⟩ := actual_nonzero_bessel_amplitude N hN f hf hf0 hcf
    ((-1 : ℂ) ^ δ) hsf r heigen ell hr
  let g := C⁻¹ • f
  have hg : Continuous g.val := continuous_const.mul hf
  have hg0 : g ≠ 0 := smul_ne_zero (inv_ne_zero hC) hf0
  have hcg : AutomorphicL2.denseEmbedding _ _ g ∈ localCuspidalSpace N hN := by
    simp only [g, map_smul]
    exact (localCuspidalSpace N hN).smul_mem C⁻¹ hcf
  have hng : AutomorphicL2.denseEmbedding _ _ g ∈ newSpace N hN := by
    simp only [g, map_smul]
    exact (newSpace N hN).smul_mem C⁻¹ hnew
  have hsg : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ g) =
      (-1 : ℂ) ^ δ • AutomorphicL2.denseEmbedding _ _ g := by
    simp only [g, map_smul, hsf, smul_smul, mul_comm C⁻¹]
  have hfg : frickeIsometry N hN (AutomorphicL2.denseEmbedding _ _ g) =
      χ • AutomorphicL2.denseEmbedding _ _ g := by
    simp only [g, map_smul, hfr, smul_smul, mul_comm C⁻¹]
  obtain ⟨hfirstg, _hrg, hcoeffg⟩ := normalize_actual_bessel_amplitude N r ell f hr C hC hfirst
  have hsol := normalized_eigenform_euler_solution N hN r δ hδ g hg hg0 hcg hng hsg
    χ hχ hfg ell (by
      intro p hp hpN _ A B hAB
      simp only [g, map_smul, hgood p hp hpN A B hAB, smul_smul, mul_comm C⁻¹]) (by
      intro p hp hpN
      change normalizedUpperBranches p hp.pos (fun z => C⁻¹ * f.val z) =
        fun z => ell p * (C⁻¹ * f.val z)
      rw [normalizedUpperBranches_const_mul, hbad p hp hpN]
      funext z
      ring) hfirstg
  rwa [hcoeffg] at hsol

#print axioms continuous_representative_embedding_ne_zero
#print axioms representative_fricke_eigen_pointwise
#print axioms normalized_wave_fricke
#print axioms normalized_eigenform_euler_solution
#print axioms normalizedUpperBranches_const_mul
#print axioms actual_eigenform_euler_solution

end QuantitativeNinaMaass
