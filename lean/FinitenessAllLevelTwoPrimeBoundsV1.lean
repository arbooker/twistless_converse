module

public import FinitenessAllLevelHeckePowerV1
public import FinitenessAllLevelNormalizedFunctionalV1
public import FinitenessAllLevelPrimeRigidityV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelTwoPrimeBounds

open Complex FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelCertificateBoundary FinitenessAllLevelGlobalHeight
  FinitenessAllLevelFormalContinuation FinitenessAllLevelHeckePower
  FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
  QuantitativeArithmeticRetainedCertificate

theorem representative_norm_pos {N k : ℕ} {a : ℝ} (ha : 0 < a) (f : S N k) :
    0 < ‖representative N k (radius_pos a) (radius_lt_one ha) f‖ := by
  apply norm_pos_iff.mpr
  intro he
  have h := FinitenessAllLevelCoefficientFunctional.normalized_representative
    (radius_pos a) (radius_lt_one ha) f 1
  rw [he, map_zero, (FinitenessEulerIdentification.solution_arithmetic f.property).1] at h
  exact zero_ne_one h

/-- The two-prime bound for actual original solutions in a fixed formal
reconstruction sector. No uniform coefficient-growth constant is assumed. -/
theorem power_comparison {N Q r p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hr : r.Prime) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (A : Certificate N {r} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε) (χ : ℕ → ℂ) (m t j : ℕ)
    (hpow : (p : ℝ) ^ t ≤ (r : ℝ) ^ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : S N (2 * m),
      (∀ z : ℂ, 0 < z.im → formal A P a χ m (f.val r)
        (representative N (2 * m) (radius_pos a) (radius_lt_one ha) f) z =
          fourier (fullCoefficients f.val (2 * m)) z) →
      ‖f.val p‖ ^ t ≤ C * (1 + ‖f.val r‖) ^ j := by
  obtain ⟨B, hB, hb⟩ := formal_sharp_height hN hr A P ha hae χ m j
  let α : ℂ := (scale p m)⁻¹
  let β : ℂ := α * (p : ℂ) ^ (2 * m)
  let D : ℝ := ‖α‖ * p + ‖β‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D ^ t * B, mul_nonneg (pow_nonneg hD _) hB, fun f he => ?_⟩
  let F := representative N (2 * m) (radius_pos a) (radius_lt_one ha) f
  let G := fourier (fullCoefficients f.val (2 * m))
  have htail : ∀ z : ℂ, a / (p : ℝ) ^ t ≤ z.im →
      ‖G z‖ ≤ B * (1 + ‖f.val r‖) ^ j * ‖F‖ := by
    intro z hz
    have hz' : a / (r : ℝ) ^ j ≤ z.im :=
      (div_le_div_of_nonneg_left ha.le (pow_pos (Nat.cast_pos.mpr hp.pos) _) hpow).trans hz
    dsimp only [G]
    rw [← he z ((div_pos ha (pow_pos (Nat.cast_pos.mpr hp.pos) _)).trans_le hz)]
    exact hb _ _ _ hz'
  have hnorm : ‖(f.val p ^ t) • F‖ ≤ D ^ t * (B * (1 + ‖f.val r‖) ^ j * ‖F‖) := by
    apply norm_le_of_tail ((f.val p ^ t) • F) (fun z => f.val p ^ t * G z) _ (by positivity)
    · intro z hz
      rw [norm_mul, norm_pow]
      exact power_bound hp.one_lt.le α β (f.val p) G
        (fun w hw => original_relation hp hgood m f.property.toEulerData hw) t ha htail hz
    · intro z hz
      change extend ((f.val p ^ t) • F.val) (Function.Periodic.qParam 1 z) = _
      rw [extend_smul]
      change f.val p ^ t * lift F z = _
      rw [FinitenessAllLevelPencilHeights.lift_representative f ha hz]
  rw [norm_smul, norm_pow] at hnorm
  apply (mul_le_mul_iff_left₀ (representative_norm_pos ha f)).mp
  change ‖f.val p‖ ^ t * ‖F‖ ≤ _
  convert hnorm using 1
  ring

theorem pow_le_pow_ceil {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (t : ℕ) :
    (p : ℝ) ^ t ≤ (r : ℝ) ^ Nat.ceil ((t : ℝ) * (Real.log p / Real.log r)) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.mpr hr.pos
  have hlr : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr.one_lt)
  apply (Real.log_le_log_iff (pow_pos hp0 _) (pow_pos hr0 _)).mp
  rw [Real.log_pow, Real.log_pow]
  calc
    (t : ℝ) * Real.log p = ((t : ℝ) * (Real.log p / Real.log r)) * Real.log r := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hlr.le

theorem ceiling_comparison {N Q r p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hr : r.Prime) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (A : Certificate N {r} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε) (χ : ℕ → ℂ) (m t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : S N (2 * m),
      (∀ z : ℂ, 0 < z.im → formal A P a χ m (f.val r)
        (representative N (2 * m) (radius_pos a) (radius_lt_one ha) f) z =
          fourier (fullCoefficients f.val (2 * m)) z) →
      ‖f.val p‖ ^ t ≤ C * (1 + ‖f.val r‖) ^
        Nat.ceil ((t : ℝ) * (Real.log p / Real.log r)) :=
  power_comparison hN hr hp hgood A P ha hae χ m t _ (pow_le_pow_ceil hp hr t)

#print axioms power_comparison
#print axioms pow_le_pow_ceil
#print axioms ceiling_comparison

end FinitenessAllLevelTwoPrimeBounds
