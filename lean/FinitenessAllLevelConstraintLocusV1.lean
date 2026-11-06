module

public import FinitenessAllLevelOriginalEquationsV1
public import FinitenessAllLevelFunctionalChartV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Metric Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelGoodTrace FinitenessAllLevelFormalContinuation
  FinitenessAllLevelCoefficientFunctional FinitenessAllLevelCauchyConstraints
  FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
  QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedReconstruction
  FinitenessAnalyticReconstruction

theorem twist_congr_upper {F G : ℂ → ℂ}
    (he : ∀ z : ℂ, 0 < z.im → F z = G z) (q : ℕ) {z : ℂ} (hz : 0 < z.im) :
    twist F q z = twist G q z := by
  apply Finset.sum_congr rfl
  intro j _
  apply he
  simpa using hz

theorem complete_congr_upper {F G : ℂ → ℂ}
    (he : ∀ z : ℂ, 0 < z.im → F z = G z) (q : ℕ) {z : ℂ} (hz : 0 < z.im) :
    completeTwist F q z = completeTwist G q z := by
  apply Finset.sum_congr rfl
  intro j _
  apply he
  simpa using hz

variable {N Q p : ℕ} {hQ : 0 < Q}

/-- The exact infinite system of spatial and coefficient equations.
This definition asserts no local finite generation or analytic-space structure. -/
structure Constraints (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a)) : Prop where
  cauchy : CauchyIdentities (formal A P a χ m lam F)
  fricke : ∀ q : ℕ, q ∣ Q → ∀ z : ℂ, 0 < z.im →
    twist (formal A P a χ m lam F) q z =
      χ q / (((Real.sqrt (Nat.lcm N (q ^ 2)) : ℝ) : ℂ) * z) ^ (2 * m) *
        twist (formal A P a χ m lam F) q (-1 / ((Nat.lcm N (q ^ 2) : ℕ) * z))
  hecke : ∀ z : ℂ, 0 < z.im →
    completeTwist (formal A P a χ m lam F) p z =
      firstMultiplier (fun _ => lam) m p * formal A P a χ m lam F ((p : ℂ) * z) -
        (p : ℂ) ^ (2 * m) * formal A P a χ m lam F ((p : ℂ) ^ 2 * z)
  euler : ∀ e : FinitenessAllLevelEulerEquations.Equation N,
    FinitenessAllLevelEulerEquations.equation N (2 * m) p (radius_pos a) e (lam, F) = 0

/-- Every original solution lies in this exact zero locus for one coherent
root-number sector, with its actual eigenvalue and disk representative. -/
theorem original_constraints (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε) (m : ℕ) (f : S N (2 * m)) :
    ∃ χ : ℕ → ℂ, (∀ q, χ q = I ^ (2 * m) ∨ χ q = -I ^ (2 * m)) ∧
      (∀ q, ‖χ q‖ = 1) ∧ Constraints A P a χ m (f.val p)
        (representative N (2 * m) (radius_pos a) (radius_lt_one ha) f) := by
  obtain ⟨χ, hs, hn, hFE, he⟩ :=
    original_formal_with_laws hN hp hgood hpQ A P ha hae m f
  refine ⟨χ, hs, hn, ?_⟩
  constructor
  · apply identities_of_differentiableOn
    apply (show DifferentiableOn ℂ (fourier (fullCoefficients f.val (2 * m)))
        {z : ℂ | 0 < z.im} from fun z hz =>
      (holomorphic (FinitenessOriginalDiskIndependence.polynomial N (2 * m) f) hz).differentiableWithinAt).congr
    exact he
  · intro q hq z hz
    have hL : 0 < Nat.lcm N (q ^ 2) := Nat.lcm_pos hN (pow_pos (Nat.pos_of_dvd_of_pos hq hQ) _)
    have hr : 0 < (-1 / ((Nat.lcm N (q ^ 2) : ℕ) * z)).im := by
      simpa only [ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
        (L := (Nat.lcm N (q ^ 2) : ℝ)) (by exact_mod_cast hL) hz
    rw [twist_congr_upper he q hz, twist_congr_upper he q hr]
    exact hFE q hq z hz
  · intro z hz
    have hz1 : 0 < ((p : ℂ) * z).im := by
      simpa using mul_pos (Nat.cast_pos.mpr hp.pos : (0 : ℝ) < p) hz
    have hz2 : 0 < ((p : ℂ) ^ 2 * z).im := by
      simpa only [← ofReal_natCast, ← ofReal_pow, mul_im, ofReal_re, ofReal_im,
        zero_mul, add_zero] using mul_pos (pow_pos (Nat.cast_pos.mpr hp.pos : (0 : ℝ) < p) 2) hz
    rw [complete_congr_upper he p hz, he _ hz1, he _ hz2]
    exact original_complete_even f.property.toEulerData hp hgood m hz
  · exact FinitenessAllLevelEulerEquations.original_equations p (radius_pos a) (radius_lt_one ha) f

/-- Conversely, a constrained disk vector is precisely the representative
of an original solution with the specified eigenvalue. -/
theorem constraints_recover (hN : 0 < N) (hp : p.Prime) (hpQ : p ∣ Q)
    {m : ℕ} (hm : 0 < m) (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε) (χ : ℕ → ℂ) (lam : ℂ)
    (F : space (radius a)) (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1) (hlam : ‖lam‖ ≤ L)
    (hs : χ 1 = I ^ (2 * m) ∨ χ 1 = -(I ^ (2 * m)))
    (hc : Constraints A P a χ m lam F) :
    ∃ f : S N (2 * m), f.val p = lam ∧
      representative N (2 * m) (radius_pos a) (radius_lt_one ha) f = F := by
  obtain ⟨hf, heig⟩ := solution_of_equations hN hp hpQ hm A P ha hae χ lam F hχ hlam hs
    hc.cauchy hc.fricke hc.hecke hc.euler
  obtain ⟨M, hM, hb⟩ := global_height_of_equations hN hp hpQ A P ha hae χ m lam F hχ hlam
    hc.cauchy hc.fricke hc.hecke
  exact ⟨⟨_, hf⟩, heig, representative_recovered hN hp A P ha hae χ m lam F hc.cauchy hM hb hf⟩

#print axioms original_constraints
#print axioms constraints_recover

end FinitenessAllLevelConstraintLocus
