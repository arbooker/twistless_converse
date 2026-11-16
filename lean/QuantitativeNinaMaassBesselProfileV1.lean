module

public import QuantitativeNinaMaassFourierEnergyV1
public import QuantitativeNinaMaassTailUniquenessV1
public import MaassKBesselComparisonV1
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory QuantitativeMaass
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology

/-!
The actual decaying Bessel profile, with its spatial scaling, classical
derivatives and finite hyperbolic energy. The subsequent comparison uses
the actual Fourier-profile equation and energy, rather than postulating a
Fourier--Bessel expansion for a spectral vector.
-/

namespace QuantitativeNinaMaass

def scaledBesselProfile (r k y : ℝ) : ℂ := (MaassKBessel.W r (k * y) : ℂ)

def scaledBesselVelocity (r k y : ℝ) : ℂ := (k * MaassKBessel.W₁ r (k * y) : ℝ)

def scaledBesselPotential (r k y : ℝ) : ℝ := k ^ 2 - (r ^ 2 + 1 / 4) / y ^ 2

theorem scaledBesselProfile_hasDerivAt (r k : ℝ) (hk : 0 < k) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (scaledBesselProfile r k) (scaledBesselVelocity r k y) y := by
  have h := (MaassKBessel.W_hasDerivAt r (mul_pos hk hy)).comp y ((hasDerivAt_id y).const_mul k)
  simpa only [scaledBesselProfile, scaledBesselVelocity, Function.comp_apply, id_eq, mul_one, mul_comm]
    using! h.ofReal_comp

theorem scaledBesselVelocity_hasDerivAt (r k : ℝ) (hk : 0 < k) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (scaledBesselVelocity r k)
      (scaledBesselPotential r k y • scaledBesselProfile r k y) y := by
  have h := ((MaassKBessel.W₁_hasDerivAt r (mul_pos hk hy)).comp y
    ((hasDerivAt_id y).const_mul k)).const_mul k
  have he : k * (MaassKBessel.W₂ r (k * y) * k) =
      scaledBesselPotential r k y * MaassKBessel.W r (k * y) := by
    rw [MaassKBessel.W_ode r (mul_pos hk hy)]
    unfold scaledBesselPotential
    field_simp [hk.ne', hy.ne']
  simp only [mul_one] at h
  rw [he] at h
  dsimp only [scaledBesselProfile, scaledBesselVelocity]
  rw [Complex.real_smul, ← Complex.ofReal_mul]
  simpa only [Function.comp_apply, id_eq] using! h.ofReal_comp

theorem scaledBesselProfile_continuousOn (r k : ℝ) (hk : 0 < k) :
    ContinuousOn (scaledBesselProfile r k) (Ioi 0) :=
  fun y hy => (scaledBesselProfile_hasDerivAt r k hk y hy).continuousAt.continuousWithinAt

theorem scaledBesselPotential_continuousOn (r k : ℝ) :
    ContinuousOn (scaledBesselPotential r k) (Ioi 0) :=
  continuous_const.continuousOn.sub (continuous_const.continuousOn.div (continuousOn_id.pow 2)
    (fun _ hy => pow_ne_zero 2 (ne_of_gt hy)))

theorem scaledBesselProfile_ne_zero (r k y : ℝ) (hk : 0 < k) (hy : 0 < y)
    (hthreshold : r ^ 2 + 1 / 4 ≤ (k * y) ^ 2) : scaledBesselProfile r k y ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (MaassKBessel.W_pos r (mul_pos hk hy) hthreshold).ne'

theorem scaledBesselProfile_energy_bound (r k y : ℝ) (hk : 0 < k)
    (hy : 1 ≤ y) (hky : 1 ≤ k * y) :
    ‖scaledBesselProfile r k y‖ ^ 2 / y ^ 2 ≤
      (k * Real.exp 2 * (MaassKBessel.moment 0 0 1) ^ 2) * Real.exp ((-2 * k) * y) := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  let M := MaassKBessel.moment 0 0 1
  have hM : 0 ≤ M := MaassKBessel.zero_moment_nonneg 0 1
  have hb : ‖MaassKBessel.K r (k * y)‖ ≤ Real.exp (1 - k * y) * M := by
    rw [← MaassKBessel.moment_zero]
    exact MaassKBessel.moment_norm_decay 0 r hky
  have hsq : ‖MaassKBessel.K r (k * y)‖ ^ 2 ≤ (Real.exp (1 - k * y) * M) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hM)).mpr hb
  have hn : ‖scaledBesselProfile r k y‖ ^ 2 =
      (k * y) * ‖MaassKBessel.K r (k * y)‖ ^ 2 := by
    simp only [scaledBesselProfile, Complex.norm_real, MaassKBessel.W, MaassSqrtRescaling.W,
      norm_mul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (mul_pos hk hy0).le]
  have hex : (Real.exp (1 - k * y)) ^ 2 = Real.exp 2 * Real.exp ((-2 * k) * y) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = k * ‖MaassKBessel.K r (k * y)‖ ^ 2 / y := by rw [hn]; field_simp
    _ ≤ k * ‖MaassKBessel.K r (k * y)‖ ^ 2 := div_le_self (mul_nonneg hk.le (sq_nonneg _)) hy
    _ ≤ k * (Real.exp (1 - k * y) * M) ^ 2 := mul_le_mul_of_nonneg_left hsq hk.le
    _ = _ := by rw [mul_pow, hex]; ring

theorem scaledBesselProfile_hyperbolic_integrable (r k a : ℝ) (hk : 0 < k)
    (ha : 1 ≤ a) (hka : 1 ≤ k * a) :
    IntegrableOn (fun y => ‖scaledBesselProfile r k y‖ ^ 2 / y ^ 2) (Ioi a) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hc : ContinuousOn (fun y => ‖scaledBesselProfile r k y‖ ^ 2 / y ^ 2) (Ioi a) :=
    (((scaledBesselProfile_continuousOn r k hk).mono (fun _ hy => ha0.trans hy)).norm.pow 2).div
      (continuousOn_id.pow 2) (fun y hy => pow_ne_zero 2 (ha0.trans hy).ne')
  apply ((integrableOn_exp_mul_Ioi (show -2 * k < 0 by nlinarith) a).const_mul
    (k * Real.exp 2 * (MaassKBessel.moment 0 0 1) ^ 2)).mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg y))]
  exact scaledBesselProfile_energy_bound r k y hk (ha.trans hy.le)
    (hka.trans (mul_le_mul_of_nonneg_left hy.le hk.le))

/-- Finite hyperbolic energy selects the actual decaying Bessel branch
among all classical solutions. The equality extends from a positive-
potential tail to every positive height by Cauchy uniqueness. -/
theorem bessel_multiple_of_ode_energy (r k : ℝ) (hk : 0 < k) (F V : ℝ → ℂ)
    (hF : ∀ y, 0 < y → HasDerivAt F (V y) y)
    (hV : ∀ y, 0 < y → HasDerivAt V (scaledBesselPotential r k y • F y) y)
    (hi : IntegrableOn (fun y => ‖F y‖ ^ 2 / y ^ 2) (Ioi 2)) :
    ∃ C : ℂ, ∀ y, 0 < y → F y = C * scaledBesselProfile r k y := by
  let a := max 2 ((|r| + 1) / k)
  have ha2 : 2 ≤ a := le_max_left _ _
  have ha : 0 < a := lt_of_lt_of_le (by norm_num) ha2
  have hka : |r| + 1 ≤ k * a := by
    have h := (div_le_iff₀ hk).mp (le_max_right 2 ((|r| + 1) / k))
    simpa only [mul_comm] using h
  have hthreshold (y : ℝ) (hy : a ≤ y) : r ^ 2 + 1 / 4 ≤ (k * y) ^ 2 := by
    have hky := hka.trans (mul_le_mul_of_nonneg_left hy hk.le)
    have hs := (sq_le_sq₀ (show 0 ≤ |r| + 1 by positivity)
      (mul_pos hk (ha.trans_le hy)).le).mpr hky
    nlinarith [sq_abs r, abs_nonneg r]
  have hq (y : ℝ) (hy : a ≤ y) : 0 ≤ scaledBesselPotential r k y := by
    have hd : (r ^ 2 + 1 / 4) / y ^ 2 ≤ k ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos (ha.trans_le hy))).mpr (by nlinarith [hthreshold y hy])
    exact sub_nonneg.mpr hd
  have hB0 := scaledBesselProfile_ne_zero r k a hk ha (hthreshold a le_rfl)
  let C : ℂ := F a / scaledBesselProfile r k a
  let G : ℝ → ℂ := fun y => C * scaledBesselProfile r k y
  let W : ℝ → ℂ := fun y => C * scaledBesselVelocity r k y
  have hG (y : ℝ) (hy : 0 < y) : HasDerivAt G (W y) y :=
    (scaledBesselProfile_hasDerivAt r k hk y hy).const_mul C
  have hW (y : ℝ) (hy : 0 < y) :
      HasDerivAt W (scaledBesselPotential r k y • G y) y := by
    have h := (scaledBesselVelocity_hasDerivAt r k hk y hy).const_mul C
    simpa only [G, W, Complex.real_smul, mul_left_comm C] using h
  have hiB := scaledBesselProfile_hyperbolic_integrable r k a hk (by linarith)
    (le_trans (by nlinarith [abs_nonneg r]) hka)
  have hiG : IntegrableOn (fun y => ‖G y‖ ^ 2 / y ^ 2) (Ioi a) := by
    apply (hiB.const_mul (‖C‖ ^ 2)).congr
    exact Eventually.of_forall (fun y => by simp only [G, norm_mul, mul_pow]; ring)
  have he : ∀ y ∈ Ici a, F y = G y :=
    ode_unique_of_hyperbolic_integrable a ha F V G W (scaledBesselPotential r k)
      (fun y hy => hF y (ha.trans_le hy)) (fun y hy => hV y (ha.trans_le hy))
      (fun y hy => hG y (ha.trans_le hy)) (fun y hy => hW y (ha.trans_le hy)) hq
      (by exact (div_mul_cancel₀ (F a) hB0).symm)
      (hi.mono_set (fun y hy => ha2.trans_lt hy)) hiG
  exact ⟨C, positive_ode_unique_of_tail F V G W (scaledBesselPotential r k)
    (scaledBesselPotential_continuousOn r k) hF hV hG hW a ha he⟩

/-- The first literal Fourier profile of an actual principal Friedrichs
eigenvector is a scalar multiple of the actual decaying Bessel integral.
All differential regularity and finite-energy inputs are proved internally. -/
theorem actual_first_bessel_profile (N : ℕ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (r : ℝ)
    (heigen : FriedrichsGraph N (AutomorphicL2.denseEmbedding _ _ f)
      (((1 / 4 + r ^ 2 : ℝ) : ℂ) • AutomorphicL2.denseEmbedding _ _ f)) :
    ∃ C : ℂ, ∀ y, 0 < y →
      cartesianFourier f.val 1 y = C * scaledBesselProfile r (2 * Real.pi) y := by
  obtain ⟨V, _hVc, hV⟩ := friedrichs_fourier_classical N f hf _ heigen 1
  have hpot (y : ℝ) : fourierHeightPotential 1 (((1 / 4 + r ^ 2 : ℝ) : ℂ)) y =
      (scaledBesselPotential r (2 * Real.pi) y : ℂ) := by
    simp only [fourierHeightPotential, scaledBesselPotential, Int.cast_one, mul_one,
      Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_pow,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  apply bessel_multiple_of_ode_energy r (2 * Real.pi) (by positivity) _ V
    (fun y hy => (hV y hy).1)
  · intro y hy
    have h := (hV y hy).2
    rw [hpot] at h
    simpa only [Complex.real_smul] using h
  · exact cartesianFourier_hyperbolic_integrable N f hf 1 2 le_rfl

#print axioms scaledBesselProfile_hasDerivAt
#print axioms scaledBesselVelocity_hasDerivAt
#print axioms scaledBesselProfile_continuousOn
#print axioms scaledBesselPotential_continuousOn
#print axioms scaledBesselProfile_ne_zero
#print axioms scaledBesselProfile_energy_bound
#print axioms scaledBesselProfile_hyperbolic_integrable
#print axioms bessel_multiple_of_ode_energy
#print axioms actual_first_bessel_profile

end QuantitativeNinaMaass
