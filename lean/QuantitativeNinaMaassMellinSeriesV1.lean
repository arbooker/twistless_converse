module

public import MaassOriginalAxisV1
public import AsymptoticClassicalMellinSplitV1
public import QuantitativeMaassEulerHeightDecayV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Complex Asymptotics
open scoped Topology

/-!
Forward Mellin summation and the general entire-continuation argument for
an exponentially decaying inversion datum. The actual automorphic Fricke
relation and decay estimates must be supplied by the physical wave; they
are not assumed in a claimed original Euler-solution theorem here.
-/

namespace QuantitativeNinaMaass

theorem mellin_dilated_term_norm (F : ℝ → ℂ) (s a : ℂ) (d : ℝ) (hd : 0 < d) :
    (∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * (a * F (d * t))‖) =
      ‖a * (d : ℂ) ^ (-s)‖ * (∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * F t‖) := by
  have hdC : (d : ℂ) ≠ 0 := ofReal_ne_zero.mpr hd.ne'
  have he (t : ℝ) (ht : 0 < t) :
      (t : ℂ) ^ (s - 1) * (a * F (d * t)) =
        (a * (d : ℂ) ^ (1 - s)) * (((d * t : ℝ) : ℂ) ^ (s - 1) * F (d * t)) := by
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hd.le ht.le,
      show 1 - s = -(s - 1) by ring, cpow_neg]
    have hp : (d : ℂ) ^ (s - 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hdC)
    field_simp
  have heN : EqOn (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) * (a * F (d * t))‖)
      (fun t : ℝ => ‖a * (d : ℂ) ^ (1 - s)‖ *
        ‖((d * t : ℝ) : ℂ) ^ (s - 1) * F (d * t)‖) (Ioi 0) := by
    intro t ht
    dsimp only
    rw [he t ht, norm_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi heN, integral_const_mul,
    integral_comp_mul_left_Ioi (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) * F t‖) 0 hd,
    mul_zero, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [show 1 - s = 1 + (-s) by ring, cpow_add _ _ hdC, cpow_one]
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd.le]
  field_simp

/-- Sum/integral exchange for an arbitrary Mellin-convergent kernel and
positive dilations. The required norm series is explicit and verified
for the manuscript's polynomially growing coefficients below. -/
theorem mellin_sum_dilations (F : ℝ → ℂ) (s : ℂ) (a : ℕ → ℂ) (d : ℕ → ℝ)
    (hd : ∀ n, 0 < d n) (hF : MellinConvergent F s)
    (ha : Summable (fun n => ‖a n * (d n : ℂ) ^ (-s)‖)) :
    mellin (fun t => ∑' n, a n * F (d n * t)) s =
      (∑' n, a n * (d n : ℂ) ^ (-s)) * mellin F s := by
  have hi (n : ℕ) : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (a n * F (d n * t))) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using
      ((MellinConvergent.comp_mul_left (hd n)).mpr hF).const_smul (a n)
  have hs : Summable (fun n => ∫ t in Ioi (0 : ℝ),
      ‖(t : ℂ) ^ (s - 1) * (a n * F (d n * t))‖) := by
    simp_rw [mellin_dilated_term_norm F s _ _ (hd _)]
    exact ha.mul_right _
  have ht (n : ℕ) : (∫ t in Ioi (0 : ℝ),
      (t : ℂ) ^ (s - 1) * (a n * F (d n * t))) =
      (a n * (d n : ℂ) ^ (-s)) * mellin F s := by
    change mellin (fun t => a n • F (d n * t)) s = _
    rw [mellin_const_smul, mellin_comp_mul_left F s (hd n), smul_eq_mul, smul_eq_mul]
    ring
  unfold mellin
  simp only [smul_eq_mul, ← tsum_mul_left]
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  simp_rw [ht]
  rw [tsum_mul_right]
  rfl

/-- The actual conductor-normalized Bessel datum, in positive Mellin height. -/
def parityMellinAxis (L : ℝ) (p : MaassSpectral.Parameter) (δ : ℕ)
    (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑' n, b (n + 1) * MaassMellin.parityKernel p δ
    (Real.exp (MaassOriginal.frequencies L n) * t)

theorem parityMellinAxis_log (L : ℝ) (p : MaassSpectral.Parameter) (δ : ℕ)
    (b : ℕ → ℂ) (t : ℝ) (ht : 0 < t) :
    parityMellinAxis L p δ b t = MaassOriginal.axisSum L p δ b (Real.log t) := by
  unfold parityMellinAxis MaassOriginal.axisSum
  apply tsum_congr
  intro n
  rw [Real.exp_add, Real.exp_log ht, mul_comm t]

theorem exp_dilation_cpow (x : ℝ) (s : ℂ) :
    (Real.exp x : ℂ) ^ (-s) = Complex.exp (((-x : ℝ) : ℂ) * s) := by
  rw [MaassMellin.cpow_pos _ (Real.exp_pos x), Real.log_exp]
  congr 1
  push_cast
  ring

/-- The forward Mellin transform is exactly the original completed
Dirichlet series, including the conductor and parity Gamma factors. -/
theorem parityMellinAxis_mellin {L : ℝ} (hL : 0 < L)
    (p : MaassSpectral.Parameter) (δ : ℕ) {b : ℕ → ℂ} {τ : ℝ}
    (hb : (fun n => ‖b n‖) =O[atTop] (fun n : ℕ => (n : ℝ) ^ τ))
    (s : ℂ) (hs : 1 < s.re) (hτ : τ + 1 < s.re) :
    mellin (parityMellinAxis L p δ b) s = MaassOriginal.completed L p δ b s := by
  have ha : Summable (fun n => ‖b (n + 1) *
      (Real.exp (MaassOriginal.frequencies L n) : ℂ) ^ (-s)‖) := by
    simp only [exp_dilation_cpow, norm_mul, Complex.norm_exp,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    simpa only [mul_comm (-s.re), neg_mul, mul_neg] using
      MaassOriginal.weighted_summable hb hτ L
  unfold parityMellinAxis
  rw [mellin_sum_dilations _ _ _ _ (fun _ => Real.exp_pos _)
    (MaassMellin.parity_mellin_convergent p δ hs) ha,
    MaassMellin.parity_mellin p δ hs, MaassOriginal.completed_series hL]
  simp only [exp_dilation_cpow, FinitenessMellinSeries.series]
  ring

/-- A direct inversion datum with exponential tails has an entire,
finite-order Mellin transform. This general analytic lemma is applied
only after the physical axis inversion and decay have been proved. -/
theorem mellin_entire_of_inversion (f : ℝ → ℂ)
    (hf : ContinuousOn f (Ioi 0)) (ε : ℂ) (hε : ε ≠ 0)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * Real.exp (-c * t))
    (hinv : ∀ t : ℝ, 0 < t → f (1 / t) = (ε * (t : ℂ)) * f t) :
    Differentiable ℂ (mellin f) ∧ FinitenessFiniteOrder.Bound (mellin f) ∧
      ∀ s : ℂ, mellin f s = ε * mellin f (1 - s) := by
  have hrapid (r : ℝ) : f =O[atTop] (fun t : ℝ => t ^ r) := by
    have ho : f =O[atTop] (fun t : ℝ => Real.exp (-c * t)) := by
      apply IsBigO.of_bound C
      filter_upwards [eventually_ge_atTop 1] with t ht
      simpa only [Real.norm_eq_abs, Real.abs_exp] using hdecay t ht
    exact ho.trans (isLittleO_exp_neg_mul_rpow_atTop hc r).isBigO
  let P : WeakFEPair ℂ :=
    { f := f
      g := f
      k := 1
      ε := ε
      f₀ := 0
      g₀ := 0
      hf_int := hf.locallyIntegrableOn measurableSet_Ioi
      hg_int := hf.locallyIntegrableOn measurableSet_Ioi
      hk := by norm_num
      hε := hε
      h_feq := by
        intro t ht
        simpa only [Real.rpow_one, smul_eq_mul] using hinv t ht
      hf_top := by intro r; simpa only [sub_zero] using hrapid r
      hg_top := by intro r; simpa only [sub_zero] using hrapid r }
  have hP : IsStrongFEPair P := ⟨rfl, rfl⟩
  have he : P.Λ = mellin f := funext (fun s => (hP.hasMellin s).2.symm)
  have he' : P.symm.Λ = mellin f := funext (fun s => (hP.symm.hasMellin s).2.symm)
  refine ⟨he ▸ hP.differentiable_Λ,
    he ▸ AsymptoticClassicalLSeries.strongPair_finiteOrder P hP hC hC hc hc hdecay hdecay, ?_⟩
  intro s
  have h := P.functional_equation (1 - s)
  rw [he, he'] at h
  simpa only [P, Complex.ofReal_one, sub_sub_cancel, smul_eq_mul] using h

open QuantitativeMaass

theorem parityMellinAxis_weighted (L r : ℝ) (δ : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    parityMellinAxis L (.principal r) δ b t =
      2 * ((Real.exp (-Real.log L / 2) * t : ℝ) : ℂ) ^ δ *
        principalWeightedSeries b r 0 δ 0 (0, Real.exp (-Real.log L / 2) * t) := by
  have hfreq (n : ℕ) : Real.exp (MaassOriginal.frequencies L n) =
      ((n + 1 : ℕ) : ℝ) * Real.exp (-Real.log L / 2) := by
    unfold MaassOriginal.frequencies
    rw [show Real.log (n + 1) - Real.log L / 2 =
      Real.log (n + 1) + (-Real.log L / 2) by ring, Real.exp_add,
      Real.exp_log (by positivity : (0 : ℝ) < n + 1)]
    norm_cast
  unfold parityMellinAxis principalWeightedSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [hfreq, MaassMellin.parityKernel, MaassSpectral.K, principalWeightedTerm,
    eulerParityPhase, mul_zero, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero,
    pow_zero, one_mul, MaassKBessel.moment_zero]
  simp only [mul_assoc, Complex.ofReal_mul, mul_pow]
  push_cast
  ring

theorem parityMellinAxis_continuousOn {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (L r : ℝ) (δ : ℕ) :
    ContinuousOn (parityMellinAxis L (.principal r) δ b) (Ioi 0) := by
  have he : parityMellinAxis L (.principal r) δ b = fun t =>
      2 * ((Real.exp (-Real.log L / 2) * t : ℝ) : ℂ) ^ δ *
        principalWeightedSeries b r 0 δ 0 (0, Real.exp (-Real.log L / 2) * t) :=
    funext (parityMellinAxis_weighted L r δ b)
  rw [he]
  apply ContinuousOn.mul
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      (2 : ℂ) * ((Real.exp (-Real.log L / 2) * t : ℝ) : ℂ) ^ δ)).continuousOn
  · exact (principalWeightedSeries_continuousOn hb r 0 δ 0).comp
      (by fun_prop : Continuous (fun t : ℝ => ((0 : ℝ), Real.exp (-Real.log L / 2) * t))).continuousOn
      (fun t ht => mul_pos (Real.exp_pos _) ht)

theorem parityMellinAxis_exponential {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (L r : ℝ) (δ : ℕ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ t : ℝ, 1 ≤ t →
      ‖parityMellinAxis L (.principal r) δ b t‖ ≤ C * Real.exp (-c * t) := by
  let a := Real.exp (-Real.log L / 2)
  have ha : 0 < a := Real.exp_pos _
  let M := ∑' n, principalMomentMajorant b 0 δ (2 * Real.pi) (a / 2) n
  have hM : 0 ≤ M := by
    apply tsum_nonneg
    intro n
    unfold principalMomentMajorant
    have hm := MaassKBessel.zero_moment_nonneg 0 ((2 * Real.pi) * (a / 2))
    positivity
  refine ⟨4 * M * Real.exp (2 * (δ : ℝ) ^ 2 / Real.pi), (Real.pi / 2) * a,
    by positivity, by positivity, ?_⟩
  intro t ht
  have hat : 0 < a * t := mul_pos ha (zero_lt_one.trans_le ht)
  have hay : a ≤ a * t := by nlinarith
  have hw := principalWeightedSeries_exponential_bound hb r 0 δ 0 a ha 0 (a * t) hay
  have hp := AsymptoticClassicalLSeries.rpow_exp_bound Real.pi_pos (Nat.cast_nonneg δ) hat
  rw [Real.rpow_natCast] at hp
  rw [parityMellinAxis_weighted]
  change ‖2 * (((a * t : ℝ) : ℂ) ^ δ) * principalWeightedSeries b r 0 δ 0 (0, a * t)‖ ≤ _
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hat.le]
  norm_num only [norm_ofNat]
  calc
    _ ≤ (2 * (a * t) ^ δ) * ((2 * Real.exp (-Real.pi * (a * t))) * M) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = (4 * M) * ((a * t) ^ δ * Real.exp (-Real.pi * (a * t))) := by ring
    _ ≤ (4 * M) * (Real.exp (2 * (δ : ℝ) ^ 2 / Real.pi) *
        Real.exp (-(Real.pi / 2) * (a * t))) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by
      rw [show -(Real.pi / 2) * (a * t) = -((Real.pi / 2) * a) * t by ring]
      ring

/-- Conditional intermediate: polynomial growth supplies every analytic
estimate, while the axis inversion remains an explicit physical obligation.
This is not a claim that arbitrary coefficient sequences satisfy that inversion. -/
theorem parityMellinAxis_continuation {L : ℝ} (hL : 0 < L)
    {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b) (r : ℝ) (δ : ℕ)
    (ε : ℂ) (hε : ε ≠ 0)
    (hinv : ∀ t : ℝ, 0 < t → parityMellinAxis L (.principal r) δ b (1 / t) =
      (ε * (t : ℂ)) * parityMellinAxis L (.principal r) δ b t) :
    MaassOriginal.Continuation L (.principal r) δ b ε := by
  obtain ⟨C, c, hC, hc, hdecay⟩ := parityMellinAxis_exponential hb L r δ
  obtain ⟨hhol, hfinite, hfe⟩ := mellin_entire_of_inversion _
    (parityMellinAxis_continuousOn hb L r δ) ε hε C c hC hc hdecay hinv
  refine ⟨mellin (parityMellinAxis L (.principal r) δ b), hhol,
    FinitenessInputBounds.bound_finiteOrder hfinite, ?_, hfe⟩
  obtain ⟨τ, hτ⟩ := hb
  refine ⟨max 1 (τ + 1), fun s hs => ?_⟩
  exact parityMellinAxis_mellin hL (.principal r) δ hτ s
    ((le_max_left _ _).trans_lt hs) ((le_max_right _ _).trans_lt hs)

#print axioms mellin_dilated_term_norm
#print axioms mellin_sum_dilations
#print axioms parityMellinAxis_log
#print axioms exp_dilation_cpow
#print axioms parityMellinAxis_mellin
#print axioms mellin_entire_of_inversion
#print axioms parityMellinAxis_weighted
#print axioms parityMellinAxis_continuousOn
#print axioms parityMellinAxis_exponential
#print axioms parityMellinAxis_continuation

end QuantitativeNinaMaass
