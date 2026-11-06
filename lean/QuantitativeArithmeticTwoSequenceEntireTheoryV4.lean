module

public import FinitenessAllLevelMellinPairV1
public import QuantitativeArithmeticMellinStripBoundV1
public import QuantitativeArithmeticTwoSequenceTaylorTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticTwoSequenceEntire. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticTwoSequenceEntireV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTwoSequenceEntire
open Complex Filter Asymptotics Set MeasureTheory
open FinitenessPolynomialSeries FinitenessFourierConstruction FinitenessAllLevelAxisDecay

def scaledAxis (a : ℕ → ℂ) (c t : ℝ) : ℂ := fourier a (((c*t:ℝ):ℂ)*I)

theorem scaled_continuous {a : ℕ → ℂ} (ha : PolynomialBound a) {c : ℝ} (hc : 0<c) :
    ContinuousOn (scaledAxis a c) (Ioi 0) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  exact (FinitenessFourierConstruction.holomorphic ha
    (by simpa only [mul_I_im,ofReal_re] using mul_pos hc ht)).continuousAt.comp
      (by fun_prop)

theorem scaled_rapid {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    {c : ℝ} (hc : 0<c) (r : ℝ) :
    scaledAxis a c=O[atTop] (fun t : ℝ => t^r) := by
  obtain ⟨C,_,hb⟩ := fourier_exponential ha ha0 hc
  have ho : scaledAxis a c=O[atTop] (fun t : ℝ => Real.exp (-(2*Real.pi*c)*t)) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop 1] with t ht
    have hh := hb (((c*t:ℝ):ℂ)*I) (by
      simpa only [mul_I_im,ofReal_re] using (le_mul_of_one_le_right hc.le ht))
    have he : -2*Real.pi*(c*t)= -(2*Real.pi*c)*t := by ring
    simpa only [scaledAxis,mul_I_im,ofReal_re,he,Real.norm_eq_abs,Real.abs_exp] using hh
  exact ho.trans (isLittleO_exp_neg_mul_rpow_atTop (by positivity : 0<2*Real.pi*c) r).isBigO

theorem reflected_axis {L t : ℝ} (hL : 0<L) (ht : 0<t) :
    -1/((L:ℂ)*(((1/t:ℝ):ℂ)*I))=(((1/L*t:ℝ):ℂ)*I) := by
  have hLc : (L:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have htc : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
  push_cast
  field_simp
  simp [I_sq]

theorem inverse_axis_scalar (k : ℕ) (χ : ℂ) {t : ℝ} (ht : 0<t) :
    χ/((((1/t:ℝ):ℂ)*I)^k)=χ/I^k*(t:ℂ)^k := by
  have htc : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
  push_cast
  rw [mul_pow,one_div,inv_pow]
  field_simp

def pair {a b : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (hb : PolynomialBound b) (hb0 : b 0=0) {L : ℝ} (hL : 0<L)
    (k : ℕ) (hk : 0<k) (χ : ℂ) (hχ : χ≠0)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=χ/z^k*fourier b (-1/((L:ℂ)*z))) :
    WeakFEPair ℂ where
  f := scaledAxis a 1
  g := scaledAxis b (1/L)
  k := k
  ε := χ/I^k
  f₀ := 0
  g₀ := 0
  hf_int := (scaled_continuous ha (by norm_num : (0:ℝ)<1)).locallyIntegrableOn measurableSet_Ioi
  hg_int := (scaled_continuous hb (one_div_pos.mpr hL)).locallyIntegrableOn measurableSet_Ioi
  hk := by exact_mod_cast hk
  hε := div_ne_zero hχ (pow_ne_zero _ I_ne_zero)
  h_feq := by
    intro t ht
    have hh := hF (((1/t:ℝ):ℂ)*I) (by
      simpa only [mul_I_im,ofReal_re] using one_div_pos.mpr ht)
    rw [reflected_axis hL ht,inverse_axis_scalar k χ ht] at hh
    simpa only [scaledAxis,one_mul,Real.rpow_natCast,Complex.ofReal_pow,smul_eq_mul,
      mul_assoc] using hh
  hf_top := by intro r; simpa only [sub_zero] using scaled_rapid ha ha0 (by norm_num : (0:ℝ)<1) r
  hg_top := by intro r; simpa only [sub_zero] using scaled_rapid hb hb0 (one_div_pos.mpr hL) r

/-- A two-sequence Fricke law gives an entire Mellin transform on the
unshifted ray; no continuation of either Dirichlet series is assumed. -/
theorem mellin_entire {a b : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (hb : PolynomialBound b) (hb0 : b 0=0) {L : ℝ} (hL : 0<L)
    (k : ℕ) (hk : 0<k) (χ : ℂ) (hχ : χ≠0)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=χ/z^k*fourier b (-1/((L:ℂ)*z))) :
    Differentiable ℂ (mellin (fun t : ℝ => fourier a ((t:ℂ)*I))) := by
  let P := pair ha ha0 hb hb0 hL k hk χ hχ hF
  have hP : IsStrongFEPair P := ⟨rfl,rfl⟩
  have he : P.Λ=mellin (fun t : ℝ => fourier a ((t:ℂ)*I)) := by
    funext s
    have hh := (hP.hasMellin s).2.symm
    change P.Λ s=mellin (scaledAxis a 1) s at hh
    have heq : scaledAxis a 1=(fun t : ℝ => fourier a ((t:ℂ)*I)) := by
      funext t
      simp only [scaledAxis,one_mul]
    rwa [heq] at hh
  rw [← he]
  exact hP.differentiable_Λ

#print axioms scaled_continuous
#print axioms scaled_rapid
#print axioms reflected_axis
#print axioms inverse_axis_scalar
#print axioms mellin_entire
end QuantitativeArithmeticTwoSequenceEntire
end
end

/-! ## QuantitativeArithmeticTwoSequenceMellinConvergentV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticTwoSequenceEntire
open Complex Set MeasureTheory
open FinitenessPolynomialSeries FinitenessFourierConstruction

theorem mellin_convergent {a b : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (hb : PolynomialBound b) (hb0 : b 0=0) {L : ℝ} (hL : 0<L)
    (k : ℕ) (hk : 0<k) (χ : ℂ) (hχ : χ≠0)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=χ/z^k*fourier b (-1/((L:ℂ)*z)))
    (s : ℂ) : MellinConvergent (fun t : ℝ => fourier a ((t:ℂ)*I)) s := by
  let P := pair ha ha0 hb hb0 hL k hk χ hχ hF
  have hP : IsStrongFEPair P := ⟨rfl,rfl⟩
  have hh := (hP.hasMellin s).1
  change MellinConvergent (scaledAxis a 1) s at hh
  have heq : scaledAxis a 1=(fun t : ℝ => fourier a ((t:ℂ)*I)) := by
    funext t
    simp only [scaledAxis,one_mul]
  rwa [heq] at hh

theorem mellin_bounded_strips {a b : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (hb : PolynomialBound b) (hb0 : b 0=0) {L : ℝ} (hL : 0<L)
    (k : ℕ) (hk : 0<k) (χ : ℂ) (hχ : χ≠0)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=χ/z^k*fourier b (-1/((L:ℂ)*z)))
    (l u : ℝ) : ∃ C : ℝ,0≤C ∧ ∀ s : ℂ,l≤s.re → s.re≤u →
      ‖mellin (fun t : ℝ => fourier a ((t:ℂ)*I)) s‖≤C :=
  QuantitativeArithmeticMellinStrip.bounded_strip _ l u
    (mellin_convergent ha ha0 hb hb0 hL k hk χ hχ hF l)
    (mellin_convergent ha ha0 hb hb0 hL k hk χ hχ hF u)
#print axioms mellin_convergent
#print axioms mellin_bounded_strips
end QuantitativeArithmeticTwoSequenceEntire
end
end
