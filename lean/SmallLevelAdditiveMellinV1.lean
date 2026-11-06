module

public import SmallLevelAdditiveCoefficientsV1
public import FinitenessEulerIdentificationV1
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelAdditive

open Complex Filter Asymptotics Set MeasureTheory FinitenessPolynomialSeries
open FinitenessFourierConstruction FinitenessAllLevelMellinDirichlet

/-- The classical completed additive Dirichlet series, centered at k/2 once
`a` is the original sequence of classical Fourier coefficients. -/
def transform (a : ℕ → ℂ) (r : ℝ) (s : ℂ) : ℂ :=
  Complex.Gamma s*((2*Real.pi:ℝ):ℂ)^(-s)*LSeries (coefficients a r) s

theorem abscissa_bound {a : ℕ → ℂ} {d : ℕ}
    (ha : a=O[atTop] (fun n : ℕ => (n:ℝ)^(d:ℝ))) (r : ℝ) :
    LSeries.abscissaOfAbsConv (coefficients a r)≤(d:ℝ)+1 :=
  LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (coefficients_growth ha r)

theorem summable_at {a : ℕ → ℂ} {d : ℕ}
    (ha : a=O[atTop] (fun n : ℕ => (n:ℝ)^(d:ℝ))) (r : ℝ)
    {s : ℂ} (hs : (d:ℝ)+1<s.re) : LSeriesSummable (coefficients a r) s := by
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  exact (abscissa_bound ha r).trans_lt (by exact_mod_cast hs)

theorem transform_analytic {a : ℕ → ℂ} {d : ℕ}
    (ha : a=O[atTop] (fun n : ℕ => (n:ℝ)^(d:ℝ))) (r : ℝ)
    {s : ℂ} (hs : (d:ℝ)+1<s.re) : AnalyticAt ℂ (transform a r) s := by
  have hd : DifferentiableOn ℂ (transform a r) {z : ℂ | (d:ℝ)+1<z.re} := by
    intro z hz
    change (d:ℝ)+1<z.re at hz
    have hz0 : 0<z.re := by linarith [Nat.cast_nonneg (α:=ℝ) d]
    have hg : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z (by
      intro m hm
      have hh := congrArg Complex.re hm
      simp only [Complex.neg_re,Complex.natCast_re] at hh
      linarith [Nat.cast_nonneg (α:=ℝ) m])
    have hp : DifferentiableAt ℂ (fun w : ℂ => ((2*Real.pi:ℝ):ℂ)^(-w)) z := by
      simp_rw [Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr (by positivity : (2*Real.pi:ℝ)≠0))]
      fun_prop
    have hL := (LSeries_analyticOnNhd (coefficients a r) z
      ((abscissa_bound ha r).trans_lt (by exact_mod_cast hz))).differentiableAt
    exact ((hg.mul hp).mul hL).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re) s hs

theorem transform_eq_series {a : ℕ → ℂ} (ha0 : a 0=0) {d : ℕ}
    (ha : a=O[atTop] (fun n : ℕ => (n:ℝ)^(d:ℝ))) (r : ℝ)
    {s : ℂ} (hs : (d:ℝ)+1<s.re) :
    transform a r s=Complex.Gamma s*((2*Real.pi:ℝ):ℂ)^(-s)*
      ∑' n : ℕ, a (n+1)*phase r (n+1)*((n+1:ℕ):ℂ)^(-s) := by
  rw [transform,← FinitenessEulerIdentification.L_eq_mathlib
    (coefficients_zero ha0 r) (summable_at ha r hs)]
  rfl

/-- The actual Mellin integral along the translated vertical ray agrees with
the completed additive Dirichlet series in its convergence half-plane. -/
theorem mellin_eq_transform {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    {d : ℕ} (hg : a=O[atTop] (fun n : ℕ => (n:ℝ)^(d:ℝ))) (r : ℝ)
    {s : ℂ} (hs : (d:ℝ)+1<s.re) :
    mellin (fun t : ℝ => fourier a ((r:ℂ)+(t:ℂ)*Complex.I)) s=transform a r s := by
  have hs0 : 0<s.re := by linarith [Nat.cast_nonneg (α:=ℝ) d]
  have hm := axis_mellin (by decide : 0<1) (coefficients_polynomial ha r)
    (coefficients_zero ha0 r) hs0 (summable_norm_div (coefficients_growth hg r) hs)
  change mellin (FinitenessAllLevelAxisDecay.axis 1 (coefficients a r)) s=
    Complex.Gamma s*(rate 1:ℂ)^(-s)*FinitenessOriginalInput.L (coefficients a r) s at hm
  rw [FinitenessEulerIdentification.L_eq_mathlib (coefficients_zero ha0 r)
    (summable_at hg r hs)] at hm
  rw [show FinitenessAllLevelAxisDecay.axis 1 (coefficients a r)=
    (fun t : ℝ => fourier a ((r:ℂ)+(t:ℂ)*Complex.I)) from funext (axis_one_translate a r)] at hm
  simpa only [rate,Nat.cast_one,Real.sqrt_one,div_one,transform] using hm

/-- One half-plane works for every real translate, hence for every finite
additive grid. Its bound depends only on the original coefficient growth. -/
theorem common_halfplane {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0) :
    ∃ B : ℝ, ∀ r : ℝ, ∀ s : ℂ, B<s.re →
      AnalyticAt ℂ (transform a r) s ∧
      mellin (fun t : ℝ => fourier a ((r:ℂ)+(t:ℂ)*Complex.I)) s=transform a r s := by
  obtain ⟨d,hd⟩ := polynomial_growth ha
  exact ⟨(d:ℝ)+1,fun r s hs => ⟨transform_analytic hd r hs,mellin_eq_transform ha ha0 hd r hs⟩⟩

def original (k : ℕ) (f : ℕ → ℂ) (r : ℝ) : ℂ → ℂ :=
  transform (FinitenessOriginalFourier.fullCoefficients f k) r

theorem original_common_halfplane {N k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) :
    ∃ B : ℝ, ∀ r : ℝ, ∀ s : ℂ, B<s.re →
      AnalyticAt ℂ (original k f r) s ∧
      mellin (fun t : ℝ => fourier (FinitenessOriginalFourier.fullCoefficients f k)
        ((r:ℂ)+(t:ℂ)*Complex.I)) s=original k f r s := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  exact common_halfplane (FinitenessOriginalFourier.polynomial_bound hf.zero hg k)
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero k)

#print axioms abscissa_bound
#print axioms transform_analytic
#print axioms transform_eq_series
#print axioms mellin_eq_transform
#print axioms common_halfplane
#print axioms original_common_halfplane

end SmallLevelAdditive
