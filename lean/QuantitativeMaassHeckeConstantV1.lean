module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Tactic

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped Interval BigOperators

namespace QuantitativeMaass

/-- The literal zero Fourier coefficient on the unit translation cylinder. -/
noncomputable def zeroFourier (F : ℝ → ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1, F x y

/-- The usual normalized unramified Hecke formula in Cartesian coordinates.
The constant-term calculation below only needs a positive integer p. -/
noncomputable def normalizedHecke (p : ℕ) (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  (Real.sqrt (p : ℝ))⁻¹ •
    (F ((p : ℝ) * x) ((p : ℝ) * y) +
      ∑ a ∈ Finset.range p, F ((x + (a : ℝ)) / p) (y / p))

theorem periodic_dilate_average (f : ℝ → ℂ) (hf : Continuous f)
    (hperiod : Function.Periodic f 1) (p : ℕ) (hp : 0 < p) :
    (∫ x in (0 : ℝ)..1, f ((p : ℝ) * x)) = ∫ x in (0 : ℝ)..1, f x := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hperiodIntegral : (∫ x in (0 : ℝ)..(p : ℝ), f x) =
      (p : ℝ) • ∫ x in (0 : ℝ)..1, f x := by
    simpa using hperiod.intervalIntegral_add_zsmul_eq (p : ℤ) 0
      (fun a b => hf.intervalIntegrable a b)
  rw [intervalIntegral.integral_comp_mul_left f hp0]
  simp only [mul_zero, mul_one, hperiodIntegral, smul_smul, inv_mul_cancel₀ hp0, one_smul]

theorem sum_affine_branch_integrals (f : ℝ → ℂ) (hf : Continuous f)
    (p : ℕ) (hp : 0 < p) :
    (∑ a ∈ Finset.range p, ∫ x in (0 : ℝ)..1, f ((x + (a : ℝ)) / p)) =
      (p : ℝ) • ∫ x in (0 : ℝ)..1, f x := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hbranch (a : ℕ) : (∫ x in (0 : ℝ)..1, f ((x + (a : ℝ)) / p)) =
      (p : ℝ) • ∫ x in (a : ℝ) / p..((a : ℝ) + 1) / p, f x := by
    simpa only [add_div, zero_div, zero_add, add_zero, add_comm] using
      intervalIntegral.integral_comp_div_add (a := 0) (b := 1) f hp0 ((a : ℝ) / p)
  simp_rw [hbranch]
  rw [← Finset.smul_sum]
  apply congrArg (fun z : ℂ => (p : ℝ) • z)
  have hh := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := fun a : ℕ => (a : ℝ) / p) (n := p)
    (fun _ _ => hf.intervalIntegrable _ _)
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, div_self hp0] using hh

/-- Exact Hecke action on the zero channel: the p lower branches combine
into one full-period integral, including the required factor p. -/
theorem normalizedHecke_zeroFourier (F : ℝ → ℝ → ℂ)
    (hF : ∀ y, Continuous (fun x => F x y))
    (hperiod : ∀ y, Function.Periodic (fun x => F x y) 1)
    (p : ℕ) (hp : 0 < p) (y : ℝ) :
    zeroFourier (normalizedHecke p F) y =
      (Real.sqrt (p : ℝ))⁻¹ • zeroFourier F ((p : ℝ) * y) +
      Real.sqrt (p : ℝ) • zeroFourier F (y / p) := by
  have hpos : 0 < (p : ℝ) := by exact_mod_cast hp
  have hroot : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hsqrt : (Real.sqrt (p : ℝ))⁻¹ * (p : ℝ) = Real.sqrt (p : ℝ) := by
    have hs := Real.sq_sqrt hpos.le
    field_simp
    nlinarith
  have hcontinuous (a : ℕ) : Continuous (fun x : ℝ => F ((x + (a : ℝ)) / p) (y / p)) :=
    (hF _).comp ((continuous_id.add continuous_const).div_const _)
  have hu : Continuous (fun x : ℝ => F ((p : ℝ) * x) ((p : ℝ) * y)) :=
    (hF _).comp (continuous_const.mul continuous_id)
  unfold zeroFourier normalizedHecke
  rw [intervalIntegral.integral_smul,
    intervalIntegral.integral_add (hu.intervalIntegrable _ _)
      ((continuous_finsetSum _ (fun a _ => hcontinuous a)).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun a _ => (hcontinuous a).intervalIntegrable _ _),
    periodic_dilate_average _ (hF _) (hperiod _) p hp,
    sum_affine_branch_integrals _ (hF _) p hp,
    smul_add, smul_smul, hsqrt]

/-- Conjugation by the square-root height factor removes the asymmetric
Hecke coefficients. This is the precise zero-channel shift formula. -/
theorem normalizedHecke_halfDensity (F : ℝ → ℝ → ℂ) (a : ℝ → ℂ)
    (hF : ∀ y, Continuous (fun x => F x y))
    (hperiod : ∀ y, Function.Periodic (fun x => F x y) 1)
    (hshape : ∀ y, 0 < y → zeroFourier F y = Real.sqrt y • a (Real.log y))
    (p : ℕ) (hp : 0 < p) (y : ℝ) (hy : 0 < y) :
    zeroFourier (normalizedHecke p F) y = Real.sqrt y •
      (a (Real.log y + Real.log (p : ℝ)) + a (Real.log y - Real.log (p : ℝ))) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hroot : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.2 hpR).ne'
  have hleft : (Real.sqrt (p : ℝ))⁻¹ * (Real.sqrt (p : ℝ) * Real.sqrt y) =
      Real.sqrt y := by field_simp
  have hright : Real.sqrt (p : ℝ) * (Real.sqrt y / Real.sqrt (p : ℝ)) =
      Real.sqrt y := by field_simp
  rw [normalizedHecke_zeroFourier F hF hperiod p hp y,
    hshape _ (mul_pos hpR hy), hshape _ (div_pos hy hpR),
    Real.sqrt_mul hpR.le, Real.sqrt_div hy.le,
    Real.log_mul hpR.ne' hy.ne', Real.log_div hy.ne' hpR.ne',
    smul_smul, smul_smul, hleft, hright, ← smul_add]
  rw [add_comm (Real.log (p : ℝ)) (Real.log y)]

/-- On the zero-channel plane waves, the symmetric translation operator
has exactly the cosine multiplier appearing in the LV cuspidalizer. -/
theorem symmetric_shift_exponential (r u t : ℝ) :
    Complex.exp (((r * (u + t) : ℝ) : ℂ) * Complex.I) +
      Complex.exp (((r * (u - t) : ℝ) : ℂ) * Complex.I) =
      (2 * Complex.cos ((r * t : ℝ) : ℂ)) *
        Complex.exp (((r * u : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.two_cos]
  have hplus : (((r * (u + t) : ℝ) : ℂ) * Complex.I) =
      (((r * t : ℝ) : ℂ) * Complex.I) + (((r * u : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  have hminus : (((r * (u - t) : ℝ) : ℂ) * Complex.I) =
      (-((r * t : ℝ) : ℂ) * Complex.I) + (((r * u : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hplus, hminus, Complex.exp_add, Complex.exp_add, add_mul]

#print axioms periodic_dilate_average
#print axioms sum_affine_branch_integrals
#print axioms normalizedHecke_zeroFourier
#print axioms normalizedHecke_halfDensity
#print axioms symmetric_shift_exponential

end QuantitativeMaass
