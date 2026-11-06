module

public import AsymptoticClassicalHeckeDegeneracyV1
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Algebra.Field.GeomSum

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalDiscriminant
open scoped ModularForm

/-- The finite Fourier projection onto exponents divisible by p. -/
theorem root_filter (p : ℕ) (hp : 0 < p) (n : ℕ) :
    (∑ a : Fin p, (Complex.exp (2 * Real.pi * Complex.I / p) ^ n) ^ a.val) =
      if p ∣ n then (p : ℂ) else 0 := by
  classical
  let ζ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hζ := Complex.isPrimitiveRoot_exp p hp.ne'
  change (∑ a : Fin p, (ζ ^ n) ^ a.val) = _
  by_cases hn : p ∣ n
  · have he : ζ ^ n = 1 := hζ.pow_eq_one_iff_dvd n |>.mpr hn
    simp [hn, he]
  · have he : ζ ^ n ≠ 1 := mt (hζ.pow_eq_one_iff_dvd n).mp hn
    simp only [hn, ite_false]
    rw [Fin.sum_univ_eq_sum_range, geom_sum_eq he]
    have hh : (ζ ^ n) ^ p = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [hh, sub_self, zero_div]

/-- The Fourier parameter of a standard upper-triangular Hecke branch. -/
theorem qParam_hecke_branch (p : ℕ) (hp : 0 < p) (a : ℕ) (z : ℍ) :
    Function.Periodic.qParam 1
      (affine (1 / p) (by positivity) ((a : ℝ) / p) z) =
      Function.Periodic.qParam p z * Complex.exp (2 * Real.pi * Complex.I / p) ^ a := by
  simp only [affine, Function.Periodic.qParam, Complex.ofReal_one, div_one,
    Complex.ofReal_div, Complex.ofReal_natCast]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

/-- The p-th power of the width-p Fourier parameter has width one. -/
theorem qParam_width_pow (p : ℕ) (hp : 0 < p) (z : ℍ) :
    Function.Periodic.qParam p z ^ p = Function.Periodic.qParam 1 z := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [Function.Periodic.qParam, Complex.ofReal_natCast, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp

#print axioms root_filter
#print axioms qParam_hecke_branch
#print axioms qParam_width_pow

end AsymptoticClassicalCusp
