module

public import QuantitativeArithmeticSmallLevelThirtyFiveIntegerWordsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Matrix Complex

def integerDen (w : Word) (t : ℤ) : ℤ :=
  integerRaw w 1 0*t+integerRaw w 1 1*210

def integerNumer (w : Word) (t : ℤ) : ℤ :=
  integerRaw w 0 0*t+integerRaw w 0 1*210

def rationalRate (w : Word) (t : ℤ) : ℚ :=
  (integerDen w t : ℚ)^2/((integerRaw w).det*210^2)

def rationalDerivative (w : Word) (t : ℤ) : ℚ :=
  (integerRaw w 1 0 : ℚ)*integerDen w t/((integerRaw w).det*210)

theorem raw_det_integer (w : Word) : (raw w).det=((integerRaw w).det : ℝ) := by
  rw [raw_integer]
  simp [Matrix.det_fin_two,Matrix.map_apply]

theorem integer_det_pos (w : Word) : 0<(integerRaw w).det := by
  have hp := raw_det_pos w
  rw [raw_det_integer] at hp
  exact_mod_cast hp

theorem raw_den_integer (w : Word) (t : ℤ) :
    rawDen w t=(integerDen w t : ℝ)/210 := by
  simp only [rawDen,rawC,rawD,raw_integer,Matrix.map_apply,Int.coe_castRingHom,
    integerDen,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
  ring

theorem raw_numer_integer (w : Word) (t : ℤ) :
    rawA w*((t:ℝ)/210)+rawB w=(integerNumer w t : ℝ)/210 := by
  simp only [rawA,rawB,raw_integer,Matrix.map_apply,Int.coe_castRingHom,
    integerNumer,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
  ring

theorem word_C_integer (w : Word) : coordC w≠0 ↔ integerRaw w 1 0≠0 := by
  rw [raw_C_ne_zero]
  simp [rawC,raw_integer,Matrix.map_apply]

theorem word_den_integer (w : Word) (t : ℤ) :
    wordDen w t≠0 ↔ integerDen w t≠0 := by
  rw [raw_den_ne_zero,raw_den_integer]
  simp

/-- Closing a row on the grid is an integer identity. It does not require
numerical comparison of the normalized real matrices. -/
theorem word_partner_integer (w : Word) (t u : ℤ)
    (ht : integerDen w t≠0) (hu : 210*integerNumer w t=u*integerDen w t) :
    (coordA w*((t:ℝ)/210)+coordB w)/wordDen w t=(u:ℝ)/210 := by
  rw [raw_partner,raw_numer_integer,raw_den_integer]
  have htR : (integerDen w t : ℝ)≠0 := by exact_mod_cast ht
  have huR : (210:ℝ)*(integerNumer w t : ℝ)=(u:ℝ)*(integerDen w t : ℝ) := by
    exact_mod_cast hu
  field_simp
  nlinarith

theorem word_rate_rational (w : Word) (t : ℤ) :
    (wordDen w t)^2=(rationalRate w t : ℝ) := by
  rw [raw_rate,raw_den_integer,raw_det_integer]
  simp only [rationalRate,Rat.cast_div,Rat.cast_pow,Rat.cast_mul,Rat.cast_intCast,
    Rat.cast_ofNat]
  ring

theorem word_derivative_rational (w : Word) (t : ℤ) :
    coordC w*wordDen w t=(rationalDerivative w t : ℝ) := by
  rw [raw_derivative_rate,raw_den_integer,raw_det_integer]
  simp only [rawC,raw_integer,Matrix.map_apply,Int.coe_castRingHom,
    rationalDerivative,Rat.cast_div,Rat.cast_mul,Rat.cast_intCast,Rat.cast_ofNat]
  ring

/-- Exact equality for the complete Taylor coefficient, not just its leading
term. All matrix-dependent data on the right are rational or integral. -/
theorem wordCoefficient_rational (m : ℕ) (χ : ℂ) (w : Word) (t : ℤ)
    (n : ℕ) (s : ℂ) :
    wordCoefficient m χ w t n s=
      χ^(frickeCount w)*(rationalRate w t : ℂ)^(s-(m:ℂ))*
        (I*(rationalDerivative w t : ℂ))^n*
          Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  rw [wordCoefficient,character_count,word_rate_rational,word_derivative_rational]
  simp only [Complex.ofReal_ratCast]

#print axioms integer_det_pos
#print axioms word_partner_integer
#print axioms wordCoefficient_rational
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
