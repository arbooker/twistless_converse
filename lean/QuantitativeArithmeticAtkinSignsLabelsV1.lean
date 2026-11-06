module

public import AsymptoticClassicalHeckeNormalizerV1
public import AsymptoticClassicalLocalAtkinLowerV1
public import QuantitativeArithmeticCrossPrimeV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticAtkinSigns

open Matrix AsymptoticAtkinLehner AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticClassicalCusp AsymptoticRationalGroup AsymptoticFreshMatrices
open scoped MatrixGroups

/-- The existing local Atkin element in a convenient exact group factorization. -/
theorem localAtkin_eq_dilation_inv (M p : ℕ) (hM : 0<M) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) :
    localAtkin M p hM hp A B hAB=
      (dilationLabel p hp)⁻¹*integralLabel (heckeSL M p A B hAB) := by
  have he := congrArg Inv.inv (heckeNormalizerLabel_eq M p hp A B hAB hM)
  simpa only [heckeNormalizerLabel,_root_.mul_inv_rev,map_inv,inv_inv] using he.symm

/-- A literal determinant-p rational matrix for the local projective element. -/
def localRawGL (M p : ℕ) (hp : 0<p) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) : GL (Fin 2) ℚ :=
  rationalGL (traceSL M p A B hAB 0)*dilationGL p hp

theorem localRawGL_val (M p : ℕ) (hp : 0<p) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) :
    (localRawGL M p hp A B hAB).val=!![(p:ℚ),(B:ℚ);-(p:ℚ)*M,(p:ℚ)*A] := by
  change (traceSL M p A B hAB 0).val.map (fun z:ℤ => (z:ℚ))*(dilationGL p hp).val=_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceSL,dilationGL,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring

theorem localAtkin_eq_trace_dilation (M p : ℕ) (hM : 0<M) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) :
    localAtkin M p hM hp A B hAB=
      integralLabel (traceSL M p A B hAB 0)*dilationLabel p hp := by
  rw [localAtkin_eq_dilation_inv]
  apply (mul_left_cancel (a:=dilationLabel p hp))
  simp only [mul_inv_cancel_left]
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (rationalGL (heckeSL M p A B hAB))=
    rationalMap (dilationGL p hp)*(rationalMap (rationalGL (traceSL M p A B hAB 0))*rationalMap (dilationGL p hp))
  rw [← map_mul,← map_mul]
  have he : dilationGL p hp*localRawGL M p hp A B hAB=
      rationalGL (heckeSL M p A B hAB)*GeneralLinearGroup.scalar (Fin 2)
        (Units.mk0 (p:ℚ) (by exact_mod_cast hp.ne')) := by
    apply Units.ext
    change (dilationGL p hp).val*(localRawGL M p hp A B hAB).val=
      (heckeSL M p A B hAB).val.map (fun z:ℤ => (z:ℚ))*_
    rw [localRawGL_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dilationGL,heckeSL,GeneralLinearGroup.mkOfDetNeZero,GeneralLinearGroup.scalar,
        Matrix.scalar,Matrix.natCast_apply,Matrix.mul_apply,Fin.sum_univ_two]
    all_goals ring
  change rationalMap (rationalGL (heckeSL M p A B hAB))=rationalMap (dilationGL p hp*localRawGL M p hp A B hAB)
  rw [he,map_mul,rationalMap_scalar,mul_one]

/-- Ready-to-use projective matrix identity for independent arithmetic calculations. -/
theorem localAtkin_rationalMap (M p : ℕ) (hM : 0<M) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) :
    (localAtkin M p hM hp A B hAB).val.val=rationalMap (localRawGL M p hp A B hAB) := by
  rw [localAtkin_eq_trace_dilation]
  change rationalMap (rationalGL (traceSL M p A B hAB 0))*rationalMap (dilationGL p hp)=_
  rw [← map_mul]
  rfl

#print axioms localAtkin_eq_dilation_inv
#print axioms localAtkin_eq_trace_dilation
#print axioms localAtkin_rationalMap

end QuantitativeArithmeticAtkinSigns
