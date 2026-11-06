module

public import QuantitativeArithmeticAtkinSignsLabelsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticAtkinSigns

open Matrix AsymptoticAtkinLehner AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticClassicalCusp AsymptoticRationalGroup
open scoped MatrixGroups

theorem localRawGL_lower (L q p : ℕ) (hp : 0<p) (A B : ℤ)
    (hAB : (p:ℤ)*A+((q*L:ℕ):ℤ)*B=1) :
    localRawGL (q*L) p hp A B hAB=
      rationalGL (localAtkinLowerSL L q p A B hAB)*
        localRawGL L p hp A ((q:ℤ)*B) (localAtkin_lower_bezout L q p A B hAB) := by
  have hab : (p:ℚ)*A+(q:ℚ)*L*B=1 := by exact_mod_cast hAB
  have he : (localAtkinLowerSL L q p A B hAB).val.map (fun z:ℤ => (z:ℚ))*
      (localRawGL L p hp A ((q:ℤ)*B) (localAtkin_lower_bezout L q p A B hAB)).val=
      ((p:ℚ)*A+(q:ℚ)*L*B) • (localRawGL (q*L) p hp A B hAB).val := by
    rw [localRawGL_val,localRawGL_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [localAtkinLowerSL,Matrix.mul_apply,Fin.sum_univ_two]
    all_goals ring
  rw [hab,one_smul] at he
  exact Units.ext he.symm

theorem localAtkin_lower (L q p : ℕ) (hL : 0<L) (hq : 0<q) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+((q*L:ℕ):ℤ)*B=1) :
    localAtkin (q*L) p (Nat.mul_pos hq hL) hp A B hAB=
      integralLabel (localAtkinLowerSL L q p A B hAB)*
        localAtkin L p hL hp A ((q:ℤ)*B) (localAtkin_lower_bezout L q p A B hAB) := by
  apply Subtype.ext
  apply Subtype.ext
  change (localAtkin (q*L) p (Nat.mul_pos hq hL) hp A B hAB).val.val=
    rationalMap (rationalGL (localAtkinLowerSL L q p A B hAB))*
      (localAtkin L p hL hp A ((q:ℤ)*B) (localAtkin_lower_bezout L q p A B hAB)).val.val
  rw [localAtkin_rationalMap,localAtkin_rationalMap,← map_mul,localRawGL_lower]

theorem localRawGL_lower_dilation (L q p : ℕ) (hq : 0<q) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+((q*L:ℕ):ℤ)*B=1) :
    dilationGL q hq*localRawGL (q*L) p hp A B hAB=
      localRawGL L p hp A ((q:ℤ)*B) (localAtkin_lower_bezout L q p A B hAB)*dilationGL q hq := by
  apply Units.ext
  change (dilationGL q hq).val*(localRawGL (q*L) p hp A B hAB).val=
    (localRawGL L p hp A ((q:ℤ)*B) (localAtkin_lower_bezout L q p A B hAB)).val*(dilationGL q hq).val
  rw [localRawGL_val,localRawGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dilationGL,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring

theorem localAtkin_lower_dilation (L q p : ℕ) (hL : 0<L) (hq : 0<q) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+((q*L:ℕ):ℤ)*B=1) :
    dilationLabel q hq*localAtkin (q*L) p (Nat.mul_pos hq hL) hp A B hAB=
      localAtkin L p hL hp A ((q:ℤ)*B) (localAtkin_lower_bezout L q p A B hAB)*dilationLabel q hq := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (dilationGL q hq)*(localAtkin (q*L) p _ hp A B hAB).val.val=
    (localAtkin L p hL hp A ((q:ℤ)*B) (localAtkin_lower_bezout L q p A B hAB)).val.val*rationalMap (dilationGL q hq)
  rw [localAtkin_rationalMap,localAtkin_rationalMap,← map_mul,← map_mul,localRawGL_lower_dilation]

#print axioms localAtkin_lower
#print axioms localAtkin_lower_dilation

end QuantitativeArithmeticAtkinSigns
