module

public import QuantitativeMaassExactAtkinLabelV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticRationalGroup AsymptoticRationalFreeness
open scoped MatrixGroups

namespace QuantitativeMaass

/-- Changing the Bezout coefficients of an exact Atkin representative
only left-multiplies it by a congruence transformation. -/
theorem exactAtkin_choice_mod_gamma (D Q : ℕ) (hQ : 0<Q) (A B A' B' : ℤ)
    (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) (hAB' : (Q:ℤ)*A'+(D:ℤ)*B'=1) :
    ∃ a : gamma (Q*D),a.val*exactAtkinLabel D Q hQ A B hAB=
      exactAtkinLabel D Q hQ A' B' hAB' := by
  have hxy : (Q:ℤ)*1*A'-(D:ℤ)*B'*(-1)=1 := by nlinarith [hAB']
  let a := exactAtkinComparison D Q A B 1 B' (-1) A' hAB hxy
  have ha : a∈CongruenceSubgroup.Gamma0 (Q*D) :=
    exactAtkinComparison_mem D Q A B 1 B' (-1) A' hAB hxy
  have hm : a.val*exactAtkinMatrix D Q A B=exactAtkinMatrix D Q A' B' := by
    simpa only [mul_one,mul_neg_one,exactAtkinMatrix,neg_mul] using
      exactAtkinComparison_mul D Q A B 1 B' (-1) A' hAB hxy
  refine ⟨⟨integralLabel a,⟨a,ha,rfl⟩⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (rationalGL a)*rationalMap (exactAtkinGL D Q hQ A B hAB)=
    rationalMap (exactAtkinGL D Q hQ A' B' hAB')
  rw [←map_mul]
  apply congrArg rationalMap
  apply Units.ext
  change (a.val.map (fun z : ℤ => (z:ℚ)))*
    ((exactAtkinMatrix D Q A B).map (fun z : ℤ => (z:ℚ)))=
      (exactAtkinMatrix D Q A' B').map (fun z : ℤ => (z:ℚ))
  ext i j
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => (M i j:ℚ)) hm
  simpa only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.map_apply,Int.cast_add,Int.cast_mul] using hh

#print axioms exactAtkin_choice_mod_gamma

end QuantitativeMaass
