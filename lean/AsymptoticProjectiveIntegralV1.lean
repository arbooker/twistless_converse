module

public import AsymptoticDegeneracyContainmentV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceLabels

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness
open scoped MatrixGroups

/-- A determinant-one rational representative of an integral projective
matrix is integral: the possible scalar is necessarily a sign. -/
theorem projective_det_one_integral (R : GL (Fin 2) ℚ)
    (hR : R.val.det=1) (A : SL(2,ℤ))
    (he : rationalMap R=rationalMap (rationalGL A)) (i j : Fin 2) :
    ∃ a : ℤ, R.val i j=(a:ℚ) := by
  change ProjGenLinGroup.mk (realMatrix R)=ProjGenLinGroup.mk (realMatrix (rationalGL A)) at he
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
  have hR' : (realMatrix R).val.det=1 := by
    change (R.val.map (fun r : ℚ => (r:ℝ))).det=1
    rw [← Rat.cast_det,hR,Rat.cast_one]
  have hA' : (realMatrix (rationalGL A)).val.det=1 := by
    change (A.val.map (fun a : ℤ => (a:ℝ))).det=1
    rw [← Int.cast_det,A.property,Int.cast_one]
  have hd := congrArg (fun B : GL (Fin 2) ℝ => B.val.det) hu
  change ((realMatrix R).val*(GeneralLinearGroup.scalar (Fin 2) u).val).det=_ at hd
  rw [Matrix.det_mul,hR',one_mul] at hd
  have hu2 : (u:ℝ)^2=1 := by
    simpa [GeneralLinearGroup.scalar,Matrix.scalar,Matrix.det_fin_two,hA'] using hd
  have hij := congrArg (fun B : GL (Fin 2) ℝ => B.val i j) hu
  change ((realMatrix R).val*(GeneralLinearGroup.scalar (Fin 2) u).val) i j=(A.val i j:ℝ) at hij
  have hij' : (R.val i j:ℝ)*(u:ℝ)=(A.val i j:ℝ) := by
    simpa [realMatrix,GeneralLinearGroup.map,GeneralLinearGroup.scalar,Matrix.scalar,
      Matrix.mul_diagonal] using hij
  rcases (sq_eq_one_iff).mp hu2 with h | h
  · refine ⟨A.val i j,?_⟩
    rw [h,mul_one] at hij'
    exact_mod_cast hij'
  · refine ⟨-A.val i j,?_⟩
    rw [h,mul_neg_one] at hij'
    have hh : (R.val i j:ℝ)=-(A.val i j:ℝ) := by linarith
    exact_mod_cast hh

end AsymptoticCongruenceLabels

namespace AsymptoticCongruenceStrip

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticCongruenceLabels
open AsymptoticRationalBranches
open scoped MatrixGroups

/-- Membership in any congruence subgroup forces all entries of a
unit-determinant rational representative to be integers. -/
theorem ofMatrix_mem_gamma_integral (N : ℕ) (R : GL (Fin 2) ℚ)
    (hR : R.val.det=1) (hpos : 0<(realMatrix R).det.val)
    (hmem : ofMatrix R hpos∈gamma N) (i j : Fin 2) :
    ∃ a : ℤ, R.val i j=(a:ℚ) := by
  obtain ⟨A,_,he⟩ := hmem
  apply projective_det_one_integral R hR A
  exact (congrArg (fun g : AsymptoticRationalGroup.Group => g.val.val) he).symm

#print axioms AsymptoticCongruenceLabels.projective_det_one_integral
#print axioms ofMatrix_mem_gamma_integral

end AsymptoticCongruenceStrip
