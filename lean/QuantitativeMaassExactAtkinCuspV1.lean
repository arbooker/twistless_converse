module

public import AsymptoticAtkinLehnerNormalizerV1
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open scoped MatrixGroups

namespace QuantitativeMaass

def exactAtkinMatrix (D Q : ℕ) (A B : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(Q:ℤ),B;-(Q:ℤ)*D,(Q:ℤ)*A]

theorem exactAtkinMatrix_det (D Q : ℕ) (A B : ℤ)
    (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) : (exactAtkinMatrix D Q A B).det=(Q:ℤ) := by
  rw [Matrix.det_fin_two]
  dsimp [exactAtkinMatrix]
  linear_combination (Q:ℤ)*hAB

/-- An explicit Gamma0(QD) factor comparing a determinant-Q matrix of
Atkin--Lehner shape with the fixed Bezout representative. -/
def exactAtkinComparison (D Q : ℕ) (A B x y z w : ℤ)
    (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) (hxy : (Q:ℤ)*x*w-(D:ℤ)*y*z=1) : SL(2,ℤ) :=
  ⟨!![(Q:ℤ)*A*x+(D:ℤ)*y,-B*x+y;
    (Q:ℤ)*D*(A*z+w),-(D:ℤ)*B*z+(Q:ℤ)*w],by
    rw [Matrix.det_fin_two]
    dsimp
    linear_combination ((Q:ℤ)*x*w-(D:ℤ)*y*z)*hAB+hxy⟩

theorem exactAtkinComparison_mem (D Q : ℕ) (A B x y z w : ℤ)
    (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) (hxy : (Q:ℤ)*x*w-(D:ℤ)*y*z=1) :
    exactAtkinComparison D Q A B x y z w hAB hxy∈CongruenceSubgroup.Gamma0 (Q*D) := by
  apply (gamma0_mem_dvd (Q*D) _).mpr
  exact ⟨A*z+w,by simp [exactAtkinComparison]⟩

theorem exactAtkinComparison_mul (D Q : ℕ) (A B x y z w : ℤ)
    (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) (hxy : (Q:ℤ)*x*w-(D:ℤ)*y*z=1) :
    (exactAtkinComparison D Q A B x y z w hAB hxy).val*exactAtkinMatrix D Q A B=
      !![(Q:ℤ)*x,y;(Q:ℤ)*D*z,(Q:ℤ)*w] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exactAtkinComparison,exactAtkinMatrix,Matrix.mul_apply,Fin.sum_univ_two]
  · linear_combination (Q:ℤ)*x*hAB
  · linear_combination y*hAB
  · linear_combination (Q:ℤ)*D*z*hAB
  · linear_combination (Q:ℤ)*w*hAB

theorem integral_first_column_coprime (a : SL(2,ℤ)) : IsCoprime (a 0 0) (a 1 0) := by
  refine ⟨a 1 1,-a 0 1,?_⟩
  have h := a.property
  rw [Matrix.det_fin_two] at h
  change a 0 0*a 1 1-a 0 1*a 1 0=1 at h
  linear_combination h

/-- The fixed exact-divisor Atkin--Lehner representative sends a cusp
whose denominator is D times a number prime to Q to infinity, modulo
Gamma0(QD). No cusp classification theorem is assumed. -/
theorem exactAtkin_cusp_to_infinity (D Q : ℕ) (A B : ℤ)
    (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) (a : SL(2,ℤ)) (c : ℤ)
    (hc : a 1 0=(D:ℤ)*c) (hQc : IsCoprime (Q:ℤ) (a 1 0)) :
    ∃ b : SL(2,ℤ),b∈CongruenceSubgroup.Gamma0 (Q*D) ∧
      (b.val*exactAtkinMatrix D Q A B*a.val) 1 0=0 := by
  obtain ⟨x,y,hxy⟩ := hQc.mul_left (integral_first_column_coprime a)
  have hw : (Q:ℤ)*x*(a 0 0)-(D:ℤ)*y*(-c)=1 := by
    rw [hc] at hxy
    linear_combination hxy
  refine ⟨exactAtkinComparison D Q A B x y (-c) (a 0 0) hAB hw,
    exactAtkinComparison_mem D Q A B x y (-c) (a 0 0) hAB hw,?_⟩
  rw [exactAtkinComparison_mul]
  simp [Matrix.mul_apply,Fin.sum_univ_two,hc]
  ring

/-- At a squarefree level every denominator has an exact-divisor split
to which the explicit Atkin--Lehner cusp calculation applies. -/
theorem squarefree_cusp_divisor (N : ℕ) (hS : Squarefree N) (c : ℤ) :
    ∃ D Q : ℕ,Q*D=N ∧ Nat.Coprime Q D ∧ (D:ℤ)∣c ∧ IsCoprime (Q:ℤ) c := by
  by_cases hc : c=0
  · subst c
    exact ⟨N,1,by simp,by simp,by simp,1,0,by norm_num⟩
  let D := Nat.gcd N c.natAbs
  let Q := N/D
  have hd : D∣c.natAbs := Nat.gcd_dvd_right N c.natAbs
  have hq : Nat.Coprime Q c.natAbs :=
    Nat.coprime_div_gcd_of_squarefree hS (Int.natAbs_ne_zero.mpr hc)
  refine ⟨D,Q,Nat.div_mul_cancel (Nat.gcd_dvd_left N c.natAbs),
    hq.of_dvd_right hd,Int.natCast_dvd.mpr hd,?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one,Int.gcd_def,Int.natAbs_natCast]
  exact hq

theorem squarefree_cusp_atkin_matrix (N : ℕ) (hN : 0<N) (hS : Squarefree N)
    (a : SL(2,ℤ)) :
    ∃ D Q : ℕ,∃ A B : ℤ,∃ b : SL(2,ℤ),
      Q*D=N ∧ 0<Q ∧ (Q:ℤ)*A+(D:ℤ)*B=1 ∧
      b∈CongruenceSubgroup.Gamma0 N ∧
      (b.val*exactAtkinMatrix D Q A B*a.val) 1 0=0 := by
  obtain ⟨D,Q,hQD,hcop,hDc,hQc⟩ := squarefree_cusp_divisor N hS (a 1 0)
  obtain ⟨A,B,hAB⟩ := hcop.isCoprime
  have hab : (Q:ℤ)*A+(D:ℤ)*B=1 := by simpa only [mul_comm] using hAB
  obtain ⟨c,hc⟩ := hDc
  obtain ⟨b,hb,hzero⟩ := exactAtkin_cusp_to_infinity D Q A B hab a c hc hQc
  refine ⟨D,Q,A,B,b,hQD,?_,hab,?_,hzero⟩
  · have : 0<Q*D := hQD.symm ▸ hN
    apply Nat.pos_of_ne_zero
    intro hQ
    simp only [hQ,zero_mul,lt_self_iff_false] at this
  · simpa only [hQD] using hb

#print axioms exactAtkinMatrix_det
#print axioms exactAtkinComparison_mem
#print axioms exactAtkinComparison_mul
#print axioms integral_first_column_coprime
#print axioms exactAtkin_cusp_to_infinity
#print axioms squarefree_cusp_divisor
#print axioms squarefree_cusp_atkin_matrix

end QuantitativeMaass
