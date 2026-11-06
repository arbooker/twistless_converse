module

public import QuantitativeEulerDiamondBranchesV1
public import AsymptoticFreshAveragingV1
public import AsymptoticCongruenceLabelsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticDiamondLabels

open Matrix CongruenceSubgroup QuantitativeArithmetic QuantitativeEulerDensityGenerators
open AsymptoticCongruenceLabels AsymptoticFreshMatrices AsymptoticRationalGroup
open AsymptoticRationalFreeness AsymptoticReconstructionBranch
open scoped MatrixGroups

/-- Exact integral intertwining transports to the actual positive projective
labels, without any automorphy hypothesis. -/
theorem fricke_intertwine_label (N : ℕ) (hN : 0<N) (A B : SL(2,ℤ))
    (h : integralFrickeMatrix N*A.val=B.val*integralFrickeMatrix N) :
    frickeLabel N hN*integralLabel A=integralLabel B*frickeLabel N hN := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (branch (N:ℚ) 0 0 _)*rationalMap (rationalGL A)=
    rationalMap (rationalGL B)*rationalMap (branch (N:ℚ) 0 0 _)
  rw [← map_mul,← map_mul]
  congr 1
  apply Units.ext
  change (branch (N:ℚ) 0 0 _).val*A.val.map (Int.castRingHom ℚ)=
    B.val.map (Int.castRingHom ℚ)*(branch (N:ℚ) 0 0 _).val
  have hw : (branch (N:ℚ) 0 0 (by exact_mod_cast hN.ne')).val=
      (integralFrickeMatrix N).map (Int.castRingHom ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [branch,integralFrickeMatrix,GeneralLinearGroup.mkOfDetNeZero]
  rw [hw,← Matrix.map_mul,← Matrix.map_mul,h]

theorem frickeConjugate_label (N : ℕ) (hN : 0<N) (A : SL(2,ℤ)) (hA : A∈Gamma0 N) :
    frickeLabel N hN*integralLabel A*(frickeLabel N hN)⁻¹=
      integralLabel (frickeConjugate N A hA) := by
  rw [fricke_intertwine_label N hN A _ (frickeConjugate_identity N A hA)]
  group

theorem upperSL_one_gamma1 (N : ℕ) : upperSL 1∈Gamma1 N := by
  rw [Gamma1_mem]
  norm_num [upperSL,AsymptoticFreshCRT.upper]

/-- Right quotients of same-prime canonical matrices lie in Gamma1 as well
as the left quotients used in the existing diamond interface. -/
theorem canonical_right_difference (N q : ℕ) (a b c a' b' c' : ℤ)
    (h : (q:ℤ)*c=(N:ℤ)*a*b+1) (h' : (q:ℤ)*c'=(N:ℤ)*a'*b'+1) :
    canonical N q a b c h*(canonical N q a' b' c' h')⁻¹∈Gamma1 N := by
  have hC := canonical_mem_Gamma0 N q a b c h
  have hd := canonical_same_prime_difference N q a' b' c' a b c h' h
  have hc := gamma1_conjugate N (canonical N q a b c h)⁻¹ _ ((Gamma0 N).inv_mem hC) hd
  simpa only [inv_inv,mul_assoc,mul_inv_cancel,mul_one] using hc

#print axioms fricke_intertwine_label
#print axioms frickeConjugate_label
#print axioms canonical_right_difference

end QuantitativeArithmeticDiamondLabels
