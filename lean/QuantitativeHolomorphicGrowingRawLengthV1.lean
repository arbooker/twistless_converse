module

public import QuantitativeHolomorphicGrowingHeightV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight AsymptoticCertificateBranches

theorem geometricPrefix_le_pow (M j : ℕ) :
    1+(∑ l∈Finset.range j, M^l)*M≤(1+M)^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ,pow_succ]
    calc
      1+((∑ l∈Finset.range j, M^l)+M^j)*M =
          (1+(∑ l∈Finset.range j,M^l)*M)+M^j*M := by ring
      _ ≤ (1+M)^j+(1+M)^j*M := add_le_add ih
        (Nat.mul_le_mul_right M (Nat.pow_le_pow_left (by omega : M≤1+M) j))
      _ = (1+M)^j*(1+M) := by ring

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem reconstructionGrowthConstant_nonneg (P : Parameters A) {C : ℝ} (hC : 0≤C) :
    0≤reconstructionGrowthConstant A P C := by
  unfold reconstructionGrowthConstant reconstructionThresholdConstant newtonAmplificationConstant
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hl6 : 0≤Real.log 6 := Real.log_nonneg (by norm_num)
  have hl7 : 0≤Real.log 7 := Real.log_nonneg (by norm_num)
  have hT : 0≤AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P) := by
    unfold AsymptoticCertificateOperators.terminalConstant
    positivity
  positivity

theorem foldGrowthConstant_nonneg (P : Parameters A) {C : ℝ} (hC : 0≤C) :
    0≤foldGrowthConstant A P C := by
  unfold foldGrowthConstant newtonAmplificationConstant
  have hB := foldTailCoefficient_nonneg A P
  have hL := reconstructionGrowthConstant_nonneg A P hC
  have h3 : 0≤Real.log 3 := Real.log_nonneg (by norm_num)
  have h7 : 0≤Real.log 7 := Real.log_nonneg (by norm_num)
  positivity

/-- An actual expression-length estimate. The premises concern only the
explicit depth and fold radius; the geometric sum is proved internally. -/
theorem rawReconstructionLength_growth {j J : ℕ} {a b u : ℝ}
    (_ha : 0≤a) (hb : 0≤b) (hu : 1≤u)
    (hj : (j:ℝ)≤a*u) (hJ : (J:ℝ)≤Real.exp (b*u)) :
    (rawReconstructionLength A j J:ℝ)≤
      Real.exp (a*(3*(Fintype.card (Index A):ℝ)+1+b)*u^2) := by
  let m : ℝ := Fintype.card (Index A)
  let M : ℕ := Fintype.card (Index A)*(2*J+1)
  have hm : 0≤m := Nat.cast_nonneg _
  have hE : 1≤Real.exp (b*u) := Real.one_le_exp (by positivity)
  have hbase : (1+M:ℝ)≤(3*m+1)*Real.exp (b*u) := by
    have hmul := mul_le_mul_of_nonneg_left hJ hm
    dsimp [M,m] at *
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg (Fintype.card (Index A)) : (0:ℝ)≤_)]
  have hcoef : 3*m+1≤Real.exp (3*m+1) := by linarith [Real.add_one_le_exp (3*m+1)]
  have hbaseE : (1+M:ℝ)≤Real.exp ((3*m+1+b)*u) := by
    apply hbase.trans
    apply (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)).trans
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : 0≤3*m+1)]
  have hraw : (rawReconstructionLength A j J:ℝ)≤(1+(M:ℝ))^j := by
    exact_mod_cast geometricPrefix_le_pow M j
  apply hraw.trans
  apply (pow_le_pow_left₀ (by positivity) hbaseE j).trans
  rw [←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hj (by positivity : 0≤(3*m+1+b)*u)
  nlinarith only [hmul]

def rawLengthGrowthConstant (P : Parameters A) (C : ℝ) : ℝ :=
  reconstructionGrowthConstant A P C*
    (3*(Fintype.card (Index A):ℝ)+1+foldGrowthConstant A P C)

theorem growing_raw_reconstruction_length (P : Parameters A) {C s : ℝ} (hC : 0≤C)
    (hs : 1≤s) (d : ℕ) (hd : (d:ℝ)≤Real.exp (C*s^2)) :
    let D : ℝ := 2*d+2
    let n := newtonDepth A P D (Real.exp (-8*s))
    let j := reconstructionDepth A P D (Real.exp (-8*s)) n
    let J := foldCutoff A P D (Real.exp (-8*s)) j n
    (rawReconstructionLength A j J:ℝ)≤Real.exp (rawLengthGrowthConstant A P C*s^8) := by
  have hs4 : 1≤s^4 := by nlinarith [sq_nonneg (s^2-1)]
  have h := rawReconstructionLength_growth A (reconstructionGrowthConstant_nonneg A P hC)
    (foldGrowthConstant_nonneg A P hC) hs4
    (growing_reconstruction_depth A P hC hs d hd) (growing_fold_cutoff A P hC hs d hd)
  convert h using 1
  congr 1
  dsimp [rawLengthGrowthConstant]
  ring

#print axioms rawReconstructionLength_growth
#print axioms growing_raw_reconstruction_length

end QuantitativeHolomorphic.Schedule
