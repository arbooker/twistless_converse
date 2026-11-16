module

public import QuantitativeMaassBroadHeckeRemainderV1
public import QuantitativeMaassBroadCompactFactorV1
public import QuantitativeMaassWaveCrossKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap

namespace QuantitativeMaass

def upperBroadKernel (N p : ℕ) [Fact p.Prime]
    (L : ℝ) (hL : 0 < L) (t τ : ℝ) : ℕ → HeckeUpper → ℍ → ℂ
  | 0,M,z => if hM : 0 < M.matrix.det then
      radialPoincareKernel N (broadTranslatedProfile L hL t τ) z
        (positiveIntegralGL M.matrix hM • z) else 0
  | n+1,M,z => (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ) *
      ∑ j : Option (ZMod p), upperBroadKernel N p L hL t τ n (HeckeUpper.left p j M) z

/-- The identity coefficient is the exact returning-word count; the
remaining term is the actual nonscalar correspondence sum. -/
theorem upperBroadKernel_split (N p : ℕ) [Fact p.Prime]
    (L : ℝ) (hL : 1 ≤ L) (t τ : ℝ) (n : ℕ) (M : HeckeUpper)
    (hM : 0 < M.matrix.det) (z : ℍ) :
    upperBroadKernel N p L (lt_of_lt_of_le zero_lt_one hL) t τ n M z =
      (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ)^n*(HeckeUpper.rawWalks p n M:ℂ)*
        broadTranslatedProfile L (lt_of_lt_of_le zero_lt_one hL) t τ 1 +
      upperBroadRemainder N p L (lt_of_lt_of_le zero_lt_one hL) t τ n M z := by
  classical
  induction n generalizing M with
  | zero =>
    rw [upperBroadKernel, dite_eq_left hM,
      radialIntegralKernel_identity_split N M.matrix hM _ (2+|τ|) (by positivity)
        (broadTranslatedProfile_support L hL t τ), upperBroadRemainder, dite_eq_left hM]
    simp only [pow_zero, one_mul, HeckeUpper.rawWalks, integralIdentityCoset_upper_iff N M hM]
    split_ifs <;> simp
  | succ n ih =>
    simp only [upperBroadKernel, upperBroadRemainder]
    simp_rw [ih _ (heckeUpper_left_det_pos p _ M hM)]
    rw [Finset.sum_add_distrib, mul_add]
    congr 1
    simp only [HeckeUpper.rawWalks, Nat.cast_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring

theorem upperBroadKernel_eq_iterate (N p : ℕ) [Fact p.Prime]
    (L : ℝ) (hL : 0 < L) (t τ : ℝ) (n : ℕ) (M : HeckeUpper)
    (hM : 0 < M.matrix.det) (z : ℍ) :
    upperBroadKernel N p L hL t τ n M z =
      heckeBranchIterate 1 p n (fun w => radialPoincareKernel N
        (broadTranslatedProfile L hL t τ) z w) (positiveIntegralGL M.matrix hM • z) := by
  induction n generalizing M with
  | zero => simp only [upperBroadKernel, dite_eq_left hM, heckeBranchIterate]
  | succ n ih =>
    simp only [upperBroadKernel, heckeBranchIterate, normalizedCuspHecke, cuspHeckeSum,
      Complex.real_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [ih (HeckeUpper.left p j M) (heckeUpper_left_det_pos p j M hM), heckeUpper_left_action]

/-- Every mixed broad kernel is the literal wave and Hecke power acting
on the actual quotient column, not a formally assigned spectral symbol. -/
theorem broadAbelColumn_wave_hecke_power (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬p∣N) (hNp : (N:ZMod p) ≠ 0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (L : ℝ) (hL : 0 < L) (t τ : ℝ) (n : ℕ) (z : ℍ) :
    inner ℂ (Wave.shiftedQuotientWave N τ
      (((HeckeL2.operator N p hN hpN a b hab)^n) (broadAbelColumn N L hL t z)))
      (broadAbelColumn N L hL t z) = upperBroadKernel N p L hL t τ n HeckeUpper.root z := by
  rw [upperBroadKernel_eq_iterate N p L hL t τ n HeckeUpper.root
    (by norm_num [HeckeUpper.det_matrix, HeckeUpper.root_det]), heckeUpper_root_action]
  exact timeSquare_wave_hecke_power_kernel N p hN hpN hNp a b hab
    (broadTimeSchwartz L hL t) (broadTimeWeight_compact L hL t)
    (broadTimeWeight_even L t) (broadTimeWeight_real L t) (1/L) (by positivity)
    (broadTimeWeight_support L hL t) τ n z z

#print axioms upperBroadKernel_split
#print axioms upperBroadKernel_eq_iterate
#print axioms broadAbelColumn_wave_hecke_power

end QuantitativeMaass
