module

public import QuantitativeEulerEndpointFrickeV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators AsymptoticCongruenceLabels
open QuantitativeEulerDiamondDecode QuantitativeArithmeticDiamondLabels
open AsymptoticFreshMatrices AsymptoticRegularObservationRows AsymptoticRegularBranchFamily
open AsymptoticFreshCompactDefects AsymptoticFreshAveraging
open AsymptoticRationalBranches AsymptoticRationalFreeness AsymptoticReconstructionBranch
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups Classical

/-- A literal integral representative of the actual projective Fricke
label, with determinant N rather than an artificial determinant-one lift. -/
theorem integerAction_fricke (N : ℕ) (hN : 0<N) :
    IntegerAction (frickeLabel N hN) (integralFrickeMatrix N) := by
  constructor
  · simpa [integralFrickeMatrix,Matrix.det_fin_two] using (show (N : ℤ)≠0 by exact_mod_cast hN.ne')
  · intro z
    rw [frickeLabel,ofMatrix_action,realMatrix_branch,branch_action (by exact_mod_cast hN)]
    simp [integralFrickeMatrix]

theorem fricke_entry_bound (N : ℕ) : MatrixEntryBound (integralFrickeMatrix N) (1+(N : ℝ)) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [integralFrickeMatrix]
  all_goals positivity

/-- The inverse of an actual prime branch has an explicit integral
representative W^{-1}C. Its height is at most 2(1+N) times the canonical
height, uniformly in the growing prime and its residue index. -/
theorem inverse_prime_branch_integer_bound (N q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hq : ¬q∣N) (j : Fin (q-1)) {B : ℝ}
    (hC : MatrixEntryBound (swappedCanonical N q hq j).val B) :
    IntegerAction ((AsymptoticFreshAveraging.defectLabel N q hN hq j)⁻¹)
      ((integralFrickeMatrix N).adjugate*(swappedCanonical N q hq j).val) ∧
    MatrixEntryBound ((integralFrickeMatrix N).adjugate*(swappedCanonical N q hq j).val)
      (2*(1+(N : ℝ))*B) := by
  constructor
  · have he : (AsymptoticFreshAveraging.defectLabel N q hN hq j)⁻¹=
        (frickeLabel N hN)⁻¹*integralLabel (swappedCanonical N q hq j) := by
      rw [←fricke_defectLabel_inv N q hN hq j,inv_mul_cancel_left]
    rw [he]
    exact (integerAction_fricke N hN).inv.mul (integerAction_integralLabel _)
  · exact matrix_entry_bound_mul (by positivity)
      (matrix_entry_bound_adjugate (fricke_entry_bound N)) hC

/-- Signed canonical recovery with a quantified growing-prime transport
cost. The remaining prime-branch residual is the original observed branch,
not a chosen equivalent matrix. -/
theorem canonical_original_norm (N q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hq : ¬q∣N) (j : Fin (q-1)) (w : ℂ) (hw : w*w=1)
    {B : ℝ} (hB : 0≤B) (hC : MatrixEntryBound (swappedCanonical N q hq j).val B)
    {s : Set ℍ} (hs : IsCompact s) {ε H : ℝ} (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    let b := symbolBranch ((AsymptoticFreshAveraging.defectLabel N q hN hq j)⁻¹)
    let hu := branchImage_compact b hs
    ‖AsymptoticCongruenceDefect.operator (swappedCanonical N q hq j) hs hε t x v‖≤
      ‖w‖*(integerCompactDistortion (2*(1+(N : ℝ))*B) H)^t*
        (‖twist N 1 hN Nat.zero_lt_one w hu hε t x v‖+
          ‖(w • compact (AsymptoticFreshCompactDefects.matrixBranch N q hN hq j) hu hε t x-
            compact identityBranch hu hε t x) v‖) := by
  dsimp only
  let b := symbolBranch ((AsymptoticFreshAveraging.defectLabel N q hN hq j)⁻¹)
  obtain ⟨hM,hbound⟩ := inverse_prime_branch_integer_bound N q hN hq j hC
  have hMb : IntegerAction (ofMatrix b.matrix b.positive)
      ((integralFrickeMatrix N).adjugate*(swappedCanonical N q hq j).val) := by
    rw [symbolBranch_label]
    exact hM
  have hT := branchTransport_integer_norm b hs hMb (by positivity) hbound hε hre him t x
  rw [compact_canonical_recovery N q hN hq w hw j,_root_.smul_apply,norm_smul,norm_neg,
    ContinuousLinearMap.comp_apply]
  have ht := (branchTransport b hs hε t x).le_of_opNorm_le hT
    ((twist N 1 hN Nat.zero_lt_one w (branchImage_compact b hs) hε t x+
      (w • compact (AsymptoticFreshCompactDefects.matrixBranch N q hN hq j)
        (branchImage_compact b hs) hε t x-compact identityBranch (branchImage_compact b hs) hε t x)) v)
  rw [_root_.add_apply] at ht
  have hh := ht.trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by unfold integerCompactDistortion; positivity))
  simpa only [mul_assoc,_root_.add_apply,b] using mul_le_mul_of_nonneg_left hh (norm_nonneg w)

#print axioms integerAction_fricke
#print axioms inverse_prime_branch_integer_bound
#print axioms canonical_original_norm
end QuantitativeEulerEndpointPrepared
