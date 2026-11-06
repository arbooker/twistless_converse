module

public import QuantitativeEulerDiamondTransportV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondDecode

open UpperHalfPlane AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRegularBranchFamily AsymptoticCompactBranch
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

theorem expression_eq_sum (B : Ring) :
    B=∑ g∈B.coeff.support, B.coeff g • symbol g := by
  simpa only [Finsupp.sum,symbol,MonoidAlgebra.of_apply,MonoidAlgebra.smul_single,
    smul_eq_mul,mul_one] using (MonoidAlgebra.sum_coeff_single B).symm

/-- Explicit finite output transport for any multiplier, in particular
the inverse and correction polynomials in the diamond identity. -/
theorem compactAction_mul (A B : Ring) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compactAction hs hε t x (A*B)=
      ∑ g∈B.coeff.support, B.coeff g •
        (branchTransport (symbolBranch g) hs hε t x).comp
          (compactAction (branchImage_compact (symbolBranch g) hs) hε t x A) := by
  calc
    compactAction hs hε t x (A*B)=
        ∑ g∈B.coeff.support, B.coeff g • compactAction hs hε t x (A*symbol g) := by
      conv_lhs => rw [expression_eq_sum B]
      simp only [Finset.mul_sum,mul_smul_comm,map_sum,map_smul]
    _=_ := by
      apply Finset.sum_congr rfl
      intro g _
      congr 1
      simpa only [symbolBranch_label] using
        compactAction_mul_symbol (symbolBranch g) hs hε t x A

/-- The multiplier estimate retains the actual enlarged compact sets
and their explicit cap-ratio bounds. It applies to arbitrary vectors,
so it estimates residual sizes rather than only their common kernel. -/
theorem compactAction_mul_norm (A B : Ring) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x (A*B) v‖≤
      ∑ g∈B.coeff.support, ‖B.coeff g‖*
        (data (realMatrix (symbolBranch g).matrix) hs hε t).bound*
          ‖compactAction (branchImage_compact (symbolBranch g) hs) hε t x A v‖ := by
  rw [compactAction_mul]
  simp only [_root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro g _
  rw [norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left
    ((branchTransport (symbolBranch g) hs hε t x).le_of_opNorm_le
      (branchTransport_norm (symbolBranch g) hs hε t x) _) (norm_nonneg _)

#print axioms compactAction_mul
#print axioms compactAction_mul_norm
end QuantitativeEulerDiamondDecode
