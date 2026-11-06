module

public import QuantitativeEulerDiamondNormV1
public import QuantitativeEulerDiamondPolynomialNormV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondDecode

open UpperHalfPlane AsymptoticRationalBranches AsymptoticRationalFreeness
open QuantitativeHolomorphic AsymptoticRegularCompactBranch
open scoped Classical

def expressionMass (B : Ring) : ℝ := ∑ g∈B.coeff.support, ‖B.coeff g‖

/-- Every fixed finite multiplier has a uniform polynomial transport
bound. The matrix-height constant is constructed from its finite support,
and is independent of epsilon, the height cutoff and the weight exponent.
Only the actual residual on each indicated compact image is assumed bounded. -/
theorem fixed_multiplier_polynomial_bound (B : Ring) :
    ∃ C : ℝ, 1≤C ∧ ∀ (A : Ring) {s : Set ℍ} (hs : IsCompact s)
      {ε : ℝ} (hε : 0<ε) (H : ℝ)
      (_hre : ∀ z∈s, |z.re|≤1) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space) (D : ℝ),
      (∀ g∈B.coeff.support,
        ‖compactAction (branchImage_compact (symbolBranch g) hs) hε t x A v‖≤D) →
      ‖compactAction hs hε t x (A*B) v‖≤
        expressionMass B*(integerCompactDistortion C H)^t*D := by
  obtain ⟨C,hC,hmat⟩ := QuantitativeEulerIntegerHeight.finite_family_height
    (fun g : ↥B.coeff.support => (g : G))
  refine ⟨C,hC,?_⟩
  intro A s hs ε hε H hre him t x v D hD
  rw [compactAction_mul]
  simp only [_root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply]
  calc
    _ ≤ ∑ g∈B.coeff.support, ‖B.coeff g‖*(integerCompactDistortion C H)^t*D := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro g hg
      obtain ⟨M,hM,hb⟩ := hmat ⟨g,hg⟩
      have hM' : IntegerAction (ofMatrix (symbolBranch g).matrix (symbolBranch g).positive) M := by
        simpa only [symbolBranch_label] using hM
      rw [norm_smul,mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact ((branchTransport (symbolBranch g) hs hε t x).le_of_opNorm_le
        (branchTransport_integer_norm (symbolBranch g) hs hM' (by linarith) hb hε hre him t x) _).trans
        (mul_le_mul_of_nonneg_left (hD g hg) (by unfold integerCompactDistortion; positivity))
    _ = _ := by simp only [expressionMass,Finset.sum_mul]

#print axioms fixed_multiplier_polynomial_bound
end QuantitativeEulerDiamondDecode
