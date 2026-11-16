module

public import QuantitativeMaassReconstructedSourceErrorV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
open ContinuousLinearMap
namespace QuantitativeMaass
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Pulling a target projection back through a partial isometry gives a
terminal source with exactly the same target cogram. -/
theorem projection_source_pullback (R Q : H→L[ℂ]H) (hQ : IsStarProjection Q)
    (hRQ : R*R.adjoint*Q=Q) :
    (R.adjoint*R)*(R.adjoint*Q*R)=R.adjoint*Q*R ∧
      R*(R.adjoint*Q*R)*R.adjoint=Q := by
  have hQR : Q*R*R.adjoint=Q := by
    have hh := congrArg star hRQ
    simpa only [star_mul,show star Q=Q from hQ.isSelfAdjoint.star_eq,
      ContinuousLinearMap.star_eq_adjoint,adjoint_adjoint,←mul_assoc] using hh
  constructor
  · calc
      _ = R.adjoint*(R*R.adjoint*Q)*R := by simp only [mul_assoc]
      _ = _ := by rw [hRQ]
  · calc
      _ = (R*R.adjoint*Q)*R*R.adjoint := by simp only [mul_assoc]
      _ = _ := by rw [hRQ,hQR]

theorem projection_source_pullback_rows (R Q B : H→L[ℂ]H)
    (hRQ : R*R.adjoint*Q=Q) (hB : B*Q=0) : B*R*(R.adjoint*Q*R)=0 := by
  calc
    _ = B*(R*R.adjoint*Q)*R := by simp only [mul_assoc]
    _ = 0 := by rw [hRQ,hB,zero_mul]

theorem projection_source_pullback_norm (R Q : H→L[ℂ]H) (hR : ‖R‖≤1) (hQ : ‖Q‖≤1) :
    ‖R.adjoint*Q*R‖≤1 := by
  apply (norm_mul_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans
  rw [adjoint.norm_map]
  nlinarith [norm_nonneg R,norm_nonneg Q,mul_le_mul hR hQ (norm_nonneg Q) (by norm_num : (0:ℝ)≤1)]

#print axioms projection_source_pullback
#print axioms projection_source_pullback_rows
#print axioms projection_source_pullback_norm
end QuantitativeMaass
