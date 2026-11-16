module

public import AsymptoticObservationPerturbationV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
open ContinuousLinearMap
namespace QuantitativeMaass
variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Reconstruction transports an approximate source identity in operator
norm. The reconstruction is only a partial isometry; its initial projection
is required to fix the actual source, not the whole ambient space. -/
theorem reconstructed_source_error (R S : G→L[ℂ]H) (E F : G→L[ℂ]G)
    (hR : ‖R‖≤1) (hS : ‖S‖≤1) (hE : ‖E‖≤1) (hF : ‖F‖≤1)
    (hRE : R.adjoint.comp (R.comp E)=E)
    {δ η : ℝ} (hδ : ‖F.comp E-E‖≤δ) (hη : ‖R-S‖≤η) :
    ‖(S.comp (F.comp S.adjoint)).comp (R.comp (E.comp R.adjoint))-
      R.comp (E.comp R.adjoint)‖≤δ+2*η := by
  let P := R.comp (E.comp R.adjoint)
  let A := R.comp (F.comp R.adjoint)
  let B := S.comp (F.comp S.adjoint)
  have hcontract (T : G→L[ℂ]G) : ‖R.comp (T.comp R.adjoint)‖≤‖T‖ := by
    calc
      _ ≤ ‖R‖*(‖T‖*‖R.adjoint‖) := (opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1*(‖T‖*1) := by rw [adjoint.norm_map];gcongr
      _ = _ := by ring
  have hPn : ‖P‖≤1 := (hcontract E).trans hE
  have hfix : A.comp P-P=R.comp ((F.comp E-E).comp R.adjoint) := by
    dsimp only [A,P]
    calc
      _ = R.comp ((F.comp (R.adjoint.comp (R.comp E))-E).comp R.adjoint) := by
        simp only [comp_sub,sub_comp,comp_assoc]
      _ = _ := by rw [hRE]
  have hfixn : ‖A.comp P-P‖≤δ := by rw [hfix];exact (hcontract _).trans hδ
  have hBA : ‖B-A‖≤2*η := by
    rw [norm_sub_rev]
    have hh := AsymptoticObservation.sandwich_sub_norm_le R S F F hF hF
    simp only [sub_self,norm_zero,mul_zero,add_zero] at hh
    exact hh.trans (mul_le_mul (by linarith : ‖R‖+‖S‖≤2) hη
      (norm_nonneg _) (by norm_num : (0:ℝ)≤2))
  have he : B.comp P-P=(B-A).comp P+(A.comp P-P) := by
    simp only [sub_comp]
    abel
  change ‖B.comp P-P‖≤_
  rw [he]
  apply (norm_add_le _ _).trans
  have hh : ‖(B-A).comp P‖≤2*η := by
    apply (opNorm_comp_le _ _).trans
    calc
      _ ≤ ‖B-A‖*1 := mul_le_mul_of_nonneg_left hPn (norm_nonneg _)
      _ ≤ 2*η := by simpa only [mul_one] using hBA
  linarith

#print axioms reconstructed_source_error
end QuantitativeMaass
