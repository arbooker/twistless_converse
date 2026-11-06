module

public import AsymptoticHolomorphicTraceV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap InnerProductSpace AsymptoticDiagonalTrace AsymptoticFourierNorm
open scoped InnerProduct

variable {G H : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def compressedSandwich (R : G →L[ℂ] H) (I : G →L[ℂ] G)
    (U : Submodule ℂ H) [CompleteSpace U] : U →L[ℂ] U :=
  U.subtypeL.adjoint.comp ((R.comp (I.comp R.adjoint)).comp U.subtypeL)

theorem compressedSandwich_diagonal_bound (R : G →L[ℂ] H) (I : G →L[ℂ] G)
    (U : Submodule ℂ H) [CompleteSpace U] (u : U) :
    ‖(⟪compressedSandwich R I U u,u⟫_ℂ).re‖≤‖I‖*‖R.adjoint (u:H)‖^2 := by
  have he : ⟪compressedSandwich R I U u,u⟫_ℂ=⟪I (R.adjoint (u:H)),R.adjoint (u:H)⟫_ℂ := by
    have hu := U.subtypeL.adjoint_inner_left u (R (I (R.adjoint (u:H))))
    change ⟪U.subtypeL.adjoint (R (I (R.adjoint (u:H)))),u⟫_ℂ=_
    rw [hu]
    exact (R.adjoint_inner_right (I (R.adjoint (u:H))) (u:H)).symm
  rw [he,Real.norm_eq_abs]
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_inner_le_norm _ _).trans
  apply (mul_le_mul_of_nonneg_right (I.le_opNorm _) (norm_nonneg _)).trans_eq
  ring

theorem compressedSandwich_sub (R : G →L[ℂ] H) (I J : G →L[ℂ] G)
    (U : Submodule ℂ H) [CompleteSpace U] :
    compressedSandwich R I U-compressedSandwich R J U=compressedSandwich R (I-J) U := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [compressedSandwich,sub_apply,comp_apply,map_sub]

theorem compressedSandwich_summable (R : G →L[ℂ] H) (I : G →L[ℂ] G)
    (U : Submodule ℂ H) [CompleteSpace U] (b : HilbertBasis ℕ ℂ U)
    (m t : ℕ) {scale ε C : ℝ} (hs : 0<scale) (hε : 0<ε)
    (hg : ∀ n,‖R.adjoint ((b n:U):H)‖^2≤C*modeRatio m t scale ε (n+1)) :
    Summable (fun n => (⟪compressedSandwich R I U (b n),b n⟫_ℂ).re) := by
  apply Summable.of_norm_bounded
    ((positive_modeRatio_summable_bound m t hs hε).1.mul_left (‖I‖*C))
  intro n
  apply (compressedSandwich_diagonal_bound R I U (b n)).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hg n) (norm_nonneg I)

/-- An inverse-polynomial error costs O(delta*k) in the actual Fourier
trace, using the reconstruction Gram majorant. Positivity of the
approximating polynomial is not needed. -/
theorem compressedSandwich_trace_error (R : G →L[ℂ] H) (I J : G →L[ℂ] G)
    (U : Submodule ℂ H) [CompleteSpace U] (b : HilbertBasis ℕ ℂ U)
    (m t : ℕ) {scale ε C δ : ℝ} (hs : 0<scale) (hε : 0<ε) (hC : 0≤C)
    (hg : ∀ n,‖R.adjoint ((b n:U):H)‖^2≤C*modeRatio m t scale ε (n+1))
    (hδ : ‖I-J‖≤δ) :
    ‖trace b (compressedSandwich R I U)-trace b (compressedSandwich R J U)‖≤
      δ*C*(1+majorantConstant t scale ε)*(m+2:ℕ) := by
  have hδ0 := (norm_nonneg (I-J)).trans hδ
  have hi := compressedSandwich_summable R I U b m t hs hε hg
  have hj := compressedSandwich_summable R J U b m t hs hε hg
  have hdiff (n : ℕ) :
      (⟪compressedSandwich R I U (b n),b n⟫_ℂ).re-(⟪compressedSandwich R J U (b n),b n⟫_ℂ).re=
        (⟪compressedSandwich R (I-J) U (b n),b n⟫_ℂ).re := by
    rw [← compressedSandwich_sub,sub_apply,inner_sub_left,Complex.sub_re]
  have hbound (n : ℕ) :
      ‖(⟪compressedSandwich R (I-J) U (b n),b n⟫_ℂ).re‖≤δ*C*modeRatio m t scale ε (n+1) := by
    apply (compressedSandwich_diagonal_bound R (I-J) U (b n)).trans
    simpa only [mul_assoc] using mul_le_mul hδ (hg n) (sq_nonneg _) hδ0
  unfold trace
  rw [← hi.tsum_sub hj]
  simp only [hdiff]
  have hsumm := compressedSandwich_summable R (I-J) U b m t hs hε hg
  apply (norm_tsum_le_tsum_norm hsumm.norm).trans
  have hmaj := positive_modeRatio_summable_bound m t hs hε
  apply (hsumm.norm.tsum_le_tsum hbound (hmaj.1.mul_left (δ*C))).trans
  rw [tsum_mul_left]
  apply (mul_le_mul_of_nonneg_left hmaj.2 (mul_nonneg hδ0 hC)).trans_eq
  ring

#print axioms compressedSandwich_diagonal_bound
#print axioms compressedSandwich_summable
#print axioms compressedSandwich_trace_error

end AsymptoticObservation
