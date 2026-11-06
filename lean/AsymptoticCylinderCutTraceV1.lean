module

public import AsymptoticCylinderCutReconstructionV1
public import AsymptoticCylinderTraceV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticReconstructedCount

open ContinuousLinearMap InnerProductSpace FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticObservation AsymptoticFourierNorm AsymptoticDiagonalTrace
open scoped InnerProduct

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The cutoff still factors through the same capped inclusion. -/
theorem cutReconstruction_eq_weighted (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N) (Y : ℝ) :
    cutReconstruction A hN P h e Y=(inclusion (parameters A P).epsilon_pos).comp
      ((AsymptoticCylinderTerminal.projection Y).comp (reconstruction A hN P h e)) := by
  have he := congrArg (fun T : Space →L[ℂ] Space => T.comp (reconstruction A hN P h e))
    (AsymptoticCylinderTerminal.projection_comp_inclusion (parameters A P).epsilon_pos Y)
  exact he

theorem cutReconstruction_fourier_gram (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (Y : ℝ) (m t : ℕ) {scale : ℝ} (hs : 0<scale) (n : ℕ) :
    ‖(cutReconstruction A hN P h e Y).adjoint
      ((fourierBasis m t hs (parameters A P).epsilon_pos n :
        holomorphicSpace m t hs (parameters A P).epsilon_pos):Space)‖^2≤
      (1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P))^2*
        modeRatio m t scale (parameters A P).ε (n+1) := by
  rw [cutReconstruction_eq_weighted]
  apply (reconstructed_fourier_gram _ m t hs (parameters A P).epsilon_pos n).trans
  apply mul_le_mul_of_nonneg_right _ (modeRatio_nonneg m t (n+1) scale (parameters A P).epsilon_pos)
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (AsymptoticCylinderTerminal.projection_norm_le Y) (norm_nonneg _)).trans
  simpa only [one_mul] using reconstruction_norm_le A hN P h e

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- The actual cutoff observation has the original O(k) Fourier trace
majorant, uniformly in cutoff height and observation stack. -/
theorem cut_observation_trace_bound (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY : Y≤(parameters A P).ε) (L : Space →L[ℂ] J)
    (m t : ℕ) {scale : ℝ} (hs : 0<scale) :
    let U := holomorphicSpace m t hs (parameters A P).epsilon_pos
    let b := fourierBasis m t hs (parameters A P).epsilon_pos
    let Q := holomorphicOperator (cutReconstruction A hN P h e Y) L
      (cutReconstruction_norm_ge A hN P h e Y hY) U
    Summable (fun n => (⟪Q (b n),b n⟫_ℂ).re) ∧
      trace b Q≤(1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P))^2*
        (1+majorantConstant t scale (parameters A P).ε)*(m+2:ℕ) :=
  holomorphic_trace_bound _ L (cutReconstruction_norm_ge A hN P h e Y hY)
    _ _ m t hs (parameters A P).epsilon_pos (sq_nonneg _)
    (cutReconstruction_fourier_gram A hN P h e Y m t hs)

#print axioms cutReconstruction_eq_weighted
#print axioms cutReconstruction_fourier_gram
#print axioms cut_observation_trace_bound

end AsymptoticReconstructedCount
