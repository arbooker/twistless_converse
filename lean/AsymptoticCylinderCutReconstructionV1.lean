module

public import AsymptoticCylinderHeightCutoffV1
public import AsymptoticReconstructedCountV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticReconstructedCount

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Reconstruction followed by the extra capped-weight inclusion. -/
noncomputable def includedReconstruction (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N) :
    AsymptoticCylinderTerminal.Space (parameters A P).ε →L[ℂ] Space :=
  (inclusion (parameters A P).epsilon_pos).comp (reconstruction A hN P h e)

/-- Actual cylinder reconstruction with the low-height output removed. -/
noncomputable def cutReconstruction (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N) (Y : ℝ) :
    AsymptoticCylinderTerminal.Space (parameters A P).ε →L[ℂ] Space :=
  (AsymptoticCylinderTerminal.projection Y).comp (includedReconstruction A hN P h e)

theorem includedReconstruction_terminal (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (g : AsymptoticCylinderTerminal.Space (parameters A P).ε) :
    AsymptoticCylinderTerminal.projection (parameters A P).ε (includedReconstruction A hN P h e g)=(g:Space) := by
  change AsymptoticCylinderTerminal.projection (parameters A P).ε
    (inclusion (parameters A P).epsilon_pos (reconstruction A hN P h e g))=_
  rw [AsymptoticCylinderTerminal.projection_inclusion]
  exact AsymptoticCylinderReconstruction.extension_terminal A hN (parameters A P) (multiplier e) (h+1)
    (lt_trans (parameters_hyperbolic_contraction A hN P (multiplier e)
      (fun q _ => multiplier_norm e q) (h+1)) (by norm_num)) g

theorem includedReconstruction_norm_le (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N) :
    ‖includedReconstruction A hN P h e‖≤1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P) := by
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (inclusion_norm_le (parameters A P).epsilon_pos) (norm_nonneg _)).trans
  simpa only [one_mul] using reconstruction_norm_le A hN P h e

theorem cutReconstruction_terminal (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY : Y≤(parameters A P).ε) (g : AsymptoticCylinderTerminal.Space (parameters A P).ε) :
    AsymptoticCylinderTerminal.projection (parameters A P).ε (cutReconstruction A hN P h e Y g)=(g:Space) := by
  have he := congrArg (fun T : Space →L[ℂ] Space => T (includedReconstruction A hN P h e g))
    (AsymptoticCylinderTerminal.projection_comp_of_le hY)
  exact he.trans (includedReconstruction_terminal A hN P h e g)

theorem cutReconstruction_norm_ge (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY : Y≤(parameters A P).ε) (g : AsymptoticCylinderTerminal.Space (parameters A P).ε) :
    ‖g‖≤‖cutReconstruction A hN P h e Y g‖ := by
  calc
    ‖g‖=‖AsymptoticCylinderTerminal.projection (parameters A P).ε (cutReconstruction A hN P h e Y g)‖ := by
      rw [cutReconstruction_terminal A hN P h e Y hY g]
      rfl
    _ ≤ _ := by
      apply ((AsymptoticCylinderTerminal.projection (parameters A P).ε).le_opNorm _).trans
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (AsymptoticCylinderTerminal.projection_norm_le (parameters A P).ε)
        (norm_nonneg (cutReconstruction A hN P h e Y g))

theorem cutReconstruction_norm_le (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N) (Y : ℝ) :
    ‖cutReconstruction A hN P h e Y‖≤1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P) := by
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (AsymptoticCylinderTerminal.projection_norm_le Y) (norm_nonneg _)).trans
  simpa only [one_mul] using includedReconstruction_norm_le A hN P h e

theorem cutReconstruction_error (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY : 0≤Y) :
    ‖includedReconstruction A hN P h e-cutReconstruction A hN P h e Y‖≤
      Y/(parameters A P).ε*(1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P)) := by
  have he : includedReconstruction A hN P h e-cutReconstruction A hN P h e Y=
      (inclusion (parameters A P).epsilon_pos-
        (AsymptoticCylinderTerminal.projection Y).comp (inclusion (parameters A P).epsilon_pos)).comp
          (reconstruction A hN P h e) := by
    apply ContinuousLinearMap.ext
    intro g
    rfl
  rw [he]
  apply (opNorm_comp_le _ _).trans
  exact mul_le_mul (AsymptoticCylinderTerminal.inclusion_cut_error (parameters A P).epsilon_pos hY)
    (reconstruction_norm_le A hN P h e) (norm_nonneg _) (div_nonneg hY (parameters A P).epsilon_pos.le)

#print axioms includedReconstruction_terminal
#print axioms includedReconstruction_norm_le
#print axioms cutReconstruction_terminal
#print axioms cutReconstruction_norm_ge
#print axioms cutReconstruction_norm_le
#print axioms cutReconstruction_error

end AsymptoticReconstructedCount
