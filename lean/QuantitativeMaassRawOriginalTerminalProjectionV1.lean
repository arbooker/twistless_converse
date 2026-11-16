module

public import QuantitativeMaassRawOriginalSourceKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns ContinuousLinearMap
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)

/-- The original source projection transported back to the normalized terminal. -/
def terminalSourceProjection :=
  let S := AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
  S.adjoint.comp ((originalSourceProjection A P e).comp S)

theorem terminalSourceProjection_fixes
    (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
    (hg : AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε g∈
      originalSourceKernel A P e) :
    terminalSourceProjection A P e g=g := by
  have hp := (originalSourceKernel A P e).starProjection_eq_self_iff.mpr hg
  change (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε).adjoint
    ((originalSourceKernel A P e).starProjection
      (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε g))=g
  rw [hp]
  exact congrArg (fun T => T g) (AsymptoticCylinderTerminal.ambientLift_adjoint_self
    (AsymptoticReconstructedCount.parameters A P).ε)

theorem terminalSourceProjection_norm : ‖terminalSourceProjection A P e‖≤1 := by
  let S := AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
  have hS : ‖S‖≤1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    simpa only [one_mul] using ((norm_map_iff_adjoint_comp_self S).mpr
      (AsymptoticCylinderTerminal.ambientLift_adjoint_self
        (AsymptoticReconstructedCount.parameters A P).ε) v).le
  change ‖S.adjoint.comp ((originalSourceProjection A P e).comp S)‖≤1
  exact (opNorm_comp_le _ _).trans (by
    rw [adjoint.norm_map]
    calc
      _ ≤ 1*(1*1) := mul_le_mul hS
        ((opNorm_comp_le _ _).trans (mul_le_mul (originalSourceProjection_norm A P e) hS
          (norm_nonneg _) zero_le_one)) (norm_nonneg _) zero_le_one
      _ = 1 := by norm_num)

#print axioms terminalSourceProjection_fixes
#print axioms terminalSourceProjection_norm
end QuantitativeMaass.RawCommonReconstruction
