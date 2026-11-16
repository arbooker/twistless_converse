module

public import QuantitativeMaassRawOriginalFiniteTraceV1
public import QuantitativeMaassReconstructedSourceErrorV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns ContinuousLinearMap
open AsymptoticFiniteBranch MeasureTheory
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)

/-- The exact reconstruction's initial projection fixes the all-row source. -/
theorem physicalExact_initial_source :
    (physicalExact A P (NeZero.pos N) e).adjoint.comp
      ((physicalExact A P (NeZero.pos N) e).comp (originalSourceProjection A P e))=
        originalSourceProjection A P e := by
  let V := (EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P e).toContinuousLinearMap
  let S := AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
  have hR : physicalExact A P (NeZero.pos N) e=V.comp S.adjoint := rfl
  have hV : V.adjoint.comp V=1 := (EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P e).adjoint_comp_self
  rw [hR,adjoint_comp,adjoint_adjoint]
  calc
    _ = S.comp ((V.adjoint.comp V).comp (S.adjoint.comp (originalSourceProjection A P e))) := by simp only [comp_assoc]
    _ = S.comp (S.adjoint.comp (originalSourceProjection A P e)) := by rw [hV];rfl
    _ = _ := sourceProjection_left_terminal A P e

/-- The literal finite reconstructed expression approximately fixes the
actual physical original-source projection, with no factor on its limit. -/
theorem reconstructedFilterExpression_source_error (s : ℝ) (T : Expression)
    (hT : ‖holomorphicSum T 0‖≤1) {δ : ℝ}
    (hδ : ‖holomorphicSum T 0*originalSourceProjection A P e-originalSourceProjection A P e‖≤δ) :
    let V := (EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P e).toContinuousLinearMap
    let E := V.comp ((terminalSourceProjection A P e).comp V.adjoint)
    ‖(holomorphicSum (reconstructedFilterExpression A P e s T) 0).comp E-E‖≤δ+Real.exp (-8*s) := by
  intro V E
  have herr := physical_error A P (NeZero.pos N) s e
  change ‖holomorphicSum (expression A P (NeZero.pos N) s e) 0-
    physicalExact A P (NeZero.pos N) e‖≤Real.exp (-8*s)/2 at herr
  rw [norm_sub_rev] at herr
  have hh := reconstructed_source_error
    (physicalExact A P (NeZero.pos N) e) (holomorphicSum (expression A P (NeZero.pos N) s e) 0)
    (originalSourceProjection A P e) (holomorphicSum T 0)
    (physicalExact_norm A P (NeZero.pos N) e) (physical_norm A P (NeZero.pos N) s e)
    (originalSourceProjection_norm A P e) hT (physicalExact_initial_source A P e) hδ
    herr
  dsimp only [E]
  rw [physicalExact_terminalSource_conjugate,reconstructedFilterExpression_physical]
  convert hh using 1
  ring

#print axioms physicalExact_initial_source
#print axioms reconstructedFilterExpression_source_error
end QuantitativeMaass.RawCommonReconstruction
