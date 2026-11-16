module

public import QuantitativeMaassFullRegularFilterTraceV1
public import QuantitativeHolomorphicTerminalTraceAlgebraV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeMaass.EulerHilbert.FullTerminal

open QuantitativeHolomorphic
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount AsymptoticFiniteBranch AsymptoticRegularTrace MeasureTheory
open scoped ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def fullFiniteRegularAmbient (hN : 0<N) (P : Parameters A) (e : Sector N)
    (j J n : ℕ) :=
  regularSum (normalizedReconstructionExpression (scaledFullExpression A hN P e j J) n)

theorem fullFiniteRegularAmbient_norm_le (hN : 0<N) (P : Parameters A) (e : Sector N)
    (j J n : ℕ) (z : UpperHalfPlane) :
    ‖fullFiniteRegularAmbient A hN P e j J n z‖≤1 := by
  rw [fullFiniteRegularAmbient,normalizedFullExpression_regular]
  have hv := finiteNormalizedRegularReconstruction_norm A hN P e z n j J
  have hs : ‖(AsymptoticRegularReconstruction.TerminalSpace A
      (AsymptoticReconstructedCount.parameters A P) z).subtypeL.adjoint‖≤1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    simpa only [one_mul,Submodule.adjoint_subtypeL] using
      (AsymptoticRegularReconstruction.TerminalSpace A
        (AsymptoticReconstructedCount.parameters A P) z).norm_orthogonalProjectionOnto_apply_le v
  exact (opNorm_comp_le _ _).trans ((mul_le_mul hv hs (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

theorem fullFiniteRegularAmbient_right_terminal (hN : 0<N) (P : Parameters A) (e : Sector N)
    (j J n : ℕ) (z : UpperHalfPlane) :
    (fullFiniteRegularAmbient A hN P e j J n z).comp
      (AsymptoticOrbitDiagonal.corner
        (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z)=
      fullFiniteRegularAmbient A hN P e j J n z := by
  let S := (AsymptoticRegularReconstruction.TerminalSpace A
    (AsymptoticReconstructedCount.parameters A P) z).subtypeL
  have hS : S.adjoint.comp S=1 :=
    AsymptoticOrbitRegion.adjoint_comp_subtype (G := AsymptoticRationalGroup.Group) _ z
  have hP : S.comp S.adjoint=AsymptoticOrbitDiagonal.corner
      (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z :=
    AsymptoticOrbitRegion.subtype_comp_adjoint _ z
  let T := finiteNormalizedRegularReconstruction A hN P e z n j J
  have he : fullFiniteRegularAmbient A hN P e j J n z=T.comp S.adjoint :=
    normalizedFullExpression_regular A hN P e n j J z
  calc
    _ = (T.comp S.adjoint).comp (S.comp S.adjoint) := congrArg₂ (fun X Z => X.comp Z) he hP.symm
    _ = T.comp S.adjoint := by
      ext1 v
      have hv := congrArg (fun W => W (S.adjoint v)) hS
      change S.adjoint (S (S.adjoint v))=S.adjoint v at hv
      change T (S.adjoint (S (S.adjoint v)))=T (S.adjoint v)
      exact congrArg T hv
    _ = _ := he.symm

theorem fullFiniteRegularAmbient_gram_trace_finite (hN : 0<N) (P : Parameters A) (e : Sector N)
    (j J n : ℕ) :
    AsymptoticRegularTrace.trace volume (fun z =>
      (fullFiniteRegularAmbient A hN P e j J n z).adjoint.comp
        (fullFiniteRegularAmbient A hN P e j J n z))<∞ := by
  apply AsymptoticHyperbolicArea.closed_terminal_trace_finite
    (C:=1) (AsymptoticReconstructedCount.parameters A P).epsilon_pos
  · intro z
    exact contraction_gram_norm_le _ (fullFiniteRegularAmbient_norm_le A hN P e j J n z)
  · intro z
    have hset : AsymptoticHyperbolicArea.closedTerminal (AsymptoticReconstructedCount.parameters A P).ε=
        AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε := rfl
    rw [hset,comp_assoc]
    exact congrArg (fun W => (fullFiniteRegularAmbient A hN P e j J n z).adjoint.comp W)
      (fullFiniteRegularAmbient_right_terminal A hN P e j J n z)

theorem fullFiniteRegularAmbient_error (hN : 0<N) (P : Parameters A) (e : Sector N)
    (j J n : ℕ) (hJ : 0<J) (z : UpperHalfPlane) :
    ‖fullFiniteRegularAmbient A hN P e j J n z-
      normalizedRegularAmbient A hN P e z‖≤normalizedCutError A P 0 j J n :=
  normalizedFullExpression_regular_error A hN P e n j J hJ z

#print axioms fullFiniteRegularAmbient_norm_le
#print axioms fullFiniteRegularAmbient_right_terminal
#print axioms fullFiniteRegularAmbient_gram_trace_finite

end QuantitativeMaass.EulerHilbert.FullTerminal
