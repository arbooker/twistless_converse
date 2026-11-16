module

public import QuantitativeMaassCanonicalCapSpaceV1
public import QuantitativeMaassProjectionSourcePullbackV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane ContinuousLinearMap AsymptoticSectorSigns
open FinitenessCertificate FinitenessGlobalHeight
open AsymptoticRegularCompactBranch (Space)
namespace QuantitativeMaass.AdmissibleScalarCover
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    {hN : GridAdmissibleGap.Admissible N} (C : AdmissibleScalarCover N hN)
    (e : Sector N) (z : ℍ)
    (hz : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • z))

include hz in
theorem regularCapSpace_cogram_fixed :
    let P' := AsymptoticReconstructedCount.parameters A P
    let R : Space→L[ℂ]Space := EulerHilbert.FullTerminal.normalizedRegularAmbient A hN.1 P e z
    let Qcap : Space→L[ℂ]Space := (C.regularCapSpace P'.epsilon_pos (by omega : 1≤P'.s+3) e z).starProjection
    R*R.adjoint*Qcap=Qcap := by
  intro P' R Qcap
  ext1 v
  have hv := (C.regularCapSpace P'.epsilon_pos (by omega : 1≤P'.s+3) e z).starProjection_apply_mem v
  obtain ⟨f,hf⟩ := hv
  change R (R.adjoint (Qcap v))=Qcap v
  change C.regularCapEmbedding P'.epsilon_pos (by omega : 1≤P'.s+3) e z f=Qcap v at hf
  rw [←hf]
  exact CountingMetric.countingCapLift_normalized_cogram A hN.1 P e z hz f.val f.property

include hz in
theorem regularCapSpace_original_rows
    (r : AsymptoticCompactObservationCount.Row N) (s : Set ℍ) (hs : IsCompact s) :
    let P' := AsymptoticReconstructedCount.parameters A P
    AsymptoticRegularObservationRows.row hN.1 r e hs P'.epsilon_pos (P'.s+3) z*
      (C.regularCapSpace P'.epsilon_pos (by omega : 1≤P'.s+3) e z).starProjection=0 := by
  intro P'
  ext1 v
  have hv := (C.regularCapSpace P'.epsilon_pos (by omega : 1≤P'.s+3) e z).starProjection_apply_mem v
  obtain ⟨f,hf⟩ := hv
  change AsymptoticRegularObservationRows.row hN.1 r e hs P'.epsilon_pos (P'.s+3) z
    ((C.regularCapSpace P'.epsilon_pos (by omega : 1≤P'.s+3) e z).starProjection v)=0
  rw [←hf]
  exact CountingMetric.countingCapLift_rows N P'.epsilon_pos (by omega) hN.1 e z hz f.val f.property r s hs

#print axioms regularCapSpace_cogram_fixed
#print axioms regularCapSpace_original_rows
end QuantitativeMaass.AdmissibleScalarCover
