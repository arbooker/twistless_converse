module

public import QuantitativeMaassFullRegularExpressionV1
public import QuantitativeHolomorphicRegularSourceV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section

open ContinuousLinearMap AsymptoticSectorSigns QuantitativeHolomorphic AsymptoticFiniteBranch
open AsymptoticCompactObservationCount AsymptoticRegularTrace MeasureTheory
namespace QuantitativeMaass.EulerHilbert.FullTerminal

private theorem extended_isometry_gram {G H K : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : G→L[ℂ]H) (S : G→L[ℂ]K) (hU : U.adjoint.comp U=1) :
    (U.comp S.adjoint).adjoint.comp (U.comp S.adjoint)=S.comp S.adjoint := by
  rw [adjoint_comp,adjoint_adjoint,comp_assoc,←comp_assoc U.adjoint U,hU]
  simp only [one_def,id_comp]

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- The actual raw normalized reconstruction, extended from its terminal source. -/
def normalizedRegularAmbient (e : Sector N) (z : UpperHalfPlane) : RegularSpace→L[ℂ]RegularSpace :=
  (normalizedRegularReconstruction A hN P e z).comp
    (AsymptoticRegularReconstruction.TerminalSpace A
      (AsymptoticReconstructedCount.parameters A P) z).subtypeL.adjoint

theorem normalizedFullExpression_regular_error (e : Sector N) (n j J : ℕ)
    (hJ : 0<J) (z : UpperHalfPlane) :
    ‖regularSum (normalizedReconstructionExpression (scaledFullExpression A hN P e j J) n) z-
      normalizedRegularAmbient A hN P e z‖≤normalizedCutError A P 0 j J n := by
  let S := (AsymptoticRegularReconstruction.TerminalSpace A
    (AsymptoticReconstructedCount.parameters A P) z).subtypeL
  have hS : S.adjoint.comp S=1 :=
    AsymptoticOrbitRegion.adjoint_comp_subtype (G:=AsymptoticRationalGroup.Group)
      (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z
  have he := norm_isometric_transport_difference_le S hS
    (1 : AsymptoticRegularFoldedLow.Space→L[ℂ]AsymptoticRegularFoldedLow.Space)
    ((norm_map_iff_adjoint_comp_self
      (1 : AsymptoticRegularFoldedLow.Space→L[ℂ]AsymptoticRegularFoldedLow.Space)).1 (fun _ => rfl))
    (finiteNormalizedRegularReconstruction A hN P e z n j J)
    (normalizedRegularReconstruction A hN P e z)
  have hh := he.trans (finiteNormalizedRegularReconstruction_error A hN P e z n j J hJ)
  simpa only [one_def,id_comp,normalizedRegularAmbient,normalizedFullExpression_regular,
    normalizedCutError,cutCountReconstructionError,zero_div,zero_mul,add_zero] using hh

/-- The finite expressions prove measurability and covariance of the raw
regular reconstruction; neither property is assumed. -/
theorem normalizedRegularAmbient_regular (e : Sector N) :
    (∀ g h, Measurable (fun z => matrix (normalizedRegularAmbient A hN P e z) g h)) ∧
      Covariant (normalizedRegularAmbient A hN P e) := by
  apply regular_of_uniform_expression_approximation
  intro ε hε
  obtain ⟨n,j,J,hJ,hsmall⟩ := exists_normalizedCutError_lt A P hε
  refine ⟨normalizedReconstructionExpression (scaledFullExpression A hN P e j J) n,?_⟩
  intro z
  exact (normalizedFullExpression_regular_error A hN P e n j J hJ z).trans_lt hsmall

/-- The source Gram is exactly the terminal corner, with no extra height factor. -/
theorem normalizedRegularAmbient_gram (e : Sector N) (z : UpperHalfPlane) :
    (normalizedRegularAmbient A hN P e z).adjoint.comp
      (normalizedRegularAmbient A hN P e z)=
      AsymptoticOrbitDiagonal.corner
        (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z := by
  let U := normalizedRegularReconstruction A hN P e z
  let S := (AsymptoticRegularReconstruction.TerminalSpace A
    (AsymptoticReconstructedCount.parameters A P) z).subtypeL
  have hU : U.adjoint.comp U=1 := (norm_map_iff_adjoint_comp_self U).mp
    (normalizedRegularReconstruction_norm A hN P e z)
  exact (extended_isometry_gram U S hU).trans
    (AsymptoticOrbitRegion.subtype_comp_adjoint _ z)

theorem normalizedRegularAmbient_norm (e : Sector N) (z : UpperHalfPlane) :
    ‖normalizedRegularAmbient A hN P e z‖≤1 := by
  apply opNorm_le_bound _ zero_le_one
  intro x
  change ‖normalizedRegularReconstruction A hN P e z
    ((AsymptoticRegularReconstruction.TerminalSpace A
      (AsymptoticReconstructedCount.parameters A P) z).subtypeL.adjoint x)‖≤1*‖x‖
  apply (normalizedRegularReconstruction_norm A hN P e z _).trans_le
  simpa only [one_mul,Submodule.adjoint_subtypeL] using
    (AsymptoticRegularReconstruction.TerminalSpace A
      (AsymptoticReconstructedCount.parameters A P) z).norm_orthogonalProjectionOnto_apply_le x

/-- The matching raw regular reconstruction has the finite terminal-area
source trace. This is finiteness, not the required quantitative excess decay. -/
theorem normalizedRegularAmbient_trace_gram (e : Sector N) :
    AsymptoticRegularTrace.trace volume (fun z =>
      (normalizedRegularAmbient A hN P e z).adjoint.comp
        (normalizedRegularAmbient A hN P e z))=
      ENNReal.ofReal (AsymptoticReconstructedCount.parameters A P).ε⁻¹ := by
  simp only [normalizedRegularAmbient_gram]
  rw [AsymptoticOrbitDiagonal.trace_corner _
    (AsymptoticCertificateOperators.highStrip_measurable _)]
  exact AsymptoticHyperbolicArea.closed_terminal_area
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos

/-- The full regular reconstruction is controlled by its own terminal
coordinates with the proved certificate constant. -/
theorem normalizedRegular_terminal_control (e : Sector N) (z : UpperHalfPlane)
    (x : AsymptoticRegularReconstruction.TerminalSpace A
      (AsymptoticReconstructedCount.parameters A P) z) :
    ‖x‖≤countReconstructionBound A P*
      ‖AsymptoticOrbitDiagonal.corner
        (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z
        (normalizedRegularReconstruction A hN P e z x)‖ := by
  let R := regularReconstruction A hN P e z
  let c := (countReconstructionBound A P)⁻¹
  let w := inverseSqrtCFC ((c • R).adjoint.comp (c • R)) x
  let g := c • w
  have he : normalizedRegularReconstruction A hN P e z x=R g := by
    change (c • R) w=R (c • w)
    rw [smul_apply,map_smul_of_tower]
  have hk := AsymptoticRegularReconstruction.parameters_contraction A hN P
    (multiplier e) (fun q _ => multiplier_norm e q) z
  have ht := AsymptoticRegularReconstruction.extension_terminal A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e) z
    (hk.trans (by norm_num)) g
  rw [←normalizedRegularReconstruction_norm A hN P e z x,he]
  change ‖R g‖≤countReconstructionBound A P*
    ‖AsymptoticRegularCertificate.highProjection A
      (AsymptoticReconstructedCount.parameters A P) z (R g)‖
  change AsymptoticRegularCertificate.highProjection A
    (AsymptoticReconstructedCount.parameters A P) z (R g)=(g:RegularSpace) at ht
  rw [ht]
  exact R.le_of_opNorm_le (regularReconstruction_bounds A hN P e z).1 g

#print axioms normalizedRegular_terminal_control
#print axioms normalizedFullExpression_regular_error
#print axioms normalizedRegularAmbient_regular
#print axioms normalizedRegularAmbient_gram
#print axioms normalizedRegularAmbient_norm
#print axioms normalizedRegularAmbient_trace_gram
end QuantitativeMaass.EulerHilbert.FullTerminal
