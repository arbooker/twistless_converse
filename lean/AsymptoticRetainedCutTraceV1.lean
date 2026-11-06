module

public import AsymptoticRetainedTraceTransportV1
public import AsymptoticCylinderFiniteUpperCutoffV1
public import AsymptoticWeightedProjectionLimitV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap
open AsymptoticCylinder AsymptoticObservation AsymptoticDiagonalTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount (Row)

theorem retainedProjection_comp_upper (Y H : ℝ) :
    (retainedProjection Y H).comp (upperProjection Y)=retainedProjection Y H := by
  rw [retainedProjection_eq_region,upperProjection_eq_terminal]
  exact AsymptoticRegionL2.projection_comp_of_subset _ _ _ _ _ (fun _ hz => hz.1)

theorem upper_comp_retainedProjection (Y H : ℝ) :
    (upperProjection Y).comp (retainedProjection Y H)=retainedProjection Y H := by
  have hh := congrArg ContinuousLinearMap.adjoint (retainedProjection_comp_upper Y H)
  simpa only [adjoint_comp,retainedProjection_adjoint,
    upperProjection,AsymptoticRegionL2.projection_adjoint] using hh

theorem retained_trace_eq_localized (m t : ℕ) {scale ε : ℝ} (hscale : 0<scale) (hε : 0<ε)
    (Y H : ℝ) (W : AsymptoticCylinder.Space →L[ℂ] AsymptoticCylinder.Space) :
    trace (fourierBasis m t hscale hε)
      (compressedSandwich (retainedProjection Y H) W (holomorphicSpace m t hscale hε))=
    AsymptoticCylinderModeComparison.localizedTrace m t hscale hε Y
      ((retainedProjection Y H).comp (W.comp (retainedProjection Y H))) := by
  unfold AsymptoticCylinderModeComparison.localizedTrace
  congr 1
  unfold compressedSandwich
  rw [retainedProjection_adjoint]
  have hP : (upperProjection Y).adjoint=upperProjection Y :=
    AsymptoticRegionL2.projection_adjoint _ _ _
  rw [hP]
  ext1 x
  have hl := congrArg (fun T : AsymptoticCylinder.Space →L[ℂ] AsymptoticCylinder.Space =>
    T (W (retainedProjection Y H (x:AsymptoticCylinder.Space)))) (upper_comp_retainedProjection Y H)
  have hr := congrArg (fun T : AsymptoticCylinder.Space →L[ℂ] AsymptoticCylinder.Space =>
    T (x:AsymptoticCylinder.Space)) (retainedProjection_comp_upper Y H)
  simp only [comp_apply,Submodule.subtypeL_apply] at hl hr ⊢
  rw [hr,hl]

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

omit [Fintype ι] in
theorem finiteCutReconstruction_left_height (hN : 0<N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ) :
    (upperProjection Y).comp (AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I)=
      AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I := by
  rw [upperProjection_eq_terminal]
  ext1 f
  let g := AsymptoticReconstructedCount.finiteReconstruction A hN P h e d I f
  have he := congrArg (fun T : AsymptoticCylinder.Space →L[ℂ] AsymptoticCylinder.Space =>
    T (AsymptoticCylinderTerminal.projection Y g))
    (AsymptoticCylinderTerminal.projection_comp_inclusion
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos Y)
  change AsymptoticCylinderTerminal.projection Y (AsymptoticCylinder.inclusion (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    (AsymptoticCylinderTerminal.projection Y g))=_
  simp only [comp_apply] at he
  rw [he]
  have hp := AsymptoticRegionL2.projection_idempotent AsymptoticCylinder.measure
    (AsymptoticCylinderTerminal.region Y) (AsymptoticCylinderTerminal.region_measurable Y) g
  change AsymptoticCylinderTerminal.projection Y (AsymptoticCylinderTerminal.projection Y g)=
    AsymptoticCylinderTerminal.projection Y g at hp
  rw [hp]
  rfl

/-- The actual upper-cut trace is the retained cylinder sandwich. -/
theorem finiteUpperCut_trace_eq_retained (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (h : ℕ) (e : Sector N) (Y H : ℝ) (n d : ℕ) (I : Finset ℤ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let R := AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I
    let J := AsymptoticCylinderObservation.finiteCutInversePolynomial A hN P r s hs h e Y n d I
    AsymptoticCylinderObservation.finiteUpperCutPolynomialTrace A hN P r s hs h e Y H n d I=
      trace (fourierBasis (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos)
        (compressedSandwich (retainedProjection Y H) (R.comp (J.comp R.adjoint))
          (holomorphicSpace (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos)) := by
  let R := AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I
  have he : removePart (upperProjection H) R=(retainedProjection Y H).comp R := by
    rw [retainedProjection,comp_assoc,finiteCutReconstruction_left_height]
    rfl
  dsimp only
  unfold AsymptoticCylinderObservation.finiteUpperCutPolynomialTrace upperCutTrace
  rw [he]
  congr 1
  ext1 x
  simp only [compressedSandwich,adjoint_comp,comp_apply,R]

#print axioms retainedProjection_comp_upper
#print axioms upper_comp_retainedProjection
#print axioms retained_trace_eq_localized
#print axioms finiteCutReconstruction_left_height
#print axioms finiteUpperCut_trace_eq_retained

end AsymptoticFiniteBranch
