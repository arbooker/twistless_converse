module

public import AsymptoticRetainedCylinderV1
public import AsymptoticFiniteCylinderPolynomialV1
public import AsymptoticSandwichCutoffV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap InnerProductSpace
open AsymptoticCylinderLift AsymptoticUnweightedKernel AsymptoticCylinder
open AsymptoticObservation AsymptoticDiagonalTrace
open scoped InnerProduct

theorem retained_lift_trace (h : ℕ) {ε : ℝ} (hε : 0<ε) (Y H : ℝ)
    (W : AsymptoticCylinder.Space →L[ℂ] AsymptoticCylinder.Space) :
    let P := AsymptoticRegionL2.projection volume (retainedRegion Y H) (retainedRegion_measurable Y H)
    liftedTrace h hε (P.comp ((lift.toContinuousLinearMap.comp (W.comp lift.toContinuousLinearMap.adjoint)).comp P))=
      trace (fourierBasis (2*h) 0 (by positivity : 0<4*Real.pi) hε)
        (compressedSandwich (retainedProjection Y H) W
          (holomorphicSpace (2*h) 0 (by positivity : 0<4*Real.pi) hε)) := by
  dsimp only
  rw [liftedTrace_eq_sum,compressedSandwich_trace_eq_sum]
  apply tsum_congr
  intro n
  let P := AsymptoticRegionL2.projection volume (retainedRegion Y H) (retainedRegion_measurable Y H)
  have hPa : P.adjoint=P := AsymptoticRegionL2.projection_adjoint _ _ _
  simp only [fourierBasis_apply,modeInSpace,retainedProjection_adjoint]
  change (⟪P (lift (W (lift.toContinuousLinearMap.adjoint (P (lift
      (unitMode (2*h) 0 n (by positivity : 0<4*Real.pi) hε)))))),lift
      (unitMode (2*h) 0 n (by positivity : 0<4*Real.pi) hε)⟫_ℂ).re=_
  rw [← P.adjoint_inner_right,hPa]
  simp only [P,← lift_retainedProjection,AsymptoticCylinderTerminal.adjoint_lift,
    lift.inner_map_map]

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount (Row)

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The retained branch trace is the actual unweighted cylinder trace
of the reconstructed inverse polynomial with both cutoffs. -/
theorem retained_finiteAmbient_trace (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (h : ℕ) (e : Sector N) (Y H : ℝ) (n d : ℕ) (I : Finset ℤ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let R := AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I
    let J := AsymptoticCylinderObservation.finiteCutInversePolynomial A hN P r s hs h e Y n d I
    liftedTrace h P'.epsilon_pos
      (holomorphicSum (retainedExpression Y H (finiteAmbientExpression A hN P r s hs e Y n d I)) (h+1))=
      trace (fourierBasis (2*h) 0 (by positivity : 0<4*Real.pi) P'.epsilon_pos)
        (compressedSandwich (retainedProjection Y H) (R.comp (J.comp R.adjoint))
          (holomorphicSpace (2*h) 0 (by positivity : 0<4*Real.pi) P'.epsilon_pos)) := by
  dsimp only
  rw [holomorphicSum_retainedExpression,holomorphic_corner,holomorphicSum_finiteAmbientExpression]
  exact retained_lift_trace h _ Y H _

#print axioms retained_lift_trace
#print axioms retained_finiteAmbient_trace

end AsymptoticFiniteBranch
