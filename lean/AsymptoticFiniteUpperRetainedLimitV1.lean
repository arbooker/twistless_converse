module

public import AsymptoticRetainedWeightedLimitV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap Filter
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount (Row)
open scoped Topology

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The actual finite, weighted cylinder trace converges to the retained
regular trace. All branch transport and weighted Fourier replacement
estimates in this statement are proved, rather than hypotheses. -/
theorem finiteUpperCut_trace_tendsto_retained (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (e : Sector N) {Y : ℝ} (hY : 0<Y) (H : ℝ) (n d : ℕ) (I : Finset ℤ) :
    Tendsto (fun h : ℕ =>
      AsymptoticCylinderObservation.finiteUpperCutPolynomialTrace A hN P r s hs h e Y H n d I/(2*h+2:ℕ))
      atTop (𝓝 (AsymptoticRegularTrace.signedTrace volume
        (fun z => (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
          ((AsymptoticRegularObservation.finiteCutPolynomialAmbient A hN P r s hs e Y n d I z).comp
            (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)))/(4*Real.pi))) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let W (h : ℕ) :=
    (AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I).comp
      ((AsymptoticCylinderObservation.finiteCutInversePolynomial A hN P r s hs h e Y n d I).comp
        (AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I).adjoint)
  have hd := retained_trace_difference_tendsto (P'.s+4) P'.epsilon_pos hY H W
    (fun h => finiteCylinderPolynomial_norm_le A hN P r s hs h e Y n d I)
  have ht := finiteAmbientExpression_trace_tendsto A hN P r s hs e hY H n d I
  simp only [retained_finiteAmbient_trace] at ht
  have hh := hd.add ht
  simp only [zero_add] at hh
  convert hh using 1
  funext h
  rw [finiteUpperCut_trace_eq_retained]
  dsimp only [W,P']
  ring

#print axioms finiteUpperCut_trace_tendsto_retained

end AsymptoticFiniteBranch
