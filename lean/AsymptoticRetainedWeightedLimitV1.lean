module

public import AsymptoticRetainedCutTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane Set ContinuousLinearMap Filter
open AsymptoticCylinder AsymptoticObservation AsymptoticDiagonalTrace
open AsymptoticCylinderModeComparison
open scoped Topology

theorem retained_sandwich_norm_le (Y H : ℝ)
    (W : AsymptoticCylinder.Space →L[ℂ] AsymptoticCylinder.Space) :
    ‖(retainedProjection Y H).comp (W.comp (retainedProjection Y H))‖≤‖W‖ := by
  have hp := retainedProjection_norm_le Y H
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
  rw [one_mul]
  apply (opNorm_comp_le _ _).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg W)

/-- The weighted/unweighted replacement tends to zero after division by
k, for any uniformly bounded family and fixed retained heights. -/
theorem retained_trace_difference_tendsto (t : ℕ) {ε Y B : ℝ}
    (hε : 0<ε) (hY : 0<Y) (H : ℝ)
    (W : ℕ → AsymptoticCylinder.Space →L[ℂ] AsymptoticCylinder.Space)
    (hW : ∀ h,‖W h‖≤B) :
    Tendsto (fun h : ℕ =>
      (trace (fourierBasis (2*h) t (by positivity : 0<4*Real.pi) hε)
        (compressedSandwich (retainedProjection Y H) (W h)
          (holomorphicSpace (2*h) t (by positivity : 0<4*Real.pi) hε))-
      trace (fourierBasis (2*h) 0 (by positivity : 0<4*Real.pi) hε)
        (compressedSandwich (retainedProjection Y H) (W h)
          (holomorphicSpace (2*h) 0 (by positivity : 0<4*Real.pi) hε)))/(2*h+2:ℕ))
      atTop (𝓝 0) := by
  have hk : Tendsto (fun h : ℕ => ((2*h+2:ℕ):ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    exact tendsto_atTop.mpr (fun b => eventually_atTop.mpr ⟨b,fun h hh => by omega⟩)
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hk)
  have hl := hi.const_mul
    (2*B*Real.sqrt (localizedErrorBound t (4*Real.pi) Y)*Real.sqrt (massSlope t (4*Real.pi) Y))
  simp only [mul_zero] at hl
  apply squeeze_zero_norm _ hl
  intro h
  rw [retained_trace_eq_localized,retained_trace_eq_localized]
  convert normalized_localizedTrace_difference_bound (2*h) t
    (by positivity : 0<4*Real.pi) hε hY
    ((retainedProjection Y H).comp ((W h).comp (retainedProjection Y H)))
    ((retained_sandwich_norm_le Y H (W h)).trans (hW h)) using 1 <;> push_cast <;> rfl

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount (Row)

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem finiteCylinderPolynomial_norm_le (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (h : ℕ) (e : Sector N) (Y : ℝ) (n d : ℕ) (I : Finset ℤ) :
    let R := AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I
    let J := AsymptoticCylinderObservation.finiteCutInversePolynomial A hN P r s hs h e Y n d I
    ‖R.comp (J.comp R.adjoint)‖≤
      (1+2*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P))^2*
        AsymptoticCoerciveNeumann.polynomialBound (AsymptoticSharedApproximation.normalBound A hN P r s hs)
          (AsymptoticCylinderObservation.normalBound A hN P r s hs) n := by
  let R := AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I
  let J := AsymptoticCylinderObservation.finiteCutInversePolynomial A hN P r s hs h e Y n d I
  have hR := AsymptoticReconstructedCount.finiteCutReconstruction_norm_le A hN P h e Y d I
  have hJ := AsymptoticCoerciveNeumann.polynomial_norm_le_of_bound
    (AsymptoticSharedApproximation.normalBound A hN P r s hs) _
    (AsymptoticCylinderObservation.finiteCutNormal_norm_le A hN P r s hs h e Y d I) n
  have hRa : ‖R.adjoint‖≤1+2*AsymptoticCertificateOperators.terminalConstant A
      (AsymptoticReconstructedCount.parameters A P) := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hR
  have hj : ‖J‖≤_ := hJ
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul hR ((opNorm_comp_le _ _).trans
    (mul_le_mul hj hRa (norm_nonneg _) ((norm_nonneg J).trans hj)))
      (norm_nonneg _) ((norm_nonneg R).trans hR)).trans_eq
  ring

#print axioms retained_sandwich_norm_le
#print axioms retained_trace_difference_tendsto
#print axioms finiteCylinderPolynomial_norm_le

end AsymptoticFiniteBranch
