module

public import AsymptoticFiniteRegularSupportV1
public import AsymptoticRegularFiniteUpperCutoffV1
public import AsymptoticRetainedCylinderV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount (Row)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem regular_finiteCutFull_left_heightStrip (hN : 0<N) (P : Parameters A)
    (χ : ℕ → ℂ) (Y : ℝ) (d : ℕ) (I : Finset ℤ) (z : ℍ) :
    (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip Y) z).comp
      (AsymptoticRegularReconstruction.finiteCutFull A hN P χ Y d I z)=
        AsymptoticRegularReconstruction.finiteCutFull A hN P χ Y d I z := by
  have hf := regularSum_full_left_strip A hN P χ d I z
  rw [regularSum_fullExpression] at hf
  ext1 f
  apply lp.ext
  funext g
  have hfg := congrArg (fun T : RegularSpace →L[ℂ] RegularSpace => T f g) hf
  simp only [regularStripProjection,comp_apply,AsymptoticOrbitDiagonal.corner_apply] at hfg
  simp only [comp_apply,AsymptoticOrbitDiagonal.corner_apply,
    AsymptoticRegularReconstruction.finiteCutFull,AsymptoticRegularHeightCutoff.projection,
    AsymptoticRegularInclusion.inclusion_apply]
  classical
  by_cases hstrip : g • z∈AsymptoticMassTransport.strip
  · by_cases hY : Y≤(g • z).im <;>
      simp [AsymptoticCertificateOperators.highStrip,AsymptoticRegularHeightCutoff.region,hstrip,hY]
  · have hg : AsymptoticRegularReconstruction.finiteFoldFull A hN P χ d I z f g=0 := by
      simpa only [ite_eq_right hstrip] using hfg.symm
    simp [AsymptoticCertificateOperators.highStrip,hstrip,hg]

variable {ι : Type*} [Fintype ι]

theorem regular_finiteAmbient_left_heightStrip (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (e : Sector N) (Y : ℝ) (n d : ℕ) (I : Finset ℤ) (z : ℍ) :
    (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip Y) z).comp
      (AsymptoticRegularObservation.finiteCutPolynomialAmbient A hN P r s hs e Y n d I z)=
        AsymptoticRegularObservation.finiteCutPolynomialAmbient A hN P r s hs e Y n d I z := by
  have he := regular_finiteCutFull_left_heightStrip A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y d I z
  unfold AsymptoticRegularObservation.finiteCutPolynomialAmbient
  rw [← comp_assoc,he]

theorem regular_finiteAmbient_root_zero (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (e : Sector N) (Y : ℝ) (n d : ℕ) (I : Finset ℤ) (z : ℍ)
    (hz : z∉AsymptoticCertificateOperators.highStrip Y) :
    matrix (AsymptoticRegularObservation.finiteCutPolynomialAmbient A hN P r s hs e Y n d I z) 1 1=0 := by
  have hh := congrArg (fun T : RegularSpace →L[ℂ] RegularSpace => T (delta 1) 1)
    (regular_finiteAmbient_left_heightStrip A hN P r s hs e Y n d I z)
  have hone : (1:AsymptoticRationalGroup.Group) • z=z := one_smul _ _
  have hnot : (1:AsymptoticRationalGroup.Group) • z∉AsymptoticCertificateOperators.highStrip Y := by
    rwa [hone]
  simpa only [comp_apply,AsymptoticOrbitDiagonal.corner_apply,ite_eq_right hnot,matrix] using hh.symm

omit [Fintype ι] in
theorem regular_corner_sandwich_root (S : Set ℍ) (z : ℍ) (B : RegularSpace →L[ℂ] RegularSpace) :
    matrix ((AsymptoticOrbitDiagonal.corner S z).comp (B.comp (AsymptoticOrbitDiagonal.corner S z))) 1 1=
      S.indicator (fun _ => matrix B 1 1) z := by
  classical
  by_cases hz : z∈S <;>
    simp [matrix,comp_apply,AsymptoticOrbitDiagonal.corner_delta,AsymptoticOrbitDiagonal.corner_apply,hz]

/-- The regular upper-cut trace equals the common retained branch trace;
the reconstruction has no root diagonal outside its lower-height strip. -/
theorem regular_finiteUpperCut_trace_eq_retained (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (e : Sector N) (Y H : ℝ) (n d : ℕ) (I : Finset ℤ) :
    AsymptoticRegularObservation.finiteUpperCutPolynomialTrace A hN P r s hs e Y H n d I=
      signedTrace volume (fun z => (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        ((AsymptoticRegularObservation.finiteCutPolynomialAmbient A hN P r s hs e Y n d I z).comp
          (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z))) := by
  unfold AsymptoticRegularObservation.finiteUpperCutPolynomialTrace signedTrace
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  rw [AsymptoticRegularUpperCutoff.cut,removeCorner_matrix,regular_corner_sandwich_root]
  have hclosed (T : ℝ) : AsymptoticHyperbolicArea.closedTerminal T=
      AsymptoticCertificateOperators.highStrip T := rfl
  rw [hclosed,retainedRegion_eq_diff]
  classical
  by_cases hY : z∈AsymptoticCertificateOperators.highStrip Y
  · by_cases hH : z∈AsymptoticCertificateOperators.highStrip H <;> simp [hY,hH]
  · have hz := regular_finiteAmbient_root_zero A hN P r s hs e Y n d I z hY
    by_cases hH : z∈AsymptoticCertificateOperators.highStrip H <;> simp [hY,hH,hz]

#print axioms regular_finiteCutFull_left_heightStrip
#print axioms regular_finiteAmbient_left_heightStrip
#print axioms regular_finiteAmbient_root_zero
#print axioms regular_corner_sandwich_root
#print axioms regular_finiteUpperCut_trace_eq_retained

end AsymptoticFiniteBranch
