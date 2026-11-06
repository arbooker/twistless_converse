module

public import AsymptoticFiniteBranchRowsV1
public import AsymptoticFiniteBranchWeightV1
public import AsymptoticFiniteExpressionTraceV1
public import AsymptoticRegularFiniteAmbientTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane Set ContinuousLinearMap
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns

variable {ι : Type*} [Fintype ι]

noncomputable def gramExpression (r : ι → Expression) : Expression :=
  sumExpressions Finset.univ (fun i => composeExpression (adjointExpression (r i)) (r i))

theorem holomorphicSum_gramExpression (r : ι → Expression) (m : ℕ) :
    holomorphicSum (gramExpression r) m=
      ∑ i,(holomorphicSum (r i) m).adjoint.comp (holomorphicSum (r i) m) := by
  rw [gramExpression,holomorphicSum_sumExpressions]
  simp only [holomorphicSum_compose,holomorphicSum_adjoint]

theorem regularSum_gramExpression (r : ι → Expression) (z : ℍ) :
    regularSum (gramExpression r) z=∑ i,(regularSum (r i) z).adjoint.comp (regularSum (r i) z) := by
  rw [gramExpression,regularSum_sumExpressions]
  exact Finset.sum_congr rfl (fun i _ =>
    (regularSum_compose (adjointExpression (r i)) (r i) z).trans
      (congrArg (fun T : RegularSpace →L[ℂ] RegularSpace => T.comp (regularSum (r i) z))
        (regularSum_adjoint (r i) z)))

noncomputable def completedNormalExpression (R G : Expression) (P : Branch) : Expression :=
  composeExpression (adjointExpression R) (composeExpression ([identity]++G) R)++
    ([identity]++scaleExpression (-1) [P])

theorem regularSum_completedNormalExpression (R G : Expression) (P : Branch) (z : ℍ) :
    regularSum (completedNormalExpression R G P) z=
      (regularSum R z).adjoint.comp ((1+regularSum G z).comp (regularSum R z))+
        (1+(-1:ℂ) • regular P z) := by
  let End := RegularSpace →L[ℂ] RegularSpace
  have h1 : regularSum [identity] z=(1:End) :=
    (show regularSum [identity] z=regular identity z from add_zero _).trans (regular_identity z)
  have hP : regularSum [P] z=regular P z := add_zero _
  have hG : regularSum ([identity]++G) z=1+regularSum G z :=
    (regularSum_append [identity] G z).trans (congrArg (fun T : End => T+regularSum G z) h1)
  have hGR : regularSum (composeExpression ([identity]++G) R) z=
      (1+regularSum G z).comp (regularSum R z) :=
    (regularSum_compose ([identity]++G) R z).trans
      (congrArg (fun T : End => T.comp (regularSum R z)) hG)
  have hmain : regularSum (composeExpression (adjointExpression R) (composeExpression ([identity]++G) R)) z=
      (regularSum R z).adjoint.comp ((1+regularSum G z).comp (regularSum R z)) :=
    (regularSum_compose (adjointExpression R) (composeExpression ([identity]++G) R) z).trans
      (congrArg₂ (fun U V : End => U.comp V) (regularSum_adjoint R z) hGR)
  have hscale : regularSum (scaleExpression (-1) [P]) z=(-1:ℂ) • regular P z :=
    (regularSum_scale (-1) [P] z).trans (congrArg (fun T : End => (-1:ℂ) • T) hP)
  have hrest : regularSum ([identity]++scaleExpression (-1) [P]) z=1+(-1:ℂ) • regular P z :=
    (regularSum_append [identity] (scaleExpression (-1) [P]) z).trans (congrArg₂ (fun U V : End => U+V) h1 hscale)
  exact (regularSum_append _ _ z).trans (congrArg₂ (fun U V : End => U+V) hmain hrest)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def finiteNormalExpression (hN : 0<N) (P : Parameters A)
    (r : ι → AsymptoticCompactObservationCount.Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ) : Expression :=
  let P' := AsymptoticReconstructedCount.parameters A P
  completedNormalExpression (cutFullExpression A hN P' (multiplier e) Y d I)
    (gramExpression (fun i => rowExpression hN (r i) e (hs i) P'.epsilon_pos (P'.s+4)))
    (corner (AsymptoticCertificateOperators.highStrip P'.ε) (AsymptoticCertificateOperators.highStrip_measurable P'.ε))

theorem regularSum_finiteNormalExpression (hN : 0<N) (P : Parameters A)
    (r : ι → AsymptoticCompactObservationCount.Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ) (z : ℍ) :
    regularSum (finiteNormalExpression A hN P r s hs e Y d I) z=
      AsymptoticRegularObservation.finiteCutNormal A hN P r s hs e Y d I z := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let R := cutFullExpression A hN P' (multiplier e) Y d I
  let G := gramExpression (fun i => rowExpression hN (r i) e (hs i) P'.epsilon_pos (P'.s+4))
  let J := corner (AsymptoticCertificateOperators.highStrip P'.ε)
    (AsymptoticCertificateOperators.highStrip_measurable P'.ε)
  let End := RegularSpace →L[ℂ] RegularSpace
  let F (R G J : End) := R.adjoint.comp ((1+G).comp R)+(1+(-1:ℂ) • J)
  have hR := regularSum_cutFullExpression A hN P' (multiplier e) Y d I z
  have hG : regularSum G z=AsymptoticRegularObservation.gram hN r s hs P'.epsilon_pos (P'.s+4) e z := by
    apply (regularSum_gramExpression _ z).trans
    apply Eq.trans _ (AsymptoticRegularObservation.gram_eq_sum hN r s hs P'.epsilon_pos (P'.s+4) e z).symm
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun T : End => T.adjoint.comp T) (regularSum_rowExpression hN (r i) e (hs i) P'.epsilon_pos (P'.s+4) z)
  have hJ : regular J z=AsymptoticRegularCertificate.highProjection A P' z := regular_corner _ _ z
  have hmain : F (regularSum R z) (regularSum G z) (regular J z)=
      F (AsymptoticRegularReconstruction.finiteCutFull A hN P' (multiplier e) Y d I z)
        (AsymptoticRegularObservation.gram hN r s hs P'.epsilon_pos (P'.s+4) e z)
        (AsymptoticRegularCertificate.highProjection A P' z) :=
    (congrArg₂ (fun U V : End => F U V (regular J z)) hR hG).trans
      (congrArg (fun T : End => F
        (AsymptoticRegularReconstruction.finiteCutFull A hN P' (multiplier e) Y d I z)
        (AsymptoticRegularObservation.gram hN r s hs P'.epsilon_pos (P'.s+4) e z) T) hJ)
  exact (regularSum_completedNormalExpression R G J z).trans
    (hmain.trans (AsymptoticRegularObservation.finiteCutNormal_formula A hN P r s hs e Y d I z).symm)

noncomputable def finiteAmbientExpression (hN : 0<N) (P : Parameters A)
    (r : ι → AsymptoticCompactObservationCount.Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (e : Sector N) (Y : ℝ) (n d : ℕ) (I : Finset ℤ) : Expression :=
  let R := cutFullExpression A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y d I
  composeExpression R (composeExpression
    (inversePolynomialExpression (AsymptoticSharedApproximation.normalBound A hN P r s hs)
      (finiteNormalExpression A hN P r s hs e Y d I) n) (adjointExpression R))

theorem regularSum_finiteAmbientExpression (hN : 0<N) (P : Parameters A)
    (r : ι → AsymptoticCompactObservationCount.Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (e : Sector N) (Y : ℝ) (n d : ℕ) (I : Finset ℤ) (z : ℍ) :
    regularSum (finiteAmbientExpression A hN P r s hs e Y n d I) z=
      AsymptoticRegularObservation.finiteCutPolynomialAmbient A hN P r s hs e Y n d I z := by
  let R := cutFullExpression A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y d I
  let C := AsymptoticSharedApproximation.normalBound A hN P r s hs
  let M := finiteNormalExpression A hN P r s hs e Y d I
  let End := RegularSpace →L[ℂ] RegularSpace
  let R' := AsymptoticRegularReconstruction.finiteCutFull A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y d I z
  have hR : regularSum R z=R' := regularSum_cutFullExpression A hN _ (multiplier e) Y d I z
  have hP : regularSum (inversePolynomialExpression C M n) z=
      AsymptoticCoerciveNeumann.polynomial C (AsymptoticRegularObservation.finiteCutNormal A hN P r s hs e Y d I z) n :=
    (regularSum_inversePolynomial C M n z).trans
      (congrArg (fun T : End => AsymptoticCoerciveNeumann.polynomial C T n)
        (regularSum_finiteNormalExpression A hN P r s hs e Y d I z))
  have hA : regularSum (adjointExpression R) z=R'.adjoint :=
    (regularSum_adjoint R z).trans (congrArg (fun T : End => T.adjoint) hR)
  have hmiddle := (regularSum_compose (inversePolynomialExpression C M n) (adjointExpression R) z).trans
    (congrArg₂ (fun U V : End => U.comp V) hP hA)
  exact (regularSum_compose R _ z).trans (congrArg₂ (fun U V : End => U.comp V) hR hmiddle)

/-- The retained finite reconstruction polynomial has the actual regular
observation operator as its limiting rooted trace. The remaining cylinder
transport is kept separate from this branch-kernel limit. -/
theorem finiteAmbientExpression_trace_tendsto (hN : 0<N) (P : Parameters A)
    (r : ι → AsymptoticCompactObservationCount.Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (e : Sector N) {Y : ℝ} (hY : 0<Y) (H : ℝ) (n d : ℕ) (I : Finset ℤ) :
    Filter.Tendsto (fun h => AsymptoticUnweightedKernel.liftedTrace h
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      (holomorphicSum (retainedExpression Y H (finiteAmbientExpression A hN P r s hs e Y n d I)) (h+1))/(2*h+2:ℕ))
      Filter.atTop (nhds (AsymptoticRegularTrace.signedTrace MeasureTheory.volume
        (fun z => (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
          ((AsymptoticRegularObservation.finiteCutPolynomialAmbient A hN P r s hs e Y n d I z).comp
            (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)))/(4*Real.pi))) := by
  have ht := retainedExpression_trace_tendsto
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos hY H
    (finiteAmbientExpression A hN P r s hs e Y n d I)
  have he : regularSum (retainedExpression Y H (finiteAmbientExpression A hN P r s hs e Y n d I))=
      (fun z => (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        ((AsymptoticRegularObservation.finiteCutPolynomialAmbient A hN P r s hs e Y n d I z).comp
          (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z))) := by
    funext z
    exact (regularSum_retainedExpression Y H _ z).trans
      (congrArg (fun T : RegularSpace →L[ℂ] RegularSpace =>
        (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
          (T.comp (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)))
        (regularSum_finiteAmbientExpression A hN P r s hs e Y n d I z))
  exact he ▸ ht

#print axioms holomorphicSum_gramExpression
#print axioms regularSum_gramExpression
#print axioms regularSum_completedNormalExpression
#print axioms regularSum_finiteNormalExpression
#print axioms regularSum_finiteAmbientExpression
#print axioms finiteAmbientExpression_trace_tendsto

end AsymptoticFiniteBranch
