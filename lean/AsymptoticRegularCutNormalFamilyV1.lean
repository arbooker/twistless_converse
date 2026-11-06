module

public import AsymptoticRegularCutNormalV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction AsymptoticRegularCertificate

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem cutNormal_formula (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (z : ℍ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let R := cutFull A hN P' (multiplier e) Y z
    cutNormal A hN P r s hs e Y z=
      R.adjoint.comp ((1+gram hN r s hs P'.epsilon_pos (P'.s+4) e z).comp R)+
        (1+(-1:ℂ) • highProjection A P' z) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let R := cutFull A hN P' (multiplier e) Y z
  let L := observations hN r s hs P'.epsilon_pos (P'.s+4) e z
  change AsymptoticObservation.normal R L+1-highProjection A P' z=
    R.adjoint.comp ((1+L.adjoint.comp L).comp R)+(1+(-1:ℂ) • highProjection A P' z)
  have he := congrArg (fun T : Space →L[ℂ] Space => T+1-highProjection A P' z)
    (AsymptoticObservation.normal_formula R L)
  have hneg : (-1:ℂ) • highProjection A P' z= -highProjection A P' z :=
    neg_one_smul ℂ (highProjection A P' z)
  apply he.trans
  calc
    _ = R.adjoint.comp ((1+L.adjoint.comp L).comp R)+(1+ -highProjection A P' z) := by abel
    _ = _ := congrArg (fun T : Space →L[ℂ] Space =>
      R.adjoint.comp ((1+L.adjoint.comp L).comp R)+(1+T)) hneg.symm

theorem cutNormal_covariant (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) :
    Covariant (cutNormal A hN P r s hs e Y) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hk : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1 := fun z =>
    lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num)
  have hc := cutFull_covariant A hN P' (multiplier e) Y hk
  have he := funext (cutNormal_formula A hN P r s hs e Y)
  rw [he]
  apply covariant_add
  · apply covariant_comp
    · exact covariant_adjoint _ hc
    · apply covariant_comp
      · exact covariant_add _ _ covariant_one (gram_covariant hN r s hs P'.epsilon_pos (P'.s+4) e)
      · exact hc
  · exact covariant_add _ _ covariant_one
      (covariant_smul _ _ (AsymptoticOrbitDiagonal.corner_covariant _))

theorem cutNormal_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (cutNormal A hN P r s hs e Y z) a b) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hk : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1 := fun z =>
    lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num)
  have hm := cutFull_matrix_measurable A hN P' (multiplier e) Y hk
  simp only [cutNormal_formula]
  apply matrix_add_measurable
  · intro c d
    apply matrix_comp_measurable
    · intro u v
      simp only [matrix_adjoint]
      exact Complex.continuous_conj.measurable.comp (hm v u)
    · intro u v
      apply matrix_comp_measurable
      · intro j k
        exact matrix_add_measurable _ _ (fun _ _ => measurable_const)
          (gram_matrix_measurable hN r s hs P'.epsilon_pos (P'.s+4) e) j k
      · exact hm
  · intro c d
    apply matrix_add_measurable
    · intro u v
      exact measurable_const
    · intro u v
      exact matrix_smul_measurable _ _
        (AsymptoticOrbitDiagonal.corner_matrix_measurable
          (fun g => (AsymptoticRationalBranches.action_continuous g).measurable)
          (AsymptoticCertificateOperators.highStrip_measurable P'.ε)) u v

#print axioms cutNormal_covariant
#print axioms cutNormal_matrix_measurable

end AsymptoticRegularObservation
