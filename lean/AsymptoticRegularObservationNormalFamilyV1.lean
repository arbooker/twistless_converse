module

public import AsymptoticRegularObservationNormalV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction AsymptoticRegularCertificate

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem wholeNormal_covariant (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) :
    Covariant (wholeNormal A hN P r s hs e) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hk : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1 := fun z =>
    lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num)
  have hc := includedFull_covariant A hN P' (multiplier e) hk
  have he := funext (wholeNormal_formula A hN P r s hs e)
  rw [he]
  apply covariant_add
  · apply covariant_comp
    · exact covariant_adjoint _ hc
    · apply covariant_comp
      · exact covariant_add _ _ covariant_one (gram_covariant hN r s hs P'.epsilon_pos (P'.s+4) e)
      · exact hc
  · exact covariant_add _ _ covariant_one
      (covariant_smul _ _ (AsymptoticOrbitDiagonal.corner_covariant _))

theorem wholeNormal_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N)
    (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (wholeNormal A hN P r s hs e z) a b) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hk : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1 := fun z =>
    lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num)
  have hm := includedFull_matrix_measurable A hN P' (multiplier e) hk
  simp only [wholeNormal_formula]
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

#print axioms wholeNormal_covariant
#print axioms wholeNormal_matrix_measurable

end AsymptoticRegularObservation
