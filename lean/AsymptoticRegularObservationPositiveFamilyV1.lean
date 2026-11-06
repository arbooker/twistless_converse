module

public import AsymptoticRegularObservationInverseV1
public import AsymptoticCompletedObservationV1
public import AsymptoticOrbitRegionAdjointV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction AsymptoticRegularCertificate

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem includedFull_eq_extension_adjoint (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ) :
    includedFull A hN P χ z=
      (includedExtension A hN P χ z).comp (TerminalSpace A P z).subtypeL.adjoint := by
  have he : includedFull A hN P χ z=(includedExtension A hN P χ z).comp
      (AsymptoticOrbitRegion.restrict (AsymptoticCertificateOperators.highStrip P.ε) z) := rfl
  exact he.trans (congrArg (fun T : Space →L[ℂ] TerminalSpace A P z =>
    (includedExtension A hN P χ z).comp T) (AsymptoticOrbitRegion.restrict_eq_adjoint _ _))

variable {ι : Type*} [Fintype ι]

/-- Identification of the existing terminal-source positive operator
with its measurable completed-inverse expression on the fixed space. -/
theorem positive_eq_whole (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let R := includedFull A hN P' (multiplier e) z
    positive A hN P r s hs e z=R.comp ((wholeInverse A hN P r s hs e z).comp R.adjoint) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let S := (TerminalSpace A P' z).subtypeL
  let E := includedExtension A hN P' (multiplier e) z
  let R := includedFull A hN P' (multiplier e) z
  let L := observations hN r s hs P'.epsilon_pos (P'.s+4) e z
  let I := wholeInverse A hN P r s hs e z
  have hS : S.adjoint.comp S=1 := AsymptoticOrbitRegion.adjoint_comp_subtype _ _
  have hP : S.comp S.adjoint=highProjection A P' z := AsymptoticOrbitRegion.subtype_comp_adjoint _ _
  have hF : E.comp S.adjoint=R := (includedFull_eq_extension_adjoint A hN P' (multiplier e) z).symm
  have hM : AsymptoticObservation.completedNormal (S.comp S.adjoint) (E.comp S.adjoint) L=
      wholeNormal A hN P r s hs e z :=
    congrArg₂ (fun P R : Space →L[ℂ] Space => AsymptoticObservation.completedNormal P R L) hP hF
  have hI : I.comp (AsymptoticObservation.completedNormal (S.comp S.adjoint) (E.comp S.adjoint) L)=1 :=
    (congrArg (fun T : Space →L[ℂ] Space => I.comp T) hM).trans (wholeInverse_mul A hN P r s hs e z)
  have hR : ∀ g,‖g‖≤‖E g‖ := includedExtension_norm_ge A hN P' (multiplier e) z
    (lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num))
  have he := AsymptoticObservation.operator_eq_completed S hS E L hR I hI
  exact he.trans (congrArg (fun T : Space →L[ℂ] Space => T.comp (I.comp T.adjoint)) hF)

theorem positive_covariant (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) :
    Covariant (positive A hN P r s hs e) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hk : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1 := fun z =>
    lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num)
  have hR := includedFull_covariant A hN P' (multiplier e) hk
  have he := funext (positive_eq_whole A hN P r s hs e)
  rw [he]
  exact covariant_comp _ _ hR
    (covariant_comp _ _ (wholeInverse_covariant A hN P r s hs e) (covariant_adjoint _ hR))

theorem positive_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N)
    (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (positive A hN P r s hs e z) a b) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hk : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1 := fun z =>
    lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num)
  have hR := includedFull_matrix_measurable A hN P' (multiplier e) hk
  simp only [positive_eq_whole]
  apply matrix_comp_measurable _ _ hR
  intro c d
  apply matrix_comp_measurable _ _ (wholeInverse_matrix_measurable A hN P r s hs e)
  intro u v
  simp only [matrix_adjoint]
  exact Complex.continuous_conj.measurable.comp (hR v u)

#print axioms includedFull_eq_extension_adjoint
#print axioms positive_eq_whole
#print axioms positive_covariant
#print axioms positive_matrix_measurable

end AsymptoticRegularObservation
