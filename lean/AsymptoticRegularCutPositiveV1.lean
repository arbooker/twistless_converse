module

public import AsymptoticRegularCutInverseV1
public import AsymptoticRegularTerminalTraceV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularReconstruction

open UpperHalfPlane MeasureTheory AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticRegularCertificate
open AsymptoticRegularFoldedLow (Space)
open scoped ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem cutFull_eq_extension_adjoint (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (Y : ℝ) (z : ℍ) :
    cutFull A hN P χ Y z=(cutExtension A hN P χ Y z).comp (TerminalSpace A P z).subtypeL.adjoint :=
  congrArg (fun T : Space →L[ℂ] Space => (AsymptoticRegularHeightCutoff.projection Y z).comp T)
    (AsymptoticRegularObservation.includedFull_eq_extension_adjoint A hN P χ z)

theorem cutFull_gram_trace_finite (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (Y : ℝ) (hK : ∀ z,‖low A hN P χ (P.s+3) z‖<1/2) :
    trace volume (fun z => (cutFull A hN P χ Y z).adjoint.comp (cutFull A hN P χ Y z))<∞ :=
  (trace_gram_comp_le volume (AsymptoticRegularHeightCutoff.projection Y) (includedFull A hN P χ)
    (AsymptoticRegularHeightCutoff.projection_norm_le Y)).trans_lt
      (includedFull_gram_trace_finite A hN P χ hχ hK)

#print axioms cutFull_eq_extension_adjoint
#print axioms cutFull_gram_trace_finite

end AsymptoticRegularReconstruction

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction AsymptoticRegularCertificate

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def cutPositive (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (z : ℍ) : Space →L[ℂ] Space :=
  let R := cutFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y z
  R.comp ((cutInverse A hN P r s hs e Y z).comp R.adjoint)

/-- The cutoff sandwich is exactly the positive observation operator
constructed from the cutoff terminal extension and the unchanged rows. -/
theorem cutPositive_eq_operator (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (z : ℍ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    cutPositive A hN P r s hs e Y z=AsymptoticObservation.operator
      (cutExtension A hN P' (multiplier e) Y z) (observations hN r s hs P'.epsilon_pos (P'.s+4) e z)
      (cutExtension_norm_ge A hN P' (multiplier e) Y hY z
        (lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num))) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let S := (TerminalSpace A P' z).subtypeL
  let E := cutExtension A hN P' (multiplier e) Y z
  let R := cutFull A hN P' (multiplier e) Y z
  let L := observations hN r s hs P'.epsilon_pos (P'.s+4) e z
  let I := cutInverse A hN P r s hs e Y z
  have hS : S.adjoint.comp S=1 := AsymptoticOrbitRegion.adjoint_comp_subtype _ _
  have hP : S.comp S.adjoint=highProjection A P' z := AsymptoticOrbitRegion.subtype_comp_adjoint _ _
  have hF : E.comp S.adjoint=R := (cutFull_eq_extension_adjoint A hN P' (multiplier e) Y z).symm
  have hM : AsymptoticObservation.completedNormal (S.comp S.adjoint) (E.comp S.adjoint) L=
      cutNormal A hN P r s hs e Y z :=
    congrArg₂ (fun P R : Space →L[ℂ] Space => AsymptoticObservation.completedNormal P R L) hP hF
  have hI : I.comp (AsymptoticObservation.completedNormal (S.comp S.adjoint) (E.comp S.adjoint) L)=1 :=
    (congrArg (fun T : Space →L[ℂ] Space => I.comp T) hM).trans (cutInverse_mul A hN P r s hs e Y hY z)
  have hR : ∀ g,‖g‖≤‖E g‖ := cutExtension_norm_ge A hN P' (multiplier e) Y hY z
    (lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num))
  have he := AsymptoticObservation.operator_eq_completed S hS E L hR I hI
  exact (he.trans (congrArg (fun T : Space →L[ℂ] Space => T.comp (I.comp T.adjoint)) hF)).symm

theorem cutPositive_isPositive (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (z : ℍ) :
    (cutPositive A hN P r s hs e Y z).IsPositive := by
  rw [cutPositive_eq_operator A hN P r s hs e Y hY z]
  exact AsymptoticObservation.operator_positive _ _ _

theorem cutPositive_norm_le_one (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (z : ℍ) :
    ‖cutPositive A hN P r s hs e Y z‖≤1 := by
  rw [cutPositive_eq_operator A hN P r s hs e Y hY z]
  exact AsymptoticObservation.operator_norm_le_one _ _ _

theorem cutPositive_covariant (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) : Covariant (cutPositive A hN P r s hs e Y) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hk : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1 := fun z =>
    lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num)
  have hr := cutFull_covariant A hN P' (multiplier e) Y hk
  exact covariant_comp _ _ hr (covariant_comp _ _ (cutInverse_covariant A hN P r s hs e Y hY) (covariant_adjoint _ hr))

theorem cutPositive_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (cutPositive A hN P r s hs e Y z) a b) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hk : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1 := fun z =>
    lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num)
  have hm := cutFull_matrix_measurable A hN P' (multiplier e) Y hk
  exact matrix_comp_measurable _ _ hm
    (matrix_comp_measurable _ _ (cutInverse_matrix_measurable A hN P r s hs e Y hY)
      (matrix_adjoint_measurable _ hm)) a b

#print axioms cutPositive_eq_operator
#print axioms cutPositive_isPositive
#print axioms cutPositive_norm_le_one
#print axioms cutPositive_covariant
#print axioms cutPositive_matrix_measurable

end AsymptoticRegularObservation
