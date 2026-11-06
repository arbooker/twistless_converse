module

public import AsymptoticRegularCutReconstructionV1
public import AsymptoticRegularObservationNormalBoundV1
public import AsymptoticNormalPerturbationV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem completedNormal_sub_bound (P R S : H →L[ℂ] H) (L : H →L[ℂ] J)
    (BR BL δ : ℝ) (hR : ‖R‖≤BR) (hS : ‖S‖≤BR) (hL : ‖L‖≤BL) (hd : ‖R-S‖≤δ) :
    ‖completedNormal P R L-completedNormal P S L‖≤(2*BR)*(1+BL^2)*δ := by
  have hR0 : 0≤BR := (norm_nonneg R).trans hR
  have hs : ‖R‖+‖S‖≤2*BR := by linarith
  have hl : 1+‖L‖^2≤1+BL^2 := add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg L) hL 2)
  apply (completedNormal_sub_norm_le P R S L).trans
  exact mul_le_mul (mul_le_mul hs hl (by positivity) (by positivity)) hd (norm_nonneg _) (by positivity)

end AsymptoticObservation

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace InnerProductSpace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction AsymptoticRegularCertificate

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def cutNormal (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (z : ℍ) : Space →L[ℂ] Space :=
  let P' := AsymptoticReconstructedCount.parameters A P
  AsymptoticObservation.completedNormal (highProjection A P' z)
    (cutFull A hN P' (multiplier e) Y z) (observations hN r s hs P'.epsilon_pos (P'.s+4) e z)

theorem cutNormal_coercive (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (z : ℍ) (x : Space) :
    ‖x‖^2≤(⟪cutNormal A hN P r s hs e Y z x,x⟫_ℂ).re := by
  apply AsymptoticObservation.completedNormal_coercive
  · exact AsymptoticOrbitDiagonal.corner_adjoint _ _
  · exact AsymptoticOrbitDiagonal.corner_idempotent _ _
  · exact highProjection_norm_le A _ z
  · exact cutFull_terminal A hN _ (multiplier e) Y hY z
      (lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num))

theorem cutNormal_norm_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (z : ℍ) :
    ‖cutNormal A hN P r s hs e Y z‖≤wholeNormalBound A hN P r s hs := by
  apply AsymptoticObservation.completedNormal_norm_le
  · exact highProjection_norm_le A _ z
  · exact cutFull_norm_le A hN _ (multiplier e) (fun q _ => multiplier_norm e q) Y z
      (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z)
  · exact observations_norm_le hN r s hs _ _ e z

noncomputable def cutErrorBound (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℝ) : ℝ :=
  let P' := AsymptoticReconstructedCount.parameters A P
  let BR := 1+2*AsymptoticCertificateOperators.terminalConstant A P'
  let BL := observationsBound hN r s hs P'.epsilon_pos (P'.s+4)
  (2*BR)*(1+BL^2)*(Y/P'.ε*BR)

theorem cutNormal_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (hY : 0≤Y) (z : ℍ) :
    ‖wholeNormal A hN P r s hs e z-cutNormal A hN P r s hs e Y z‖≤cutErrorBound A hN P r s hs Y := by
  apply AsymptoticObservation.completedNormal_sub_bound
  · exact includedFull_norm_le A hN _ (multiplier e) (fun q _ => multiplier_norm e q) z
      (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z)
  · exact cutFull_norm_le A hN _ (multiplier e) (fun q _ => multiplier_norm e q) Y z
      (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z)
  · exact observations_norm_le hN r s hs _ _ e z
  · exact cutFull_error A hN _ (multiplier e) (fun q _ => multiplier_norm e q) Y hY z
      (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z)

#print axioms AsymptoticObservation.completedNormal_sub_bound
#print axioms cutNormal_coercive
#print axioms cutNormal_norm_le
#print axioms cutNormal_error

end AsymptoticRegularObservation
