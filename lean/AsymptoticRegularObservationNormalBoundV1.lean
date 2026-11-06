module

public import AsymptoticRegularObservationNormalFamilyV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem completedNormal_norm_le (P R : H →L[ℂ] H) (L : H →L[ℂ] J)
    (BR BL : ℝ) (hP : ‖P‖≤1) (hR : ‖R‖≤BR) (hL : ‖L‖≤BL) :
    ‖completedNormal P R L‖≤BR^2+(BL*BR)^2+2 := by
  have hL0 : 0≤BL := (norm_nonneg L).trans hL
  have hLR : ‖L.comp R‖≤BL*BR :=
    (opNorm_comp_le _ _).trans (mul_le_mul hL hR (norm_nonneg R) hL0)
  have hn : ‖normal R L‖≤BR^2+(BL*BR)^2 := by
    apply (norm_add_le _ _).trans
    rw [norm_adjoint_comp_self,norm_adjoint_comp_self]
    simpa only [pow_two] using add_le_add (pow_le_pow_left₀ (norm_nonneg R) hR 2)
      (pow_le_pow_left₀ (norm_nonneg (L.comp R)) hLR 2)
  have h₁ : ‖normal R L+1‖≤BR^2+(BL*BR)^2+1 :=
    (norm_add_le _ _).trans (add_le_add hn ContinuousLinearMap.norm_id_le)
  exact (norm_sub_le _ _).trans ((add_le_add h₁ hP).trans_eq (by ring))

#print axioms completedNormal_norm_le

end AsymptoticObservation

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction AsymptoticRegularCertificate

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def observationsBound (hN : 0<N) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε) (t : ℕ) : ℝ :=
  ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Space)).symm.toContinuousLinearMap‖*
    ∑ i,AsymptoticRegularObservationRows.rowBound hN (r i) (hs i) hε t

/-- A single upper bound for the completed normal family, independent
of orbit root, sector and holomorphic weight. -/
noncomputable def wholeNormalBound (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) : ℝ :=
  let P' := AsymptoticReconstructedCount.parameters A P
  let BR := 1+2*AsymptoticCertificateOperators.terminalConstant A P'
  let BL := observationsBound hN r s hs P'.epsilon_pos (P'.s+4)
  BR^2+(BL*BR)^2+2

theorem wholeNormal_norm_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    ‖wholeNormal A hN P r s hs e z‖≤wholeNormalBound A hN P r s hs := by
  apply AsymptoticObservation.completedNormal_norm_le
  · exact highProjection_norm_le A _ z
  · exact includedFull_norm_le A hN _ (multiplier e) (fun q _ => multiplier_norm e q) z
      (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z)
  · exact observations_norm_le hN r s hs _ _ e z

#print axioms wholeNormal_norm_le

end AsymptoticRegularObservation
