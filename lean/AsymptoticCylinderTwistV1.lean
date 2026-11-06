module

public import AsymptoticTwistObservationFormulaV1
public import AsymptoticReconstructedCountV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderTwist

open UpperHalfPlane Set FinitenessCertificate FinitenessGlobalHeight
open AsymptoticSectorSigns AsymptoticCylinder AsymptoticTwistObservation

/-- The compact twist observation on the cylinder, with its exact strip
realization supplied by the isometric lift. -/
noncomputable def operator (N q : ℕ) (hN : 0<N) (hq : 0<q)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t m : ℕ) (χ : ℂ) :
    Space →L[ℂ] AsymptoticHyperbolicSlash.Space :=
  (residual N q hN hq hs hε t m χ).comp AsymptoticCylinderLift.lift.toContinuousLinearMap

theorem operator_norm_le (N q : ℕ) (hN : 0<N) (hq : 0<q)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t m : ℕ) (e : Sector N) :
    ‖operator N q hN hq hs hε t m (multiplier e q)‖≤
      translationBound q hs hε t+reflectionBound N q hN hq hs hε t := by
  have hl : ‖AsymptoticCylinderLift.lift.toContinuousLinearMap‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖AsymptoticCylinderLift.lift f‖≤1*‖f‖
    rw [AsymptoticCylinderLift.lift_norm,one_mul]
  have hb := residual_norm_le N q hN hq hs hε t m (multiplier e q)
  rw [multiplier_norm,one_mul] at hb
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left hl (norm_nonneg _)).trans (by simpa using hb))

/-- Every actual Euler sector satisfies each compact twist observation.
The functional equation is obtained from the sector definition. -/
theorem sector_annihilated {N Q : ℕ} {hQ : 0<Q} {A : Certificate N Q hQ}
    (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N) (q : ℕ) (hq : 0<q)
    {s : Set ℍ} (hs : IsCompact s)
    (w : holomorphicSpace (2*h) (P.s+4) (by positivity : 0<4*Real.pi) P.epsilon_pos)
    (hw : w∈eulerCylinderSector P h e) :
    operator N q hN hq hs P.epsilon_pos (P.s+4) (h+1) (multiplier e q) (w:Space)=0 := by
  obtain ⟨a,rfl⟩ := hw
  have hFE := AsymptoticSectorReconstruction.coefficientSector_laws hN hq
    (multiplier e) (h+1) (h+1+P.s) a.val (a.property.1 q hq)
  exact residual_eq_zero N q hN hq hs P.epsilon_pos (P.s+4) (h+1) (multiplier e q)
    (FinitenessFourierConstruction.fourier a.val.val) (FinitenessFourierConstruction.periodic a.val.val)
    (hFE q (dvd_refl q)) _
    (AsymptoticCylinderLift.lift_fourierMap h (P.s+4) (h+1+P.s) P.epsilon_pos (by omega) a.val)

#print axioms operator_norm_le
#print axioms sector_annihilated

end AsymptoticCylinderTwist
