module

public import QuantitativeNewGapLocalEnergyV1
public import QuantitativeNewGapTotalFrickeV1
public import AsymptoticTotalNewTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticCongruenceStrip AsymptoticNestedQuotients UpperHalfPlane
open scoped lp

def weightedLocalOldEnergy (N : ℕ) (hN : 0<N) (p : ℕ)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) : ℝ := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  exact if hp : p.Prime ∧ p∣N then
    ‖(AsymptoticCongruenceOldSpace.lowerSpace (Nat.div_dvd_of_dvd hp.2) hε ht z).starProjection v‖^2+
    ‖(AsymptoticCongruenceOldSpace.frickeSpace hN (Nat.div_dvd_of_dvd hp.2) hε ht z).starProjection v‖^2
    else 0

theorem weightedLocalOldEnergy_induction (N : ℕ) (hN : 0<N) (p : ℕ)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (f : ℓ²(Classes (gamma N),ℂ)) :
    weightedLocalOldEnergy N hN p hε ht z (AsymptoticCongruenceQuotient.induction N hε ht z f)=
      localOldEnergy N hN p f := by
  classical
  unfold weightedLocalOldEnergy localOldEnergy
  split
  · simp only [AsymptoticCongruenceOldSpace.lowerSpace,AsymptoticCongruenceOldSpace.frickeSpace,
      AsymptoticCongruenceOldSpace.projection_induction,LinearIsometry.norm_map]
  · rfl

/-- Exact projection transport for the literal joint new space. -/
theorem totalNew_induction (N : ℕ) (hN : 0<N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (f : ℓ²(Classes (gamma N),ℂ)) :
    (AsymptoticTotalNewCorner.stripSpace N hN hε ht z).starProjection
      (AsymptoticCongruenceQuotient.induction N hε ht z f)=
      AsymptoticCongruenceQuotient.induction N hε ht z
        ((AsymptoticTotalNewCorner.space N hN).starProjection f) := by
  rw [AsymptoticTotalNewCorner.stripSpace_projection]
  exact QuantitativeEulerOldProjectionBlock.compressed_apply_isometry _ _ f

/-- The full weighted distance is exactly the counting-coset distance,
uniformly in the weight and geometric root. -/
theorem totalNew_induction_distance (N : ℕ) (hN : 0<N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (f : ℓ²(Classes (gamma N),ℂ)) :
    ‖AsymptoticCongruenceQuotient.induction N hε ht z f-
      (AsymptoticTotalNewCorner.stripSpace N hN hε ht z).starProjection
        (AsymptoticCongruenceQuotient.induction N hε ht z f)‖=
      ‖f-(AsymptoticTotalNewCorner.space N hN).starProjection f‖ := by
  rw [totalNew_induction,← map_sub,LinearIsometry.norm_map]

#print axioms weightedLocalOldEnergy_induction
#print axioms totalNew_induction
#print axioms totalNew_induction_distance

end QuantitativeNewGap
