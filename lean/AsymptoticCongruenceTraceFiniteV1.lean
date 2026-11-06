module

public import AsymptoticCongruenceFiniteCoverV1
public import AsymptoticOrbitDensityCoverV1
public import AsymptoticCongruenceProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceQuotient

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticRegularTrace
open scoped ENNReal

/-- The normalized rooted diagonal is a nonnegative orbit density with
total mass one on each congruence orbit. -/
theorem amplitude_ofReal_tsum (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    (∑' g : gamma N,ENNReal.ofReal (‖amplitude N ε t (g.val • z)‖^2))=1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun g => sq_nonneg _)
    (amplitude_hasSum N hε ht z).summable,(amplitude_hasSum N hε ht z).tsum_eq]
  exact ENNReal.ofReal_one

theorem projection_trace_le_cover (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    trace volume (projection N hε ht)≤volume (AsymptoticCongruenceCover.cover N) := by
  have he : trace volume (projection N hε ht)=
      ∫⁻ z : ℍ,ENNReal.ofReal (‖amplitude N ε t z‖^2) := by
    apply lintegral_congr
    intro z
    rw [projection_diagonal,one_smul]
    congr 1
    simpa only [OneMemClass.coe_one,one_smul] using (amplitude_norm_sq N hε ht 1 z).symm
  rw [he]
  exact AsymptoticOrbitDensity.integral_le_cover (G:=gamma N) volume
    (fun g => AsymptoticRationalGroup.measurePreserving g.val)
    (fun z => ENNReal.ofReal (‖amplitude N ε t z‖^2))
    (((amplitude_measurable N ε t).norm.pow_const 2).ennreal_ofReal)
    (amplitude_ofReal_tsum N hε ht) (AsymptoticCongruenceCover.cover N)
    (AsymptoticCongruenceCover.orbit_meets_cover N)

/-- Finiteness of the actual congruence quotient trace, with no supplied
covolume or fundamental-domain hypothesis. Modular reduction and finite
index give a finite-volume orbit cover. -/
theorem projection_trace_finite (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    trace volume (projection N hε ht)<∞ :=
  (projection_trace_le_cover N hε ht).trans_lt (AsymptoticCongruenceCover.cover_volume_finite N hN)

#print axioms amplitude_ofReal_tsum
#print axioms projection_trace_le_cover
#print axioms projection_trace_finite

end AsymptoticCongruenceQuotient
