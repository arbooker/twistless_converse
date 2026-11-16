module

public import QuantitativeMaassLocalTestPairingV1
public import QuantitativeMaassPoincareLocalizationV1
public import AsymptoticL2MultiplierV1

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson

namespace QuantitativeMaass

/-- The adjoint of actual local restriction is literal Poincare summation
on every compact smooth local test. -/
theorem quotientRestriction_adjoint_localSeed (N : ℕ) (K : Set ℍ)
    (hK : IsCompact K) (u : SmoothUpperSeed)
    (hu : tsupport (upperFunction u.toFun) ⊆ K) :
    (quotientRestriction N K hK hK.measurableSet).adjoint (localSeedVector K u) =
      poincareSeedVector N u := by
  apply ext_inner_right ℂ
  intro f
  rw [adjoint_inner_left]
  exact quotientRestriction_pairing N K hK hK.measurableSet u hu f

/-- A bounded local transfer between two actual quotient L2 spaces.
It is restriction, multiplication by the compact cutoff, and the
adjoint restriction; the cutoff need not be invariant under either group. -/
def crossQuotientLocalization (N M : ℕ) (K : Set ℍ) (hK : IsCompact K)
    (b : SmoothUpperSeed) {B : ℝ} (hB : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B) :
    AutomorphicSpace M →L[ℂ] AutomorphicSpace N :=
  (quotientRestriction N K hK hK.measurableSet).adjoint.comp
    ((AsymptoticL2Multiplier.operator (C := B) (upperFunction b.toFun)
      (upperFunction_continuous b.smooth).aestronglyMeasurable
      (by filter_upwards [ae_restrict_mem hK.measurableSet] with z hz; exact hB z hz)).comp
      (quotientRestriction M K hK hK.measurableSet))

/-- The completed L2 transfer has exactly the compact cross-Poincare
action used by the cross-quotient Green identity. -/
theorem crossQuotientLocalization_on_seed (N M : ℕ) (K : Set ℍ) (hK : IsCompact K)
    (b : SmoothUpperSeed) {B : ℝ} (hB : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hb : tsupport (upperFunction b.toFun) ⊆ K) (v : SmoothUpperSeed) :
    crossQuotientLocalization N M K hK b hB (poincareSeedVector M v) =
      poincareSeedVector N (b.localized (congruencePoincareCartesian M v.toFun)
        (congruencePoincareCartesian_smooth M v.smooth v.compact)) := by
  let U := b.localized (congruencePoincareCartesian M v.toFun)
    (congruencePoincareCartesian_smooth M v.smooth v.compact)
  let A : Lp ℂ 2 (volume.restrict K) →L[ℂ] Lp ℂ 2 (volume.restrict K) :=
    AsymptoticL2Multiplier.operator (C := B) (upperFunction b.toFun)
      (upperFunction_continuous b.smooth).aestronglyMeasurable
      (by filter_upwards [ae_restrict_mem hK.measurableSet] with z hz; exact hB z hz)
  have hU : tsupport (upperFunction U.toFun) ⊆ K :=
    tsupport_mul_subset_right.trans hb
  have he : A (quotientRestriction M K hK hK.measurableSet (poincareSeedVector M v)) =
      localSeedVector K U := by
    apply Lp.ext
    have hr := quotientRestriction_representative_ae M K hK hK.measurableSet
      ⟨_, poincareSeed_representative M v⟩
    filter_upwards [AsymptoticL2Multiplier.operator_coeFn (C := B) (upperFunction b.toFun)
        (upperFunction_continuous b.smooth).aestronglyMeasurable
        (show ∀ᵐ z ∂volume.restrict K, ‖upperFunction b.toFun z‖ ≤ B from
          by filter_upwards [ae_restrict_mem hK.measurableSet] with z hz; exact hB z hz)
        (quotientRestriction M K hK hK.measurableSet (poincareSeedVector M v)),
      hr, (localSeedMemLp K U).coeFn_toLp] with z ha hr hu
    change (quotientRestriction M K hK hK.measurableSet (poincareSeedVector M v)) z =
      poincareSum (G := gamma M) (upperFunction v.toFun) z at hr
    change (localSeedVector K U) z = upperFunction U.toFun z at hu
    rw [ha, hr, hu]
    change upperFunction b.toFun z * poincareSum (G := gamma M) (upperFunction v.toFun) z =
      upperFunction (congruencePoincareCartesian M v.toFun) z * upperFunction b.toFun z
    rw [congruencePoincareCartesian_represents, mul_comm]
  change (quotientRestriction N K hK hK.measurableSet).adjoint
    (A (quotientRestriction M K hK hK.measurableSet (poincareSeedVector M v))) = _
  rw [he]
  exact quotientRestriction_adjoint_localSeed N K hK U hU

#print axioms quotientRestriction_adjoint_localSeed
#print axioms crossQuotientLocalization_on_seed

end QuantitativeMaass
