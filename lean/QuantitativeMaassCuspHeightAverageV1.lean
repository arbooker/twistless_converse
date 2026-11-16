module

public import QuantitativeMaassFiberAverageV1
public import QuantitativeMaassCuspRestrictionV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups InnerProductSpace

namespace QuantitativeMaass

/-- The exact height marginal of hyperbolic volume on a local region. -/
def heightMeasure (K : Set ℍ) : Measure ℝ := (volume.restrict K).map UpperHalfPlane.im

def localHeightAverage (K : Set ℍ) :
    Lp ℂ 2 (volume.restrict K) →L[ℂ] Lp ℂ 2 (heightMeasure K) :=
  FiberAverage.average (volume.restrict K) UpperHalfPlane.im continuous_im.measurable

/-- Actual bounded height-fiber averaging in every integral cusp chart. -/
def cuspHeightAverage (N : ℕ) (s : SL(2,ℤ)) (K : Set ℍ) (hK : IsCompact K) :
    AutomorphicSpace N →L[ℂ] Lp ℂ 2 (heightMeasure K) :=
  (localHeightAverage K).comp (cuspRestriction N s K hK)

theorem localHeightAverage_norm_le (K : Set ℍ) : ‖localHeightAverage K‖≤1 :=
  FiberAverage.average_norm_le _ _ _

theorem cuspHeightAverage_norm_le (N : ℕ) (s : SL(2,ℤ)) (K : Set ℍ) (hK : IsCompact K) :
    ‖cuspHeightAverage N s K hK‖≤‖cuspRestriction N s K hK‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (localHeightAverage_norm_le K) (norm_nonneg (cuspRestriction N s K hK))

/-- Exact local averaging identity for every quotient L2 state. -/
theorem cuspHeightAverage_pairing (N : ℕ) (s : SL(2,ℤ)) (K : Set ℍ) (hK : IsCompact K)
    (g : Lp ℂ 2 (heightMeasure K)) (f : AutomorphicSpace N) :
    inner ℂ g (cuspHeightAverage N s K hK f)=
      ∫ Z in K, star (g Z.im)*(cuspRestriction N s K hK f) Z :=
  FiberAverage.average_pairing_integral _ _ _ g _

/-- On actual invariant representatives, the bounded operator averages the
literal cusp pullback. This is an identity, not an assumed intertwining law. -/
theorem cuspHeightAverage_representative_pairing (N : ℕ) (s : SL(2,ℤ)) (K : Set ℍ)
    (hK : IsCompact K) (g : Lp ℂ 2 (heightMeasure K))
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    inner ℂ g (cuspHeightAverage N s K hK
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f))=
      ∫ Z in K, star (g Z.im)*f.val (cuspAction s Z) := by
  rw [cuspHeightAverage_pairing]
  apply integral_congr_ae
  filter_upwards [cuspRestriction_representative_ae N s K hK f] with Z hZ
  rw [hZ]

#print axioms cuspHeightAverage_norm_le
#print axioms cuspHeightAverage_pairing
#print axioms cuspHeightAverage_representative_pairing

end QuantitativeMaass
