module

public import QuantitativeMaassCountingOrbitRowsV1
public import QuantitativeMaassRegularMetricAmplitudeV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticNestedQuotients
open AsymptoticCongruenceWeight AsymptoticCompactBranch AsymptoticMassTransport
open AsymptoticSectorSigns QuantitativeNewGap ContinuousLinearMap
open scoped lp
namespace QuantitativeMaass.CountingMetric

variable (N : ℕ) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)

def capLiftCoefficient (z : ℍ) (q : Classes (gamma N)) : ℂ :=
  (regularInvariantValue N (fun w => Real.sqrt (weight N δ ν w))
    (fun a w => by rw [weight_invariant]) z q:ℝ)

include hδ hν in
theorem capLiftCoefficient_bound (z : ℍ) (q : Classes (gamma N)) :
    ‖capLiftCoefficient N (δ:=δ) (ν:=ν) z q‖≤Real.sqrt (quotientWeightBound δ) := by
  induction q using Quotient.inductionOn with
  | h a =>
    change ‖((Real.sqrt (weight N δ ν (a • z)):ℝ):ℂ)‖≤_
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (quotientWeight_uniform_bound N hδ hν _)

/-- The literal cap lift is bounded because the congruence orbit weight is
uniformly bounded. No lower bound for that weight is required. -/
def countingCapLift (z : ℍ) :
    ℓ²(Classes (gamma N),ℂ)→L[ℂ]AsymptoticRegularCompactBranch.Space :=
  (AsymptoticCongruenceQuotient.induction N hδ hν z).toContinuousLinearMap.comp
    (AsymptoticOrbitDiagonal.operator (capLiftCoefficient N (δ:=δ) (ν:=ν) z)
      (Real.sqrt_nonneg _) (capLiftCoefficient_bound N hδ hν z))

theorem countingCapLift_apply (z : ℍ) (f : ℓ²(Classes (gamma N),ℂ))
    (a : AsymptoticRationalGroup.Group) :
    countingCapLift N hδ hν z f a=
      strip.indicator (fun w => (cap δ ν w:ℂ)*f (classOf (gamma N) a)) (a • z) := by
  classical
  change amplitude N δ ν (a • z)*
    (((Real.sqrt (weight N δ ν (a • z)):ℝ):ℂ)*f (classOf (gamma N) a))=_
  by_cases ha : a • z∈strip
  · rw [amplitude,Set.indicator_of_mem ha,Set.indicator_of_mem ha,Complex.ofReal_div]
    have hw : ((Real.sqrt (weight N δ ν (a • z)):ℝ):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (weight_pos N hδ hν _)).ne'
    field_simp
  · simp only [amplitude,Set.indicator_of_notMem ha,zero_mul]

theorem countingCapLift_decode (z : ℍ) (f : ℓ²(Classes (gamma N),ℂ))
    (a : AsymptoticRationalGroup.Group) :
    AsymptoticOrbitDecode.decode δ ν z (countingCapLift N hδ hν z f) a=
      f (classOf (gamma N) a) :=
  decode_cap_lift N hδ ν z f _ (countingCapLift_apply N hδ hν z f) a

/-- Every original compact row annihilates the bounded cap lift of the
actual counting new/sign space, at a free rational orbit. -/
theorem countingCapLift_rows (hN : 0<N) (e : Sector N) (z : ℍ)
    (hz : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • z))
    (f : ℓ²(Classes (gamma N),ℂ)) (hf : f∈countingSectorSpace N hN e)
    (r : AsymptoticCompactObservationCount.Row N) (s : Set ℍ) (hs : IsCompact s) :
    AsymptoticRegularObservationRows.row hN r e hs hδ ν z
      (countingCapLift N hδ hν z f)=0 :=
  countingSector_cap_rows N hN e hδ ν z hz f hf _ (countingCapLift_decode N hδ hν z f) r s hs

#print axioms capLiftCoefficient_bound
#print axioms countingCapLift_apply
#print axioms countingCapLift_decode
#print axioms countingCapLift_rows
end QuantitativeMaass.CountingMetric
