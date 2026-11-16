module

public import QuantitativeMaassCountingMetricIsometryV1
public import QuantitativeMaassPositiveMultiplierEquivV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticNestedQuotients AsymptoticSectorSigns QuantitativeNewGap
open scoped lp
namespace QuantitativeMaass.CountingMetric

variable {ι : Type*} [Fintype ι] (N : ℕ) (g : ι→quotientNormalizerGroup N)

def regularCoverCoefficient (δ : ℝ) (ν : ℕ) (z : ℍ) (q : Classes (gamma N)) : ℂ :=
  (regularInvariantValue N (fun w => Real.sqrt (weight N δ ν w)*normalizerCoverMetric N g δ ν w)
    (by intro a w; rw [weight_invariant,normalizerCoverMetric_invariant]) z q:ℝ)

theorem regularCoverCoefficient_classOf (δ : ℝ) (ν : ℕ) (z : ℍ)
    (a : AsymptoticRationalGroup.Group) :
    regularCoverCoefficient N g δ ν z (classOf (gamma N) a)=
      ((Real.sqrt (weight N δ ν (a • z))*normalizerCoverMetric N g δ ν (a • z):ℝ):ℂ) := rfl

theorem regularCoverCoefficient_sq (δ : ℝ) (ν : ℕ) (z : ℍ) (q : Classes (gamma N)) :
    ‖regularCoverCoefficient N g δ ν z q‖^2=
      regularInvariantValue N (weight N δ ν) (weight_invariant N δ ν) z q*
        regularInvariantValue N (normalizerCoverMetricSquare N g δ ν)
          (normalizerCoverMetricSquare_invariant N g δ ν) z q := by
  induction q using Quotient.inductionOn with
  | h a =>
    change ‖((Real.sqrt (weight N δ ν (a • z))*normalizerCoverMetric N g δ ν (a • z):ℝ):ℂ)‖^2=
      weight N δ ν (a • z)*normalizerCoverMetricSquare N g δ ν (a • z)
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,
      Real.sq_sqrt (quotientWeight_nonneg N δ ν _),normalizerCoverMetric_sq]

variable [Nonempty ι] {δ Y : ℝ} (hδ : 0<δ) (hY : 0<Y) {ν : ℕ} (hν : 1≤ν)
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • ((g i).val • z)).im)

include hδ hY hν hcover in
theorem regularCoverCoefficient_bound (z : ℍ) (q : Classes (gamma N)) :
    ‖regularCoverCoefficient N g δ ν z q‖≤
      Real.sqrt (quotientWeightBound δ)*Real.sqrt ((Fintype.card ι:ℝ)/heightWeightFloor δ ν Y) := by
  induction q using Quotient.inductionOn with
  | h a =>
    change ‖((Real.sqrt (weight N δ ν (a • z))*normalizerCoverMetric N g δ ν (a • z):ℝ):ℂ)‖≤_
    rw [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (show 0≤normalizerCoverMetric N g δ ν (a • z) from Real.sqrt_nonneg _))]
    exact mul_le_mul (Real.sqrt_le_sqrt (quotientWeight_uniform_bound N hδ hν _))
      (normalizerCoverMetric_bounds N g hδ hY hν hcover _).2
      (show 0≤normalizerCoverMetric N g δ ν (a • z) from Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

def regularMetricDiagonal (z : ℍ) : ℓ²(Classes (gamma N),ℂ)→L[ℂ]ℓ²(Classes (gamma N),ℂ) :=
  AsymptoticOrbitDiagonal.operator (regularCoverCoefficient N g δ ν z)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (regularCoverCoefficient_bound N g hδ hY hν hcover z)

/-- The regular scalar-metric embedding uses the literal cap coefficient.
The finite-cover normalization makes it isometric on the canonical sector. -/
def regularMetricSectorIsometry (hN : GridAdmissibleGap.Admissible N)
    (hg : ∀ i,(g i).val∈admissibleNormalizerGroup N hN.1)
    (e : Sector N) (z : ℍ) :
    countingSectorSpace N hN.1 e →ₗᵢ[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  (AsymptoticCongruenceQuotient.induction N hδ hν z).comp
    { toLinearMap := (regularMetricDiagonal N g hδ hY hν hcover z).toLinearMap.comp
        (countingSectorSpace N hN.1 e).subtype
      norm_map' := by
        intro f
        exact countingSector_metric_norm N hN e g hg δ ν
          (fun z => (heightWeightFloor_pos hδ hY ν).trans_le
            (normalizerCoverWeight_lower N g hδ hY hν hcover z)) z
          (regularCoverCoefficient N g δ ν z)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (regularCoverCoefficient_bound N g hδ hY hν hcover z)
          (regularCoverCoefficient_sq N g δ ν z) f.val f.property }

#print axioms regularCoverCoefficient_sq
#print axioms regularCoverCoefficient_bound
#print axioms regularMetricSectorIsometry
end QuantitativeMaass.CountingMetric
