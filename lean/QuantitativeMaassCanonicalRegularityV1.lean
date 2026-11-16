module

public import QuantitativeMaassJointScalarCoverV1
public import QuantitativeEulerEndpointSectorRegularV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight AsymptoticNestedQuotients
open AsymptoticSectorSigns QuantitativeNewGap AsymptoticRegularTrace
open scoped lp ComplexConjugate MatrixGroups
namespace QuantitativeMaass.CountingMetric
variable {ι : Type*} [Fintype ι] [Nonempty ι]
    (N : ℕ) (g : ι→quotientNormalizerGroup N)
    {δ Y : ℝ} (hδ : 0<δ) (hY : 0<Y) {ν : ℕ} (hν : 1≤ν)
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • ((g i).val • z)).im)

theorem metricCompression_matrix
    (P : ℓ²(Classes (gamma N),ℂ)→L[ℂ]ℓ²(Classes (gamma N),ℂ)) (z : ℍ)
    (a b : AsymptoticRationalGroup.Group) :
    matrix (metricCompression N g hδ hY hν hcover P z) a b=
      (amplitude N δ ν (a • z)*((Real.sqrt (weight N δ ν (a • z))*normalizerCoverMetric N g δ ν (a • z):ℝ):ℂ))*
      conj (amplitude N δ ν (b • z)*((Real.sqrt (weight N δ ν (b • z))*normalizerCoverMetric N g δ ν (b • z):ℝ):ℂ))*
      matrix P (classOf (gamma N) a) (classOf (gamma N) b) := by
  rw [metricCompression,AsymptoticCongruenceQuotient.compression_matrix]
  dsimp only [regularMetricDiagonal]
  rw [diagonal_sandwich_matrix]
  change (amplitude N δ ν (a • z)*conj (amplitude N δ ν (b • z)))*
    ((regularCoverCoefficient N g δ ν z (classOf (gamma N) a)*
      conj (regularCoverCoefficient N g δ ν z (classOf (gamma N) b)))*
        matrix P (classOf (gamma N) a) (classOf (gamma N) b))=_
  rw [regularCoverCoefficient_classOf,regularCoverCoefficient_classOf,map_mul]
  ring

/-- The canonical metric projection is a measurable covariant regular family.
This is proved from its literal matrix coefficients and counting-sector symmetry. -/
theorem regularCanonicalProjection_regular (hN : GridAdmissibleGap.Admissible N) (e : Sector N) :
    (∀ a b,Measurable (fun z => matrix (regularCanonicalProjection N g hδ hY hν hcover hN e z) a b)) ∧
      Covariant (regularCanonicalProjection N g hδ hY hν hcover hN e) := by
  let c := fun z : ℍ => amplitude N δ ν z*
    ((Real.sqrt (weight N δ ν z)*normalizerCoverMetric N g δ ν z:ℝ):ℂ)
  have hm : Measurable c := (amplitude_measurable N δ ν).mul
    (Complex.measurable_ofReal.comp (((weight_measurable N δ ν).sqrt).mul (normalizerCoverMetric_measurable N g δ ν)))
  have hmatrix (z : ℍ) (a b : AsymptoticRationalGroup.Group) :
      matrix (regularCanonicalProjection N g hδ hY hν hcover hN e z) a b=
      c (a • z)*conj (c (b • z))*matrix (countingSectorSpace N hN.1 e).starProjection
        (classOf (gamma N) a) (classOf (gamma N) b) :=
    metricCompression_matrix N g hδ hY hν hcover _ z a b
  constructor
  · intro a b
    simp only [hmatrix]
    exact ((hm.comp (AsymptoticRationalGroup.measurePreserving a).measurable).mul
      (Complex.continuous_conj.measurable.comp (hm.comp (AsymptoticRationalGroup.measurePreserving b).measurable))).mul_const _
  · intro z a b k
    simp only [hmatrix,mul_smul]
    have he := QuantitativeEulerEndpointPrepared.countingSector_equivariant N hN.1 e a
      (classOf (gamma N) b) (classOf (gamma N) k)
    simp only [AsymptoticNestedQuotients.rightMulEquiv_classOf] at he
    exact congrArg (fun w : ℂ => c (b • a • z)*conj (c (k • a • z))*w) he.symm

#print axioms metricCompression_matrix
#print axioms regularCanonicalProjection_regular
end QuantitativeMaass.CountingMetric

namespace QuantitativeMaass.AdmissibleScalarCover
local instance (N : ℕ) [NeZero N] : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) := Fintype.ofFinite _
variable {N : ℕ} [NeZero N] {hN : GridAdmissibleGap.Admissible N}
    (C : AdmissibleScalarCover N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)

theorem regularProjection_regular (e : Sector N) :
    (∀ a b,Measurable (fun z => matrix (C.regularProjection hδ hν e z) a b)) ∧
      Covariant (C.regularProjection hδ hν e) :=
  CountingMetric.regularCanonicalProjection_regular N C.family hδ C.height_pos hν C.covers hN e

#print axioms regularProjection_regular
end QuantitativeMaass.AdmissibleScalarCover
