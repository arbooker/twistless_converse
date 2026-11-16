module

public import QuantitativeMaassCountingMetricPartitionV1
public import AsymptoticQuotientLeftActionV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticNestedQuotients
open scoped ENNReal
namespace QuantitativeMaass

/-- An invariant coefficient evaluated on a rational counting orbit. -/
def regularInvariantValue {β : Type*} (N : ℕ) (c : ℍ→β)
    (hc : ∀ a : gamma N,∀ z,c (a.val • z)=c z) (z : ℍ) : Classes (gamma N)→β :=
  Quotient.lift (fun a => c (a • z)) (by
    intro a b hab
    have hh := hc ⟨b*a⁻¹,QuotientGroup.rightRel_apply.mp hab⟩ (a • z)
    simpa only [mul_smul,inv_smul_smul] using hh.symm)

theorem regularInvariantValue_classOf {β : Type*} (N : ℕ) (c : ℍ→β)
    (hc : ∀ a : gamma N,∀ z,c (a.val • z)=c z) (z : ℍ)
    (a : AsymptoticRationalGroup.Group) :
    regularInvariantValue N c hc z (classOf (gamma N) a)=c (a • z) := rfl

def countingNormalizerEquiv (N : ℕ) (g : quotientNormalizerGroup N) :
    Classes (gamma N)≃Classes (gamma N) :=
  leftMulEquiv (gamma N) g.val
    (fun _ ha => normalizer_conj_mem N g ha)
    (fun _ ha => normalizer_inv_conj_mem N g ha)

/-- The actual scalar cover metric preserves counting-orbit energy for
normalizer-invariant densities. This is the regular counterpart of the
proved quotient-measure partition identity. -/
theorem regular_cover_metric_partition {ι : Type*} [Fintype ι]
    (N : ℕ) (g : ι→quotientNormalizerGroup N) (δ : ℝ) (ν : ℕ)
    (hpos : ∀ z,0<normalizerCoverWeight N g δ ν z) (z : ℍ)
    (F : Classes (gamma N)→ℝ≥0∞)
    (hF : ∀ i q,F (countingNormalizerEquiv N (g i) q)=F q) :
    (∑' q,ENNReal.ofReal
      (regularInvariantValue N (weight N δ ν) (weight_invariant N δ ν) z q*
        regularInvariantValue N (normalizerCoverMetricSquare N g δ ν)
          (normalizerCoverMetricSquare_invariant N g δ ν) z q)*F q)=∑' q,F q := by
  let e := fun i => countingNormalizerEquiv N (g i)
  let w := regularInvariantValue N (weight N δ ν) (weight_invariant N δ ν) z
  have hw (q) : 0≤w q := by
    induction q using Quotient.inductionOn with
    | h a => exact quotientWeight_nonneg N δ ν (a • z)
  have hsum (q) : (∑ i,w (e i q))=
      regularInvariantValue N (normalizerCoverWeight N g δ ν)
        (normalizerCoverWeight_invariant N g δ ν) z q := by
    induction q using Quotient.inductionOn with
    | h a =>
      change (∑ i,weight N δ ν (((g i).val*a) • z))=normalizerCoverWeight N g δ ν (a • z)
      simp only [normalizerCoverWeight,mul_smul]
  have hp (q) : 0<∑ i,w (e i q) := by
    rw [hsum]
    induction q using Quotient.inductionOn with
    | h a => exact hpos (a • z)
  have hmetric (q) : (∑ i,(∑ j,w (e j ((e i).symm q)))⁻¹)=
      regularInvariantValue N (normalizerCoverMetricSquare N g δ ν)
        (normalizerCoverMetricSquare_invariant N g δ ν) z q := by
    simp_rw [hsum]
    induction q using Quotient.inductionOn with
    | h a =>
      change (∑ i,(normalizerCoverWeight N g δ ν (((g i).val⁻¹*a) • z))⁻¹)=
        normalizerCoverMetricSquare N g δ ν (a • z)
      simp only [normalizerCoverMetricSquare,mul_smul]
  have hh := counting_cover_metric_partition e w hw hp F hF
  simp_rw [hmetric] at hh
  exact hh

#print axioms regularInvariantValue_classOf
#print axioms regular_cover_metric_partition
end QuantitativeMaass
