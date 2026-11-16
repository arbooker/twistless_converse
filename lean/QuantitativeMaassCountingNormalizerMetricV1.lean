module

public import QuantitativeMaassCountingHalfSignV1
public import QuantitativeMaassAdmissibleNormalizerSubgroupV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticIntegralSubgroup AsymptoticCongruenceStrip AsymptoticCongruenceLabels AsymptoticFreshMatrices
open AsymptoticNestedQuotients AsymptoticSectorSigns QuantitativeNewGap
open scoped lp ENNReal
namespace QuantitativeMaass.CountingMetric

/-- Every admissible normalizer preserves the modulus of an actual
counting new/sign vector; the dyadic case comes from its repeated-prime row. -/
theorem countingSector_modulus (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (e : Sector N) (f : ℓ²(Classes (gamma N),ℂ))
    (hf : f∈countingSectorSpace N hN.1 e) :
    admissibleNormalizerGroup N hN.1≤modulusStabilizer (fun a => f (classOf (gamma N) a)) := by
  let K := modulusStabilizer (fun a => f (classOf (gamma N) a))
  have hK : gamma N≤K := gamma_le_modulusStabilizer N f
  have hW : frickeLabel N hN.1∈K := by
    intro g
    have hh := congrArg norm (countingSector_fricke N hN.1 e f hf g)
    simpa only [norm_mul,sign_norm,one_mul] using hh
  have hS (p : SimplePrime N) : (simpleAtkinGeneratorIndex N hN.1 p).val∈K := by
    intro g
    have hh := congrArg (fun v : ℓ²(Classes (gamma N),ℂ) => v (classOf (gamma N) g))
      (((countingSectorSpace_mem N hN.1 e f).mp hf).2 (some p))
    change f (classOf (gamma N) (localAtkinLabel N hN.1 p*g))=
      ((-signReal (e.2 p):ℝ):ℂ)*f (classOf (gamma N) g) at hh
    change ‖f (classOf (gamma N) ((simpleAtkinGeneratorIndex N hN.1 p).val*g))‖=_
    rw [simpleAtkinGeneratorIndex_value,hh,norm_mul,Complex.ofReal_neg,signReal_coe,norm_neg,sign_norm,one_mul]
  rw [admissibleNormalizerGroup,Subgroup.closure_le]
  intro a ha
  cases ha with
  | fricke => exact hW
  | half h4 =>
    intro g
    simpa only [norm_neg] using! congrArg norm (countingSector_half N hN.1 h4 e f hf g)
  | atkin D Q hQ A B hAB hQD =>
    have hcop : Nat.Coprime Q D := Nat.isCoprime_iff_coprime.mp ⟨A,B,by nlinarith [hAB]⟩
    exact admissible_atkin_mem N hN.1 K hK hN hW hS Q D hQD hcop
      ⟨exactAtkinLabel D Q hQ A B hAB,
        admissibleNormalizerGenerator.atkin D Q hQ A B hAB hQD⟩
      ⟨D,hQ,A,B,hAB,hQD,rfl⟩

/-- The scalar cover correction has exactly the original counting-sector
energy. All modulus invariance hypotheses follow from its new/sign equations. -/
theorem countingSector_metric_energy {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : GridAdmissibleGap.Admissible N) (e : Sector N)
    (g : ι→quotientNormalizerGroup N)
    (hg : ∀ i,(g i).val∈admissibleNormalizerGroup N hN.1)
    (δ : ℝ) (ν : ℕ) (hpos : ∀ z,0<normalizerCoverWeight N g δ ν z)
    (z : UpperHalfPlane) (f : ℓ²(Classes (gamma N),ℂ))
    (hf : f∈countingSectorSpace N hN.1 e) :
    (∑' q,ENNReal.ofReal
      (regularInvariantValue N (AsymptoticCongruenceWeight.weight N δ ν)
        (AsymptoticCongruenceWeight.weight_invariant N δ ν) z q*
        regularInvariantValue N (normalizerCoverMetricSquare N g δ ν)
          (normalizerCoverMetricSquare_invariant N g δ ν) z q)*ENNReal.ofReal (‖f q‖^2))=
      ∑' q,ENNReal.ofReal (‖f q‖^2) := by
  apply regular_cover_metric_partition N g δ ν hpos z
  intro i q
  induction q using Quotient.inductionOn with
  | h a =>
    apply congrArg ENNReal.ofReal
    apply congrArg (fun r : ℝ => r^2)
    exact countingSector_modulus N hN e f hf (hg i) a

#print axioms countingSector_modulus
#print axioms countingSector_metric_energy
end QuantitativeMaass.CountingMetric
