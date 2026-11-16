module

public import QuantitativeMaassCountingNormalizerMetricV1
public import AsymptoticOrbitDiagonalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticNestedQuotients AsymptoticSectorSigns QuantitativeNewGap
open scoped lp ENNReal
namespace QuantitativeMaass.CountingMetric

/-- The actual scalar metric coefficient gives an isometry on the
counting canonical sector, including every admissible level and sign. -/
theorem countingSector_metric_norm {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : GridAdmissibleGap.Admissible N) (e : Sector N)
    (g : ι→quotientNormalizerGroup N)
    (hg : ∀ i,(g i).val∈admissibleNormalizerGroup N hN.1)
    (δ : ℝ) (ν : ℕ) (hpos : ∀ z,0<normalizerCoverWeight N g δ ν z)
    (z : UpperHalfPlane) (c : Classes (gamma N)→ℂ) {C : ℝ} (hC : 0≤C)
    (hc : ∀ q,‖c q‖≤C)
    (hc2 : ∀ q,‖c q‖^2=
      regularInvariantValue N (weight N δ ν) (weight_invariant N δ ν) z q*
        regularInvariantValue N (normalizerCoverMetricSquare N g δ ν)
          (normalizerCoverMetricSquare_invariant N g δ ν) z q)
    (f : ℓ²(Classes (gamma N),ℂ)) (hf : f∈countingSectorSpace N hN.1 e) :
    ‖AsymptoticOrbitDiagonal.operator c hC hc f‖=‖f‖ := by
  let L := AsymptoticOrbitDiagonal.operator c hC hc
  have hs (v : ℓ²(Classes (gamma N),ℂ)) : HasSum (fun q => ‖v q‖^2) (‖v‖^2) := by
    simpa using lp.hasSum_norm (p:=2) (by norm_num) v
  have he (v : ℓ²(Classes (gamma N),ℂ)) :
      ENNReal.ofReal (‖v‖^2)=∑' q,ENNReal.ofReal (‖v q‖^2) := by
    rw [←(hs v).tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hs v).summable
  have hh : ENNReal.ofReal (‖L f‖^2)=ENNReal.ofReal (‖f‖^2) := by
    rw [he,he]
    calc
      _ = ∑' q,ENNReal.ofReal
          (regularInvariantValue N (weight N δ ν) (weight_invariant N δ ν) z q*
            regularInvariantValue N (normalizerCoverMetricSquare N g δ ν)
              (normalizerCoverMetricSquare_invariant N g δ ν) z q)*ENNReal.ofReal (‖f q‖^2) := by
        apply tsum_congr
        intro q
        change ENNReal.ofReal (‖c q*f q‖^2)=_
        rw [norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg _),hc2]
      _ = _ := countingSector_metric_energy N hN e g hg δ ν hpos z f hf
  have hr := congrArg ENNReal.toReal hh
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at hr
  nlinarith [norm_nonneg (L f),norm_nonneg f]

#print axioms countingSector_metric_norm
end QuantitativeMaass.CountingMetric
