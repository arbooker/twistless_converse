module

public import QuantitativeMaassCoverMetricWeightV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane MeasureTheory AsymptoticCongruenceWeight
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCompactBranch
open scoped ENNReal
namespace QuantitativeMaass

variable {ι : Type*} [Fintype ι] (N : ℕ) (g : ι→quotientNormalizerGroup N)

theorem normalizerCoverMetricSquare_nonneg (δ : ℝ) (ν : ℕ) (z : ℍ) :
    0≤normalizerCoverMetricSquare N g δ ν z :=
  Finset.sum_nonneg (fun _i _ => inv_nonneg.mpr (normalizerCoverWeight_nonneg N g δ ν _))

theorem normalizerCoverMetric_sq (δ : ℝ) (ν : ℕ) (z : ℍ) :
    normalizerCoverMetric N g δ ν z^2=normalizerCoverMetricSquare N g δ ν z :=
  Real.sq_sqrt (normalizerCoverMetricSquare_nonneg N g δ ν z)

/-- Partition identity from a finite normalizer cover. The cover need not
be a subgroup, and the common normalizer-invariant density can be arbitrary. -/
theorem normalizerCoverMetric_partition (δ : ℝ) (ν : ℕ)
    (hpos : ∀ z,0<normalizerCoverWeight N g δ ν z)
    (F : ℍ→ℝ≥0∞) (hF : Measurable F)
    (hFi : ∀ a : gamma N,∀ z,F (a.val • z)=F z)
    (hFg : ∀ i z,F ((g i).val • z)=F z) :
    (∫⁻ z,ENNReal.ofReal (weight N δ ν z*normalizerCoverMetricSquare N g δ ν z)*F z
      ∂quotientMeasure N)=∫⁻ z,F z ∂quotientMeasure N := by
  let A := normalizerCoverWeight N g δ ν
  let E (i : ι) (z : ℍ) : ℝ≥0∞ :=
    ENNReal.ofReal (weight N δ ν z*(A ((g i).val⁻¹ • z))⁻¹)*F z
  have hmeas (i : ι) : Measurable (E i) :=
    ((weight_measurable N δ ν).mul
      (((normalizerCoverWeight_measurable N g δ ν).comp
        (AsymptoticRationalGroup.measurePreserving (g i).val⁻¹).measurable).inv)).ennreal_ofReal.mul hF
  have he (z : ℍ) : ENNReal.ofReal (weight N δ ν z*normalizerCoverMetricSquare N g δ ν z)*F z=
      ∑ i,E i z := by
    unfold normalizerCoverMetricSquare
    rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
    · rw [Finset.sum_mul]
    · intro i _
      exact mul_nonneg (quotientWeight_nonneg N δ ν z) (inv_pos.mpr (hpos _)).le
  have hmove (i : ι) : (∫⁻ z,E i z ∂quotientMeasure N)=
      ∫⁻ z,ENNReal.ofReal (weight N δ ν ((g i).val • z)*(A z)⁻¹)*F z ∂quotientMeasure N := by
    have hh := OrbitIntegral.lintegral_normalizer volume AsymptoticRationalGroup.measurePreserving
      (gamma N) (g i).val (fun _ ha => normalizer_conj_mem N (g i) ha)
      (fun _ ha => normalizer_inv_conj_mem N (g i) ha)
      (density N) (density_measurable N) (density_orbit_sum N) (E i) (hmeas i) (by
        intro a z
        dsimp only [E]
        rw [weight_invariant,hFi]
        have hi : A ((g i).val⁻¹ • (a.val • z))=A ((g i).val⁻¹ • z) :=
          invariant_normalizer_comp A (normalizerCoverWeight_invariant N g δ ν) (g i)⁻¹ a z
        rw [hi])
    have hcomp (z : ℍ) : E i ((g i).val • z)=
        ENNReal.ofReal (weight N δ ν ((g i).val • z)*(A z)⁻¹)*F z := by
      dsimp only [E]
      rw [inv_smul_smul,hFg]
    simpa only [quotientMeasure,hcomp] using hh.symm
  simp_rw [he]
  rw [lintegral_finsetSum Finset.univ (fun i _ => hmeas i)]
  simp_rw [hmove]
  have hm2 (i : ι) : Measurable (fun z => ENNReal.ofReal
      (weight N δ ν ((g i).val • z)*(A z)⁻¹)*F z) :=
    ((((weight_measurable N δ ν).comp (AsymptoticRationalGroup.measurePreserving (g i).val).measurable).mul
      (normalizerCoverWeight_measurable N g δ ν).inv).ennreal_ofReal.mul hF)
  rw [←lintegral_finsetSum Finset.univ (fun i _ => hm2 i)]
  apply lintegral_congr
  intro z
  rw [←Finset.sum_mul,←ENNReal.ofReal_sum_of_nonneg]
  · rw [←Finset.sum_mul]
    change ENNReal.ofReal (A z*(A z)⁻¹)*F z=F z
    rw [mul_inv_cancel₀ (hpos z).ne',ENNReal.ofReal_one,one_mul]
  · intro i _
    exact mul_nonneg (quotientWeight_nonneg N δ ν _) (inv_pos.mpr (hpos z)).le

/-- The scalar correction gives exactly the quotient norm for genuine
representatives whose normalizer transforms preserve absolute values. -/
theorem normalizerCoverMetric_representative_energy {δ : ℝ} (hδ : 0<δ)
    {ν : ℕ} (hν : 1≤ν) (hpos : ∀ z,0<normalizerCoverWeight N g δ ν z)
    (f : ℍ→ℂ) (hf : Measurable f)
    (hi : ∀ a : gamma N,∀ z,f (a.val • z)=f z)
    (hg : ∀ i z,‖f ((g i).val • z)‖=‖f z‖) :
    (∫⁻ z,ENNReal.ofReal (‖((normalizerCoverMetric N g δ ν z*cap δ ν z:ℝ):ℂ)*f z‖^2)
      ∂quotientMeasure 0)=∫⁻ z,ENNReal.ofReal (‖f z‖^2) ∂quotientMeasure N := by
  let F (z : ℍ) : ℂ := (normalizerCoverMetric N g δ ν z:ℂ)*f z
  have hF : Measurable F :=
    (Complex.measurable_ofReal.comp (normalizerCoverMetric_measurable N g δ ν)).mul hf
  have hFi (a : gamma N) (z : ℍ) : F (a.val • z)=F z := by
    dsimp only [F]
    rw [normalizerCoverMetric_invariant,hi]
  have he := weighted_quotient_energy N hδ hν F hF hFi
  have hid (z : ℍ) : ((normalizerCoverMetric N g δ ν z*cap δ ν z:ℝ):ℂ)*f z=
      (cap δ ν z:ℂ)*F z := by dsimp only [F];push_cast;ring
  simp_rw [hid]
  rw [he]
  have hnorm (z : ℍ) : ‖F z‖^2=normalizerCoverMetricSquare N g δ ν z*‖f z‖^2 := by
    dsimp only [F]
    rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,normalizerCoverMetric_sq]
  simp_rw [hnorm,ENNReal.ofReal_mul (normalizerCoverMetricSquare_nonneg N g δ ν _)]
  have heq (z : ℍ) : ENNReal.ofReal (weight N δ ν z)*
      (ENNReal.ofReal (normalizerCoverMetricSquare N g δ ν z)*ENNReal.ofReal (‖f z‖^2))=
      ENNReal.ofReal (weight N δ ν z*normalizerCoverMetricSquare N g δ ν z)*ENNReal.ofReal (‖f z‖^2) := by
    rw [ENNReal.ofReal_mul (quotientWeight_nonneg N δ ν z),mul_assoc]
  simp_rw [heq]
  exact normalizerCoverMetric_partition N g δ ν hpos _ (hf.norm.pow_const 2).ennreal_ofReal
    (by intro a z;rw [hi]) (by intro i z;rw [hg])

#print axioms normalizerCoverMetric_partition
#print axioms normalizerCoverMetric_representative_energy
end QuantitativeMaass
