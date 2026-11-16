module

public import QuantitativeMaassInvariantMultiplierV1
public import QuantitativeMaassCompletedGeneratorMetricV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane MeasureTheory AsymptoticCongruenceWeight
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
namespace QuantitativeMaass

/-- Invariant coefficients remain invariant after normalizer pullback. -/
theorem invariant_normalizer_comp {N : ℕ} {β : Type*} (c : ℍ→β)
    (hi : ∀ a : gamma N,∀ z,c (a.val • z)=c z) (g : quotientNormalizerGroup N)
    (a : gamma N) (z : ℍ) : c (g.val • (a.val • z))=c (g.val • z) := by
  have hh := hi ⟨g.val*a.val*g.val⁻¹,normalizer_conj_mem N g a.property⟩ (g.val • z)
  simpa only [mul_smul,inv_smul_smul] using hh

variable {ι : Type*} [Fintype ι] (N : ℕ) (g : ι→quotientNormalizerGroup N)

def normalizerCoverWeight (δ : ℝ) (ν : ℕ) (z : ℍ) : ℝ :=
  ∑ i,weight N δ ν ((g i).val • z)

theorem normalizerCoverWeight_measurable (δ : ℝ) (ν : ℕ) :
    Measurable (normalizerCoverWeight N g δ ν) := by
  apply Finset.measurable_sum
  intro i _
  exact (weight_measurable N δ ν).comp (AsymptoticRationalGroup.measurePreserving (g i).val).measurable

theorem normalizerCoverWeight_invariant (δ : ℝ) (ν : ℕ) (a : gamma N) (z : ℍ) :
    normalizerCoverWeight N g δ ν (a.val • z)=normalizerCoverWeight N g δ ν z := by
  apply Finset.sum_congr rfl
  intro i _
  exact invariant_normalizer_comp _ (weight_invariant N δ ν) (g i) a z

theorem normalizerCoverWeight_nonneg (δ : ℝ) (ν : ℕ) (z : ℍ) :
    0≤normalizerCoverWeight N g δ ν z :=
  Finset.sum_nonneg (fun i _ => quotientWeight_nonneg N δ ν ((g i).val • z))

theorem normalizerCoverWeight_upper {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (z : ℍ) :
    normalizerCoverWeight N g δ ν z≤(Fintype.card ι:ℝ)*quotientWeightBound δ := by
  calc
    _ ≤ ∑ _i : ι,quotientWeightBound δ := Finset.sum_le_sum (fun i _ =>
      quotientWeight_uniform_bound N hδ hν ((g i).val • z))
    _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

theorem normalizerCoverWeight_lower {δ Y : ℝ} (hδ : 0<δ) (hY : 0<Y)
    {ν : ℕ} (hν : 1≤ν)
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • ((g i).val • z)).im) (z : ℍ) :
    heightWeightFloor δ ν Y≤normalizerCoverWeight N g δ ν z := by
  obtain ⟨i,a,ha⟩ := hcover z
  have hh := weight_lower_of_height N hδ hY hν (a.val • ((g i).val • z)) ha
  rw [weight_invariant] at hh
  exact hh.trans (Finset.single_le_sum (f:=fun j => weight N δ ν ((g j).val • z))
    (fun j _ => quotientWeight_nonneg N δ ν ((g j).val • z)) (Finset.mem_univ i))

/-- Sum of the reciprocal cover weights in the inverse normalizer charts.
Its square root is the scalar correction to the original cylinder cap. -/
def normalizerCoverMetricSquare (δ : ℝ) (ν : ℕ) (z : ℍ) : ℝ :=
  ∑ i,(normalizerCoverWeight N g δ ν ((g i).val⁻¹ • z))⁻¹

def normalizerCoverMetric (δ : ℝ) (ν : ℕ) (z : ℍ) : ℝ :=
  Real.sqrt (normalizerCoverMetricSquare N g δ ν z)

theorem normalizerCoverMetricSquare_measurable (δ : ℝ) (ν : ℕ) :
    Measurable (normalizerCoverMetricSquare N g δ ν) := by
  apply Finset.measurable_sum
  intro i _
  exact ((normalizerCoverWeight_measurable N g δ ν).comp
    (AsymptoticRationalGroup.measurePreserving (g i).val⁻¹).measurable).inv

theorem normalizerCoverMetricSquare_invariant (δ : ℝ) (ν : ℕ) (a : gamma N) (z : ℍ) :
    normalizerCoverMetricSquare N g δ ν (a.val • z)=normalizerCoverMetricSquare N g δ ν z := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg Inv.inv (invariant_normalizer_comp _
    (normalizerCoverWeight_invariant N g δ ν) (g i)⁻¹ a z)

theorem normalizerCoverMetric_measurable (δ : ℝ) (ν : ℕ) :
    Measurable (normalizerCoverMetric N g δ ν) :=
  (normalizerCoverMetricSquare_measurable N g δ ν).sqrt

theorem normalizerCoverMetric_invariant (δ : ℝ) (ν : ℕ) (a : gamma N) (z : ℍ) :
    normalizerCoverMetric N g δ ν (a.val • z)=normalizerCoverMetric N g δ ν z :=
  congrArg Real.sqrt (normalizerCoverMetricSquare_invariant N g δ ν a z)

/-- Explicit two-sided bounds, including all cusps; neither side depends
on an eigenfunction, spectral band, polynomial degree, or sign choice. -/
theorem normalizerCoverMetricSquare_bounds [Nonempty ι]
    {δ Y : ℝ} (hδ : 0<δ) (hY : 0<Y) {ν : ℕ} (hν : 1≤ν)
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • ((g i).val • z)).im) (z : ℍ) :
    ((Fintype.card ι:ℝ)*quotientWeightBound δ+1)⁻¹≤normalizerCoverMetricSquare N g δ ν z ∧
      normalizerCoverMetricSquare N g δ ν z≤(Fintype.card ι:ℝ)/(heightWeightFloor δ ν Y) := by
  have hlo (x : ℍ) := normalizerCoverWeight_lower N g hδ hY hν hcover x
  have hpos (x : ℍ) : 0<normalizerCoverWeight N g δ ν x := (heightWeightFloor_pos hδ hY ν).trans_le (hlo x)
  constructor
  · let i : ι := Classical.choice inferInstance
    have h1 := inv_anti₀ (hpos ((g i).val⁻¹ • z))
      ((normalizerCoverWeight_upper N g hδ hν ((g i).val⁻¹ • z)).trans
        (show (Fintype.card ι:ℝ)*quotientWeightBound δ≤(Fintype.card ι:ℝ)*quotientWeightBound δ+1 by linarith))
    exact h1.trans (Finset.single_le_sum (f:=fun j => (normalizerCoverWeight N g δ ν ((g j).val⁻¹ • z))⁻¹)
      (fun j _ => (inv_pos.mpr (hpos _)).le) (Finset.mem_univ i))
  · calc
      _ ≤ ∑ _i : ι,(heightWeightFloor δ ν Y)⁻¹ := Finset.sum_le_sum (fun i _ =>
        inv_anti₀ (heightWeightFloor_pos hδ hY ν) (hlo ((g i).val⁻¹ • z)))
      _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,div_eq_mul_inv]

#print axioms invariant_normalizer_comp
#print axioms normalizerCoverWeight_lower
#print axioms normalizerCoverWeight_upper
#print axioms normalizerCoverMetric_invariant
#print axioms normalizerCoverMetricSquare_bounds
end QuantitativeMaass
