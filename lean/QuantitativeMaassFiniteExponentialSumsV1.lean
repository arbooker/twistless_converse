module

public import QuantitativeMaassFiniteExponentialV1
public import QuantitativeMaassConjugatedBandsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

theorem projection_exponential_one (n : ℤ) (f : finiteBandSpace μ l hl) :
    projection μ l hl n (exponentialEnd μ l hl 1 f).val=forward μ l hl n f.val := by
  apply Lp.ext
  filter_upwards [projection_coeFn μ l hl n (exponentialEnd μ l hl 1 f).val,
    exponentialEnd_coeFn μ l hl 1 f,forward_coeFn μ l hl n f.val] with x hp he hf
  rw [hp,hf]
  classical
  by_cases hx : x∈region l n
  · rw [Set.indicator_of_mem hx,he,forwardCoefficient,Set.indicator_of_mem hx,one_mul]
  · rw [Set.indicator_of_notMem hx,forwardCoefficient,Set.indicator_of_notMem hx,zero_mul]

theorem projection_exponential_neg_one (n : ℤ) (f : finiteBandSpace μ l hl) :
    projection μ l hl n (exponentialEnd μ l hl (-1) f).val=inverse μ l hl n f.val := by
  apply Lp.ext
  filter_upwards [projection_coeFn μ l hl n (exponentialEnd μ l hl (-1) f).val,
    exponentialEnd_coeFn μ l hl (-1) f,inverse_coeFn μ l hl n f.val] with x hp he hf
  rw [hp,hf]
  classical
  by_cases hx : x∈region l n
  · rw [Set.indicator_of_mem hx,he,inverseCoefficient,Set.indicator_of_mem hx,neg_one_mul]
  · rw [Set.indicator_of_notMem hx,inverseCoefficient,Set.indicator_of_notMem hx,zero_mul]

theorem exponential_one_sum (S : Finset ℤ) (f : finiteBandSpace μ l hl)
    (hf : ∀ n∉S,projection μ l hl n f.val=0) :
    (exponentialEnd μ l hl 1 f).val=∑ n∈S,forward μ l hl n f.val := by
  rw [eq_sum_projections μ l hl S _ (fun n hn => exponentialEnd_support μ l hl 1 f n (hf n hn))]
  exact Finset.sum_congr rfl (fun n _ => projection_exponential_one μ l hl n f)

theorem exponential_neg_one_sum (S : Finset ℤ) (f : finiteBandSpace μ l hl)
    (hf : ∀ n∉S,projection μ l hl n f.val=0) :
    (exponentialEnd μ l hl (-1) f).val=∑ n∈S,inverse μ l hl n f.val := by
  rw [eq_sum_projections μ l hl S _ (fun n hn => exponentialEnd_support μ l hl (-1) f n (hf n hn))]
  exact Finset.sum_congr rfl (fun n _ => projection_exponential_neg_one μ l hl n f)

theorem forward_projection (n : ℤ) (f : Lp ℂ 2 μ) :
    forward μ l hl n (projection μ l hl n f)=forward μ l hl n f := by
  apply Lp.ext
  filter_upwards [forward_coeFn μ l hl n (projection μ l hl n f),
    projection_coeFn μ l hl n f,forward_coeFn μ l hl n f] with x hi hp hf
  rw [hi,hp,hf]
  classical
  by_cases hx : x∈region l n
  · rw [Set.indicator_of_mem hx]
  · rw [forwardCoefficient,Set.indicator_of_notMem hx,zero_mul,zero_mul]

#print axioms projection_exponential_one
#print axioms projection_exponential_neg_one
#print axioms exponential_one_sum
#print axioms exponential_neg_one_sum
#print axioms forward_projection

end QuantitativeMaass.LogBands
