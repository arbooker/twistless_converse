module

public import QuantitativeMaassFiniteExponentialSumsV1
public import QuantitativeMaassBandPropagationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)
  (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (J : ℕ) (hT : HasBandPropagation μ l hl T J)

def finitePropagationMap : finiteBandSpace μ l hl →ₗ[ℂ] finiteBandSpace μ l hl :=
  T.toLinearMap.restrict (fun f hf => operator_mem_finiteBandSpace μ l hl T J hT ⟨f,hf⟩)

/-- Literal multiplication by exp(-l), application of T, and multiplication
by exp(l), on the dense finite-band domain. -/
def conjugationLinear : finiteBandSpace μ l hl →ₗ[ℂ] Lp ℂ 2 μ :=
  (finiteBandSpace μ l hl).subtype.comp ((exponentialEnd μ l hl 1).comp
    ((finitePropagationMap μ l hl T J hT).comp (exponentialEnd μ l hl (-1))))

include hT in
theorem conjugated_block_zero (n m : ℤ) (hnm : (J:ℤ) < |n-m|) (f : Lp ℂ 2 μ) :
    forward μ l hl n (T (inverse μ l hl m f))=0 := by
  have hm : projection μ l hl m (inverse μ l hl m f)=inverse μ l hl m f :=
    (AsymptoticRegionL2.mem_space μ _ _ _).mp (inverse_mem_space μ l hl m f)
  have hz := hT n m hnm (inverse μ l hl m f)
  rw [hm] at hz
  rw [←forward_projection μ l hl n (T (inverse μ l hl m f)),hz,map_zero]

/-- The densely defined literal conjugation equals the checked finite
band matrix on every finitely supported input. -/
theorem conjugationLinear_eq_finite (S : Finset ℤ) (f : finiteBandSpace μ l hl)
    (hf : ∀ n∉S,projection μ l hl n f.val=0) :
    conjugationLinear μ l hl T J hT f=
      finiteConjugation μ l hl (propagatedSupport S J) S J T f.val := by
  let g := exponentialEnd μ l hl (-1) f
  let u := finitePropagationMap μ l hl T J hT g
  have hg (n : ℤ) (hn : n∉S) : projection μ l hl n g.val=0 :=
    exponentialEnd_support μ l hl (-1) f n (hf n hn)
  have hu := operator_band_support μ l hl T J hT S g.val hg
  have he : conjugationLinear μ l hl T J hT f=
      ∑ n∈propagatedSupport S J,forward μ l hl n (T g.val) :=
    exponential_one_sum μ l hl (propagatedSupport S J) u hu
  rw [he]
  have hg' : g.val=∑ m∈S,inverse μ l hl m f.val := exponential_neg_one_sum μ l hl S f hf
  rw [hg']
  simp only [map_sum]
  simp only [finiteConjugation,sum_apply,ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hnm : |n-m|≤(J:ℤ)
  · rw [ite_eq_left hnm]
  · rw [ite_eq_right hnm,conjugated_block_zero μ l hl T J hT n m (lt_of_not_ge hnm) f.val]

theorem conjugationLinear_norm_bound (f : finiteBandSpace μ l hl) :
    ‖conjugationLinear μ l hl T J hT f‖≤
      ((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1)*‖T‖*‖f.val‖ := by
  obtain ⟨S,hS⟩ := finiteBandSpace_support μ l hl f
  rw [conjugationLinear_eq_finite μ l hl T J hT S f hS]
  exact finiteConjugation_apply_bound μ l hl (propagatedSupport S J) S J T f.val

#print axioms conjugated_block_zero
#print axioms conjugationLinear_eq_finite
#print axioms conjugationLinear_norm_bound

end QuantitativeMaass.LogBands
