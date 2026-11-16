module

public import QuantitativeMaassBandMultipliersV1
public import QuantitativeMaassWeightBandGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

theorem inverse_projection (n : ℤ) (f : Lp ℂ 2 μ) :
    inverse μ l hl n (projection μ l hl n f)=inverse μ l hl n f := by
  apply Lp.ext
  filter_upwards [inverse_coeFn μ l hl n (projection μ l hl n f),
    projection_coeFn μ l hl n f,inverse_coeFn μ l hl n f] with x hi hp hf
  rw [hi,hp,hf]
  classical
  by_cases hx : x∈region l n
  · rw [Set.indicator_of_mem hx]
  · rw [inverseCoefficient,Set.indicator_of_notMem hx,zero_mul,zero_mul]

/-- The actual finite matrix of conjugated band blocks, restricted to a
fixed propagation width. Both cutoffs may grow independently. -/
def finiteConjugation (S U : Finset ℤ) (J : ℕ) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  ∑ n∈S,∑ m∈U.filter (fun m => |n-m|≤(J:ℤ)),
    (forward μ l hl n).comp (T.comp (inverse μ l hl m))

theorem finiteConjugation_apply_bound (S U : Finset ℤ) (J : ℕ)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (f : Lp ℂ 2 μ) :
    ‖finiteConjugation μ l hl S U J T f‖≤
      ((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1)*‖T‖*‖f‖ := by
  let v (n m : ℤ) := forward μ l hl n (T (inverse μ l hl m f))
  let row (n : ℤ) : space μ l hl n :=
    ⟨∑ m∈U.filter (fun m => |n-m|≤(J:ℤ)),v n m,
      Submodule.sum_mem _ (fun m _ => forward_mem_space μ l hl n _)⟩
  have he : finiteConjugation μ l hl S U J T f=
      ∑ n∈S,(space μ l hl n).subtypeₗᵢ (row n) := by
    simp only [finiteConjugation,sum_apply,ContinuousLinearMap.comp_apply,row,v,
      Submodule.coe_subtypeₗᵢ]
    rfl
  have hn : ‖finiteConjugation μ l hl S U J T f‖^2=
      ∑ n∈S,‖∑ m∈U.filter (fun m => |n-m|≤(J:ℤ)),v n m‖^2 := by
    rw [he,(space_orthogonal μ l hl).norm_sum row S]
    rfl
  have hv (n : ℤ) (_hn : n∈S) (m : ℤ) (_hm : m∈U) (hnm : |n-m|≤(J:ℤ)) :
      ‖v n m‖≤(Real.exp ((J:ℝ)+1)*‖T‖)*‖projection μ l hl m f‖ := by
    have hc := conjugated_block_bound μ l hl T n m (projection μ l hl m f)
    rw [inverse_projection] at hc
    apply hc.trans
    have hd : (n:ℝ)+1-(m:ℝ)≤(J:ℝ)+1 := by
      have hh : n-m≤(J:ℤ) := (le_abs_self _).trans hnm
      have hh' : (n:ℝ)-(m:ℝ)≤(J:ℝ) := by exact_mod_cast hh
      linarith
    gcongr
  have hb := integer_band_norm_square_bound S U J (Real.exp ((J:ℝ)+1)*‖T‖)
    (fun m => ‖projection μ l hl m f‖) v hv
  rw [←hn] at hb
  have hc := sum_projection_norm_square_le μ l hl U f
  have hsq : ‖finiteConjugation μ l hl S U J T f‖^2≤
      (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1)*‖T‖*‖f‖)^2 := by
    calc
      _ ≤ ((2*J+1:ℕ):ℝ)^2*(Real.exp ((J:ℝ)+1)*‖T‖)^2*‖f‖^2 :=
        hb.trans (mul_le_mul_of_nonneg_left hc (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      _ = _ := by ring
  have hpos : 0≤((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1)*‖T‖*‖f‖ := by positivity
  nlinarith [norm_nonneg (finiteConjugation μ l hl S U J T f)]

/-- The full 2J+1 norm constant is uniform in both finite cutoffs. -/
theorem finiteConjugation_norm_bound (S U : Finset ℤ) (J : ℕ)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    ‖finiteConjugation μ l hl S U J T‖≤((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1)*‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (finiteConjugation_apply_bound μ l hl S U J T)

#print axioms inverse_projection
#print axioms finiteConjugation_apply_bound
#print axioms finiteConjugation_norm_bound

end QuantitativeMaass.LogBands
