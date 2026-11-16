module

public import QuantitativeMaassConjugatedColumnsV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory ContinuousLinearMap
open scoped BigOperators

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

/-- A finite inverse row, scaled at its output point, has a bound depending
only on the propagation width. No global inverse-weight bound is used. -/
theorem rowInverseSum_weighted_norm (J : ℕ) (x : α) :
    Real.exp (l x)*‖rowInverseSum μ l hl J ⌊l x⌋‖≤
      ((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1) := by
  classical
  let n : ℤ := ⌊l x⌋
  let S := Finset.Icc (n-(J:ℤ)) (n+(J:ℤ))
  have hrow : ‖rowInverseSum μ l hl J n‖≤∑ m∈S,Real.exp (-(m:ℝ)) := by
    exact (norm_sum_le S _).trans (Finset.sum_le_sum (fun m _ => inverse_norm_le μ l hl m))
  have hpoint (m : ℤ) (hm : m∈S) :
      Real.exp (l x)*Real.exp (-(m:ℝ))≤Real.exp ((J:ℝ)+1) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlow : (n:ℝ)-(J:ℝ)≤(m:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hhigh : l x<(n:ℝ)+1 := Int.lt_floor_add_one (l x)
    linarith
  calc
    _≤Real.exp (l x)*(∑ m∈S,Real.exp (-(m:ℝ))) :=
      mul_le_mul_of_nonneg_left hrow (Real.exp_pos _).le
    _=∑ m∈S,Real.exp (l x)*Real.exp (-(m:ℝ)) := Finset.mul_sum _ _ _
    _≤∑ _m∈S,Real.exp ((J:ℝ)+1) := Finset.sum_le_sum hpoint
    _=((S.card:ℕ):ℝ)*Real.exp ((J:ℝ)+1) := by simp
    _=_ := by rw [show S.card=2*J+1 from integer_band_card J n]

/-- The explicit conjugated column map preserves every column difference
with a uniform band constant. In particular it preserves mean-cancellation
estimates up to this squared factor. -/
theorem conjugatedColumn_sub_bound (c d : α → Lp ℂ 2 μ) (J : ℕ) (x : α) :
    ‖conjugatedColumn μ l hl c J x-conjugatedColumn μ l hl d J x‖≤
      (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))*‖c x-d x‖ := by
  unfold conjugatedColumn
  rw [←map_sub,←smul_sub]
  calc
    _≤‖(rowInverseSum μ l hl J ⌊l x⌋).adjoint‖*
        ‖(Real.exp (l x):ℂ) • (c x-d x)‖ := (rowInverseSum μ l hl J ⌊l x⌋).adjoint.le_opNorm _
    _=(Real.exp (l x)*‖rowInverseSum μ l hl J ⌊l x⌋‖)*‖c x-d x‖ := by
      rw [adjoint.norm_map,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      ring
    _≤_ := mul_le_mul_of_nonneg_right (rowInverseSum_weighted_norm μ l hl J x) (norm_nonneg _)

#print axioms rowInverseSum_weighted_norm
#print axioms conjugatedColumn_sub_bound

end QuantitativeMaass.LogBands
