module

public import QuantitativeMaassConjugatedBlocksV1
public import QuantitativeMaassIntegralSchurOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

theorem inverse_sum_coeFn (S : Finset ℤ) (f : Lp ℂ 2 μ) :
    (∑ m∈S,inverse μ l hl m f)=ᵐ[μ]
      (fun x => if ⌊l x⌋∈S then (Real.exp (-l x):ℂ)*f x else 0) := by
  classical
  have hs : ∀ᵐ x ∂μ, ∀ m∈S,inverse μ l hl m f x=inverseCoefficient l m x*f x :=
    (Filter.eventually_all_finite S.finite_toSet).mpr (fun m _ => inverse_coeFn μ l hl m f)
  filter_upwards [Lp.coeFn_finsetSum S (fun m => inverse μ l hl m f),hs] with x hx hs
  rw [hx,Finset.sum_apply]
  have he (m : ℤ) (hm : m∈S) : inverse μ l hl m f x=
      if m=⌊l x⌋ then (Real.exp (-l x):ℂ)*f x else 0 := by
    rw [hs m hm,inverseCoefficient]
    by_cases h : m=⌊l x⌋
    · subst m
      simp only [mem_floor_region,Set.indicator_of_mem,ite_true]
    · have hn : x∉region l m := fun hx =>
        Set.disjoint_left.mp (region_disjoint l h) hx (mem_floor_region l x)
      simp only [Set.indicator_of_notMem hn,zero_mul,h,ite_false]
  rw [Finset.sum_congr rfl he]
  exact Finset.sum_ite_eq' S _ _

variable [SFinite μ] (D : IntegralSchur.Data μ) (J : ℕ)
  (hT : HasBandPropagation μ l hl D.operator J)
  (hk : ∀ (n m : ℤ), (J:ℤ) < |n-m| → ∀ x∈region l n,∀ y∈region l m,D.kernel x y=0)

omit [SFinite μ] in
include hk in
theorem kernel_output_inverse_sum (n : ℤ) (f : Lp ℂ 2 μ) (x : α) (hx : x∈region l n) :
    D.output (∑ m∈Finset.Icc (n-(J:ℤ)) (n+(J:ℤ)),inverse μ l hl m f : Lp ℂ 2 μ) x=
      D.output (fun y => (Real.exp (-l y):ℂ)*f y) x := by
  classical
  apply integral_congr_ae
  filter_upwards [inverse_sum_coeFn μ l hl (Finset.Icc (n-(J:ℤ)) (n+(J:ℤ))) f] with y hy
  rw [hy]
  by_cases hm : ⌊l y⌋∈Finset.Icc (n-(J:ℤ)) (n+(J:ℤ))
  · rw [ite_eq_left hm]
  · rw [ite_eq_right hm]
    have hsep : (J:ℤ) < |n-⌊l y⌋| := by
      by_contra hh
      have ha := abs_le.mp (le_of_not_gt hh)
      exact hm (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    rw [hk n ⌊l y⌋ hsep x hx y (mem_floor_region l y),zero_mul,zero_mul]

include hk in
/-- The bounded extension equals literal weighted kernel integration on
every L2 input, even when multiplying it by the inverse weight is not L2.
Finite propagation makes every output row depend on finitely many input bands. -/
theorem boundedConjugation_kernel_coeFn (f : Lp ℂ 2 μ) :
    boundedConjugation μ l hl D.operator J hT f=ᵐ[μ]
      (fun x => (Real.exp (l x):ℂ)*D.output (fun y => (Real.exp (-l y):ℂ)*f y) x) := by
  classical
  let B := boundedConjugation μ l hl D.operator J hT
  have hn (n : ℤ) : ∀ᵐ x ∂μ,x∈region l n →
      B f x=(Real.exp (l x):ℂ)*D.output (fun y => (Real.exp (-l y):ℂ)*f y) x := by
    let v : Lp ℂ 2 μ := ∑ m∈Finset.Icc (n-(J:ℤ)) (n+(J:ℤ)),inverse μ l hl m f
    have he : projection μ l hl n (B f)=forward μ l hl n (D.operator v) := by
      rw [boundedConjugation_row]
      simp only [v,map_sum]
    have hp := projection_coeFn μ l hl n (B f)
    rw [he] at hp
    filter_upwards [hp,forward_coeFn μ l hl n (D.operator v),D.operator_coeFn v] with x hp hf hv
    intro hx
    rw [Set.indicator_of_mem hx] at hp
    rw [←hp,hf,forwardCoefficient,Set.indicator_of_mem hx]
    change D.operator v x=D.output v x at hv
    rw [hv,kernel_output_inverse_sum μ l hl D J hk n f x hx]
  filter_upwards [ae_all_iff.mpr hn] with x hx
  exact hx ⌊l x⌋ (mem_floor_region l x)

#print axioms inverse_sum_coeFn
#print axioms kernel_output_inverse_sum
#print axioms boundedConjugation_kernel_coeFn

end QuantitativeMaass.LogBands
