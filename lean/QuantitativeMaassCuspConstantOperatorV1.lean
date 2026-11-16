module

public import QuantitativeMaassHorocycleAverageV1
public import QuantitativeMaassAllCuspConstantV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups InnerProductSpace

namespace QuantitativeMaass

/-- The actual height marginal lives on the rectangle's height interval. -/
theorem heightMeasure_rectangle_ae (l r a b : ℝ) :
    ∀ᵐ y ∂heightMeasure (upperRectangle l r a b), y∈Icc a b := by
  apply (ae_map_iff continuous_im.measurable.aemeasurable measurableSet_Icc).mpr
  filter_upwards [ae_restrict_mem (upperRectangle_measurable l r a b)] with Z hZ
  exact hZ.2

/-- The existing cusp constant term is exactly the length-normalized
horizontal integral in the actual integral cusp chart. -/
theorem cuspConstant_horizontal_integral (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (F : ℍ → ℂ) (y : ℝ) (hy : 0<y) :
    cuspConstant N s F y = ((N:ℂ)⁻¹)*
      ∫ x in Icc (0:ℝ) (N:ℝ), F (cuspAction s (cartesianLift (x,y))) := by
  have hn : (N:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hN)
  have he : (fun x : ℝ => cuspProfile N s F x y)=
      fun x => F (cuspAction s (cartesianLift ((N:ℝ)*x,y))) := by
    funext x
    rw [cuspProfile,dite_eq_left hy,cartesianLift_positive _ hy]
    rfl
  unfold cuspConstant zeroFourier
  rw [he,intervalIntegral.integral_comp_mul_left
    (fun x => F (cuspAction s (cartesianLift (x,y)))) hn]
  rw [mul_zero,mul_one,intervalIntegral.integral_of_le (Nat.cast_nonneg N),
    ← integral_Icc_eq_integral_Ioc]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast]

/-- Bounded local constant-term extraction on the full quotient Hilbert
space, using the common cusp period N and a positive compact height band. -/
def cuspConstantLocal (N : ℕ) (s : SL(2,ℤ)) (a b : ℝ) (ha : 0<a) :
    AutomorphicSpace N →L[ℂ] Lp ℂ 2 (heightMeasure (upperRectangle 0 N a b)) :=
  cuspHeightAverage N s _ (upperRectangle_compact 0 N a b ha)

theorem cuspConstantLocal_norm_le (N : ℕ) (s : SL(2,ℤ)) (a b : ℝ) (ha : 0<a) :
    ‖cuspConstantLocal N s a b ha‖≤
      ‖cuspRestriction N s _ (upperRectangle_compact 0 N a b ha)‖ :=
  cuspHeightAverage_norm_le _ _ _ _

/-- The bounded operator agrees with the manuscript's literal constant
term at every integral cusp for every continuous invariant L2 representative. -/
theorem cuspConstantLocal_representative_ae (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (a b : ℝ) (ha : 0<a)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) :
    (cuspConstantLocal N s a b ha
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f) : ℝ → ℂ)
      =ᵐ[heightMeasure (upperRectangle 0 N a b)] cuspConstant N s f.val := by
  have he := localHeightAverage_horocycle_ae 0 (N:ℝ) a b (Nat.cast_pos.mpr hN) ha
    (fun Z => f.val (cuspAction s Z)) (hf.comp (cuspAction_continuous s))
    (cuspRestriction N s _ (upperRectangle_compact 0 N a b ha)
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f))
    (cuspRestriction_representative_ae N s _ (upperRectangle_compact 0 N a b ha) f)
  change (cuspConstantLocal N s a b ha
    (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f) : ℝ → ℂ)=ᵐ[_] _ at he
  filter_upwards [he,heightMeasure_rectangle_ae 0 (N:ℝ) a b] with y hey hy
  rw [hey,cuspConstant_horizontal_integral N hN s f.val y (ha.trans_le hy.1)]
  simp only [horocycleAverageExtension,sub_zero,max_eq_right hy.1,Complex.ofReal_natCast]

#print axioms cuspConstant_horizontal_integral
#print axioms cuspConstantLocal_norm_le
#print axioms cuspConstantLocal_representative_ae

end QuantitativeMaass
