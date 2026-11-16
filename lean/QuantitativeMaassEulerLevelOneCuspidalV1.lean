module

public import QuantitativeMaassEulerLevelOneHilbertV1
public import QuantitativeMaassEulerZeroMeanV1
public import QuantitativeMaassCuspLogComplexV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped MatrixGroups

namespace QuantitativeMaass

variable {b : ℕ → ℂ} (r : ℝ) (σ : ℕ)
  (hb : MaassOriginal.IsEulerSolution 1 (.principal r) σ b)

include hb

/-- At level one all integral cusp charts have the actual vanishing constant
term. Modular invariance reduces them to the proved Fourier mean. -/
theorem principalEulerPhysical_level_one_all_cusps (s : SL(2,ℤ)) (y : ℝ) (hy : 0<y) :
    cuspConstant 1 s (fun z : ℍ => principalEulerPhysical b r σ z) y=0 := by
  rw [cuspConstant_horizontal_integral 1 (by norm_num) s _ y hy]
  simp only [Nat.cast_one,inv_one,one_mul,integral_Icc_eq_integral_Ioc]
  have he : (fun x : ℝ => principalEulerPhysical b r σ (cuspAction s (cartesianLift (x,y))))=
      fun x => principalEulerWave b r σ (x,y) := by
    funext x
    change principalEulerPhysical b r σ ((s•cartesianLift (x,y):ℍ):ℂ)=_
    rw [principalEulerPhysical_level_one_invariant r σ hb,cartesianLift_positive _ hy]
    rfl
  rw [he]
  exact principalEulerWave_mean_zero hb.polynomialGrowth r σ y hy

theorem principalEulerLevelOneClass_constant_zero (s : SL(2,ℤ)) (a c : ℝ) (ha : 0<a) :
    cuspConstantLocal 1 s a c ha (principalEulerLevelOneClass r σ hb)=0 := by
  have he := cuspConstantLocal_representative_ae 1 (by norm_num) s a c ha
    (principalEulerLevelOneRepresentative r σ hb)
    (principalEulerPhysical_continuous_upper hb.polynomialGrowth r σ)
  apply Lp.ext
  filter_upwards [he,heightMeasure_rectangle_ae 0 ((1:ℕ):ℝ) a c,
    Lp.coeFn_zero ℂ 2 (heightMeasure (upperRectangle 0 ((1:ℕ):ℝ) a c))] with y hey hy hz
  change cuspConstantLocal 1 s a c ha (principalEulerLevelOneClass r σ hb) y=
    cuspConstant 1 s (fun z : ℍ => principalEulerPhysical b r σ z) y at hey
  rw [hey]
  rw [principalEulerPhysical_level_one_all_cusps r σ hb s y (ha.trans_le hy.1)]
  exact hz.symm

/-- The constructed original level-one quotient class belongs to the actual
closed all-cusp kernel used by the checked short-interval Weyl theorem. -/
theorem principalEulerLevelOneClass_cuspidal :
    principalEulerLevelOneClass r σ hb∈localCuspidalSpace 1 (by norm_num) := by
  simp only [localCuspidalSpace,Submodule.mem_iInf,LinearMap.mem_ker]
  intro s A B
  change localHalfDensityComplex ((1:ℕ):ℝ) A B (by norm_num)
    (cuspConstantLocal 1 s (Real.exp A) (Real.exp B) (Real.exp_pos A)
      (principalEulerLevelOneClass r σ hb))=0
  rw [principalEulerLevelOneClass_constant_zero r σ hb,map_zero]

def principalEulerLevelOneCuspClass : localCuspidalSpace 1 (by norm_num) :=
  ⟨principalEulerLevelOneClass r σ hb,principalEulerLevelOneClass_cuspidal r σ hb⟩

#print axioms principalEulerPhysical_level_one_all_cusps
#print axioms principalEulerLevelOneClass_constant_zero
#print axioms principalEulerLevelOneClass_cuspidal
#print axioms principalEulerLevelOneCuspClass

end QuantitativeMaass
