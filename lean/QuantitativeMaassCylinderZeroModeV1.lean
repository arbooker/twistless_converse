module

public import QuantitativeMaassCylinderEulerSpectralV1
public import QuantitativeMaassEulerZeroMeanV1
public import QuantitativeMaassHorocycleAverageV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology ContDiff MatrixGroups

namespace QuantitativeMaass

/-- Identification of cylinder L2 with its actual automorphic realization. -/
def cylinderAutomorphic : Lp ℂ 2 (quotientMeasure 0) →ₗᵢ[ℂ] AutomorphicSpace 0 where
  toFun f := ⟨f,by rw [cylinder_automorphicSpace_eq_top]; trivial⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- Bounded local horizontal mean on the translation cylinder. -/
def cylinderLocalMean (a b : ℝ) (ha : 0<a) :
    Lp ℂ 2 (quotientMeasure 0) →L[ℂ] Lp ℂ 2 (heightMeasure (upperRectangle 0 1 a b)) :=
  (cuspHeightAverage 0 1 (upperRectangle 0 1 a b) (upperRectangle_compact 0 1 a b ha)).comp
    cylinderAutomorphic.toContinuousLinearMap

/-- The actual closed subspace with vanishing constant horizontal mode at
all positive heights, expressed through bounded local mean operators. -/
def cylinderNonzeroModes : Submodule ℂ (Lp ℂ 2 (quotientMeasure 0)) :=
  ⨅ (a : ℝ) (b : ℝ) (ha : 0<a),LinearMap.ker (cylinderLocalMean a b ha).toLinearMap

theorem cylinderNonzeroModes_closed : IsClosed (cylinderNonzeroModes : Set (Lp ℂ 2 (quotientMeasure 0))) := by
  simp only [cylinderNonzeroModes,Submodule.coe_iInf]
  apply isClosed_iInter
  intro a
  apply isClosed_iInter
  intro b
  apply isClosed_iInter
  intro ha
  exact (cylinderLocalMean a b ha).isClosed_ker

instance : CompleteSpace cylinderNonzeroModes := cylinderNonzeroModes_closed.completeSpace_coe

theorem cappedEuler_continuous {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (ε : ℝ) (t : ℕ) :
    Continuous (fun z : ℍ => (cappedHeightWeight ε t z:ℂ)*principalEulerPhysical b r σ z) := by
  have hc : Continuous (cappedHeightWeight ε t) := AsymptoticCompactBranch.cap_continuous ε t
  exact (Complex.continuous_ofReal.comp hc).mul (principalEulerPhysical_continuous_upper hb r σ)

theorem cappedEuler_mean_zero {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (ε : ℝ) (t : ℕ) (y : ℝ) (hy : 0<y) :
    (∫ x in Icc (0:ℝ) 1,(cappedHeightWeight ε t (cartesianLift (x,y)):ℂ)*
      principalEulerPhysical b r σ (cartesianLift (x,y)))=0 := by
  have he (x : ℝ) : (cappedHeightWeight ε t (cartesianLift (x,y)):ℂ)*
      principalEulerPhysical b r σ (cartesianLift (x,y))=
      ((min (y/ε) 1)^t:ℂ)*principalEulerWave b r σ (x,y) := by
    rw [cartesianLift_positive _ hy]
    change (((min (y/ε) 1)^t:ℝ):ℂ)*principalEulerWave b r σ (x,y)=_
    rw [Complex.ofReal_pow]
  simp_rw [he]
  rw [integral_const_mul,integral_Icc_eq_integral_Ioc,principalEulerWave_mean_zero hb r σ y hy,mul_zero]

#print axioms cylinderAutomorphic
#print axioms cylinderNonzeroModes_closed
#print axioms cappedEuler_continuous
#print axioms cappedEuler_mean_zero

end QuantitativeMaass
