module

public import QuantitativeMaassWeightedQuotientEmbeddingV1
public import QuantitativeMaassCylinderEulerZeroModeV1
public import QuantitativeNinaMaassOldSpectrumV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCompactBranch
open AsymptoticIntegralSubgroup AsymptoticFreshMatrices QuantitativeNinaMaass
open scoped Topology MatrixGroups

namespace QuantitativeMaass

/-- The common-period cusp condition implies the unit-period mean is zero
at infinity, using the actual translation equation. -/
theorem continuous_cuspidal_unit_mean (N : ℕ) (hN : 0<N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hc : AutomorphicL2.denseEmbedding _ _ f∈localCuspidalSpace N hN)
    (y : ℝ) (hy : 0<y) :
    (∫ x in Icc (0:ℝ) 1,f.val (cartesianLift (x,y)))=0 := by
  let F : ℝ → ℂ := fun x => f.val (horocyclePoint x y hy)
  have hF : Continuous F := by
    simpa only [cuspProfile,dite_eq_left hy,map_one,one_smul,Nat.cast_one,one_mul] using
      cuspProfile_continuous 1 1 f.val hf y
  have hp : Function.Periodic F 1 := by
    intro x
    have h := f.property.2.1 ⟨translationLabel (1:ℚ),translation_mem N 1⟩ (horocyclePoint x y hy)
    have ht := horocyclePoint_translate (1:ℤ) x y hy
    rw [AsymptoticCongruenceLabels.upper_label] at ht
    simp only [Int.cast_one] at ht
    change f.val (translationLabel (1:ℚ) • horocyclePoint x y hy)=f.val (horocyclePoint x y hy) at h
    rw [ht] at h
    exact h
  have hz := localCuspidalSpace_continuous_constant_zero N hN
    (AutomorphicL2.denseEmbedding _ _ f) hc f.val hf f.property.2.1 f.property.2.2.coeFn_toLp 1 y hy
  have he := periodic_dilate_average F hF hp N hN
  have hz' : (∫ x in (0:ℝ)..1,F ((N:ℝ)*x))=0 := by
    simpa only [cuspConstant,zeroFourier,cuspProfile,dite_eq_left hy,map_one,one_smul,F] using hz
  rw [he] at hz'
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  have hl (x : ℝ) : cartesianLift (x,y)=horocyclePoint x y hy := cartesianLift_positive (x,y) hy
  simp_rw [hl]
  exact hz'

def weightedCylinderRepresentative (N : ℕ) {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    AutomorphicL2.representatives (gamma 0) (quotientMeasure 0) := by
  refine ⟨fun z => (cappedHeightWeight ε v z:ℂ)*f.val z,
    (Complex.continuous_ofReal.comp (cap_continuous ε v)).measurable.mul f.property.1,?_,
    weightedRepresentative_memLp N hε hv f⟩
  intro γ z
  change (cappedHeightWeight ε v (γ.val • z):ℂ)*f.val (γ.val • z)=
    (cappedHeightWeight ε v z:ℂ)*f.val z
  rw [cappedHeightWeight_cylinder_invariant]
  have hi := f.property.2.1 ⟨γ.val,gamma_le_of_dvd (dvd_zero N) γ.property⟩ z
  rw [hi]

theorem weightedCylinderRepresentative_class (N : ℕ) {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    AutomorphicL2.denseEmbedding _ _ (weightedCylinderRepresentative N hε hv f)=
      cylinderAutomorphic (weightedQuotientRepresentative N hε hv f) := by
  apply Subtype.ext
  apply Lp.ext
  exact (weightedCylinderRepresentative N hε hv f).property.2.2.coeFn_toLp.trans
    (weightedRepresentative_memLp N hε hv f).coeFn_toLp.symm

theorem weighted_cuspidal_unit_mean (N : ℕ) (hN : 0<N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hc : AutomorphicL2.denseEmbedding _ _ f∈localCuspidalSpace N hN)
    (ε : ℝ) (v : ℕ) (y : ℝ) (hy : 0<y) :
    (∫ x in Icc (0:ℝ) 1,(cappedHeightWeight ε v (cartesianLift (x,y)):ℂ)*
      f.val (cartesianLift (x,y)))=0 := by
  have hw (x : ℝ) : cappedHeightWeight ε v (cartesianLift (x,y))=(min (y/ε) 1)^v := by
    rw [cartesianLift_positive _ hy]
    rfl
  simp_rw [hw]
  rw [integral_const_mul,continuous_cuspidal_unit_mean N hN f hf hc y hy,mul_zero]

#print axioms continuous_cuspidal_unit_mean
#print axioms weightedCylinderRepresentative_class
#print axioms weighted_cuspidal_unit_mean

end QuantitativeMaass
