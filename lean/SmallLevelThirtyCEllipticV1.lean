module

public import SmallLevelThirtyCDefectV1
public import SmallLevelAnalyticRigidityTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelThirtyC

open Matrix ModularGroup Complex Filter Set
open scoped MatrixGroups Topology

def elliptic : SL(2,ℚ) := ⟨!![4,-1;15,-7/2], by norm_num [det_fin_two]⟩

def fixedPoint : ℂ := ⟨1/4, Real.sqrt 15/60⟩

theorem fixedPoint_positive : 0<fixedPoint.im := by
  change 0<Real.sqrt 15/60
  positivity

theorem fixedPoint_denom : (15:ℂ)*fixedPoint-7/2≠0 := by
  intro h
  have hh := congrArg Complex.im h
  simp [fixedPoint] at hh

theorem fixedPoint_fixed : (4*fixedPoint-1)/(15*fixedPoint-7/2)=fixedPoint := by
  apply (div_eq_iff fixedPoint_denom).mpr
  have hs : (Real.sqrt 15)^2=15 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [fixedPoint, Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- The explicit elliptic matrix found in the level-thirty modulus-four calculation
annihilates any positive-weight holomorphic invariant defect. -/
theorem elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F ((4*z-1)/(15*z-7/2))=(15*z-7/2)^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : (1/2:ℚ)≠m := by
    intro hm
    have hh : (2:ℚ)*m=1 := by rw [← hm]; norm_num
    have hi : (2:ℤ)*m=1 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 fixedPoint,
      F ((4*z-1)/(15*z-7/2))=(15*z-7/2)^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds fixedPoint_positive] with z hz
    simpa only [sub_eq_add_neg, neg_div] using he z hz
  have hh := SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected fixedPoint_positive
    (a:=4) (b:= -1) (c:=15) (d:= -7/2) (t:=(1/2:ℚ))
    (by norm_num) (by simpa only [sub_eq_add_neg, neg_div] using fixedPoint_denom)
    (by simpa only [sub_eq_add_neg, neg_div] using fixedPoint_fixed) hk
    (by norm_num) hnon (by simpa only [sub_eq_add_neg, neg_div] using heq)
  exact fun z hz => hh hz

def ellipticReal : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ elliptic

theorem E_square : E*E=ellipticReal := by
  have hs : (Real.sqrt 10)^2=10 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E, ellipticReal, elliptic, SmallLevelNormalized.matrix,
      GeneralLinearGroup.mkOfDetNeZero, SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_10_ne] <;> nlinarith

#print axioms E_square
#print axioms elliptic_defect_zero

end SmallLevelThirtyC
