module

public import SmallLevelTwentyFourDefectV1
public import SmallLevelAnalyticRigidityTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelTwentyFour

open Matrix ModularGroup Complex Filter Set
open scoped MatrixGroups Topology

def elliptic : SL(2,ℚ) := ⟨!![1,2/3;-4,-5/3], by norm_num [det_fin_two]⟩

def fixedPoint : ℂ := ⟨-2/6, Real.sqrt 2/6⟩

theorem fixedPoint_positive : 0<fixedPoint.im := by
  change 0<Real.sqrt 2/6
  positivity

theorem fixedPoint_denom : (-4:ℂ)*fixedPoint-5/3≠0 := by
  intro h
  have hh := congrArg Complex.im h
  simp [fixedPoint] at hh

theorem fixedPoint_fixed : (fixedPoint+2/3)/(-4*fixedPoint-5/3)=fixedPoint := by
  apply (div_eq_iff fixedPoint_denom).mpr
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [fixedPoint, Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- The explicit elliptic matrix found in the scaled level-twenty-four calculation
annihilates any positive-weight holomorphic invariant defect. -/
theorem elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F ((z+2/3)/(-4*z-5/3))=(-4*z-5/3)^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : (-2/3:ℚ)≠m := by
    intro hm
    have hh : (3:ℚ)*m= -2 := by rw [← hm]; norm_num
    have hi : (3:ℤ)*m= -2 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 fixedPoint,
      F ((z+2/3)/(-4*z-5/3))=(-4*z-5/3)^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds fixedPoint_positive] with z hz
    simpa only [sub_eq_add_neg, neg_div] using he z hz
  have hh := SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected fixedPoint_positive
    (a:=1) (b:=2/3) (c:= -4) (d:= -5/3) (t:=(-2/3:ℚ))
    (by norm_num) (by simpa only [sub_eq_add_neg, neg_div] using fixedPoint_denom)
    (by simpa only [one_mul, sub_eq_add_neg, neg_div] using fixedPoint_fixed) hk
    (by norm_num) hnon (by simpa only [one_mul, sub_eq_add_neg, neg_div] using heq)
  exact fun z hz => hh hz

def ellipticReal : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ elliptic

theorem E_square : E*E=ellipticReal := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E, ellipticReal, elliptic, SmallLevelNormalized.matrix,
      GeneralLinearGroup.mkOfDetNeZero, SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_three_ne] <;> nlinarith

#print axioms E_square
#print axioms elliptic_defect_zero

end SmallLevelTwentyFour
