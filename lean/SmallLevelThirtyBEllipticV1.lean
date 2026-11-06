module

public import SmallLevelThirtyBDefectV1
public import SmallLevelAnalyticRigidityTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelThirtyB

open Matrix ModularGroup Complex Filter Set
open scoped MatrixGroups Topology

def elliptic : SL(2,ℚ) := ⟨!![1,1/3;-10,-7/3], by norm_num [det_fin_two]⟩

def fixedPoint : ℂ := ⟨-5/30, Real.sqrt 5/30⟩

theorem fixedPoint_positive : 0<fixedPoint.im := by
  change 0<Real.sqrt 5/30
  positivity

theorem fixedPoint_denom : (-10:ℂ)*fixedPoint-7/3≠0 := by
  intro h
  have hh := congrArg Complex.im h
  simp [fixedPoint] at hh

theorem fixedPoint_fixed : (fixedPoint+1/3)/(-10*fixedPoint-7/3)=fixedPoint := by
  apply (div_eq_iff fixedPoint_denom).mpr
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [fixedPoint, Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- The explicit elliptic matrix found in the level-thirty modulus-six calculation
annihilates any positive-weight holomorphic invariant defect. -/
theorem elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F ((z+1/3)/(-10*z-7/3))=(-10*z-7/3)^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : (-4/3:ℚ)≠m := by
    intro hm
    have hh : (3:ℚ)*m= -4 := by rw [← hm]; norm_num
    have hi : (3:ℤ)*m= -4 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 fixedPoint,
      F ((z+1/3)/(-10*z-7/3))=(-10*z-7/3)^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds fixedPoint_positive] with z hz
    simpa only [sub_eq_add_neg, neg_div] using he z hz
  have hh := SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected fixedPoint_positive
    (a:=1) (b:=1/3) (c:= -10) (d:= -7/3) (t:=(-4/3:ℚ))
    (by norm_num) (by simpa only [sub_eq_add_neg, neg_div] using fixedPoint_denom)
    (by simpa only [one_mul, sub_eq_add_neg, neg_div] using fixedPoint_fixed) hk
    (by norm_num) hnon (by simpa only [one_mul, sub_eq_add_neg, neg_div] using heq)
  exact fun z hz => hh hz

def ellipticReal : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ elliptic

theorem E_square : E*E=ellipticReal := by
  have hs : (Real.sqrt 6)^2=6 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E, ellipticReal, elliptic, SmallLevelNormalized.matrix,
      GeneralLinearGroup.mkOfDetNeZero, SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_six_ne] <;> nlinarith

#print axioms E_square
#print axioms elliptic_defect_zero

end SmallLevelThirtyB
