module

public import SmallLevelFourteenMatricesV1
public import SmallLevelAnalyticRigidityTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelFourteen

open Matrix ModularGroup Complex Filter Set
open scoped MatrixGroups Topology

def A : SL(2,ℤ) := ⟨!![3,1;14,5], by decide⟩

def B : SL(2,ℤ) := ⟨!![3,-1;-14,5], by decide⟩

theorem matrix_relation : B=(kernel 2)⁻¹*((-1)*kernel 1)*T*A⁻¹ := by decide

def elliptic : SL(2,ℚ) := ⟨!![5,7/3;-14,-19/3], by norm_num [det_fin_two]⟩

def fixedPoint : ℂ := ⟨-17/42, Real.sqrt 5/42⟩

theorem fixedPoint_positive : 0<fixedPoint.im := by
  change 0<Real.sqrt 5/42
  positivity

theorem fixedPoint_denom : (-14:ℂ)*fixedPoint-19/3≠0 := by
  intro h
  have hh := congrArg Complex.im h
  simp [fixedPoint] at hh

theorem fixedPoint_fixed : (5*fixedPoint+7/3)/(-14*fixedPoint-19/3)=fixedPoint := by
  apply (div_eq_iff fixedPoint_denom).mpr
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [fixedPoint, Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- The explicit elliptic matrix found in the level-fourteen calculation
annihilates any positive-weight holomorphic invariant defect. -/
theorem elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F ((5*z+7/3)/(-14*z-19/3))=(-14*z-19/3)^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : (-4/3:ℚ)≠m := by
    intro hm
    have hh : (3:ℚ)*m= -4 := by rw [← hm]; norm_num
    have hi : (3:ℤ)*m= -4 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 fixedPoint,
      F ((5*z+7/3)/(-14*z+(-19/3)))=(-14*z+(-19/3))^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds fixedPoint_positive] with z hz
    simpa only [sub_eq_add_neg, neg_div] using he z hz
  have hh := SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected fixedPoint_positive
    (a:=5) (b:=7/3) (c:= -14) (d:= -19/3) (t:=(-4/3:ℚ))
    (by norm_num) (by simpa only [sub_eq_add_neg, neg_div] using fixedPoint_denom)
    (by simpa only [sub_eq_add_neg, neg_div] using fixedPoint_fixed) hk
    (by norm_num) hnon heq
  exact fun z hz => hh hz

#print axioms elliptic_defect_zero

end SmallLevelFourteen
