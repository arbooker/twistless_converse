module

public import SmallLevelOddFrickeV1
public import SmallLevelAnalyticRigidityTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelThirtyTwo

open Matrix ModularGroup Complex Filter Set
open scoped MatrixGroups Topology

def A : SL(2,ℤ) := ⟨!![3,1;8,3], by decide⟩

def elliptic : SL(2,ℚ) := ⟨!![3,1;-8,-7/3], by norm_num [det_fin_two]⟩

def fixedPoint : ℂ := ⟨-1/3, Real.sqrt 2/12⟩

theorem fixedPoint_positive : 0<fixedPoint.im := by
  change 0<Real.sqrt 2/12
  positivity

theorem fixedPoint_denom : (-8:ℂ)*fixedPoint-7/3≠0 := by
  intro h
  have hh := congrArg Complex.im h
  simp [fixedPoint] at hh

theorem fixedPoint_fixed : (3*fixedPoint+1)/(-8*fixedPoint-7/3)=fixedPoint := by
  apply (div_eq_iff fixedPoint_denom).mpr
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [fixedPoint, Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- The explicit elliptic matrix found in the level-thirty-two calculation
annihilates any positive-weight holomorphic invariant defect. -/
theorem elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F ((3*z+1)/(-8*z-7/3))=(-8*z-7/3)^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : (2/3:ℚ)≠m := by
    intro hm
    have hh : (3:ℚ)*m=2 := by rw [← hm]; norm_num
    have hi : (3:ℤ)*m=2 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 fixedPoint,
      F ((3*z+1)/(-8*z+(-7/3)))=(-8*z+(-7/3))^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds fixedPoint_positive] with z hz
    simpa only [sub_eq_add_neg, neg_div] using he z hz
  have hh := SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected fixedPoint_positive
    (a:=3) (b:=1) (c:= -8) (d:= -7/3) (t:=(2/3:ℚ))
    (by norm_num) (by simpa only [sub_eq_add_neg, neg_div] using fixedPoint_denom)
    (by simpa only [sub_eq_add_neg, neg_div] using fixedPoint_fixed) hk
    (by norm_num) hnon heq
  exact fun z hz => hh hz

#print axioms elliptic_defect_zero

end SmallLevelThirtyTwo
