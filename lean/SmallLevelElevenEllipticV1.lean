module

public import SmallLevelOddFrickeV1
public import SmallLevelAnalyticRigidityTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelEleven

open Matrix ModularGroup Complex Filter Set
open scoped MatrixGroups Topology

def A : SL(2,ℤ) := ⟨!![3,1;11,4], by decide⟩
def B : SL(2,ℤ) := ⟨!![3,-1;-11,4], by decide⟩

/-- Exact relation between the two modulus-three matrices and the already
available modulus-two transformation. -/
theorem matrix_relation : B=
    (-1)*(SmallLevelGenerators.oddMatrix 11 6 (by decide))⁻¹*T*A⁻¹ := by decide

def elliptic : SL(2,ℚ) := ⟨!![4,5/3;-11,-13/3], by norm_num [det_fin_two]⟩

def translation : SL(2,ℚ) := ⟨!![1,2/3;0,1], by norm_num [det_fin_two]⟩

theorem elliptic_factor : elliptic=
    (SpecialLinearGroup.map (Int.castRingHom ℚ) A)⁻¹*translation := by
  rw [← map_inv]
  have hi : A⁻¹=(⟨!![4,-1;-11,3],by decide⟩ : SL(2,ℤ)) := by decide
  rw [hi]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [elliptic, translation, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Fin.sum_univ_two]

def fixedPoint : ℂ := ⟨-25/66, Real.sqrt 35/66⟩

theorem fixedPoint_positive : 0<fixedPoint.im := by
  change 0<Real.sqrt 35/66
  positivity

theorem fixedPoint_denom : (-11:ℂ)*fixedPoint-13/3≠0 := by
  intro h
  have hh := congrArg Complex.im h
  simp [fixedPoint] at hh

theorem fixedPoint_fixed : (4*fixedPoint+5/3)/(-11*fixedPoint-13/3)=fixedPoint := by
  apply (div_eq_iff fixedPoint_denom).mpr
  have hs : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [fixedPoint, Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- The explicit elliptic matrix found in the level-eleven calculation
annihilates any positive-weight holomorphic invariant defect. -/
theorem elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F ((4*z+5/3)/(-11*z-13/3))=(-11*z-13/3)^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : (-1/3:ℚ)≠m := by
    intro hm
    have hh : (3:ℚ)*m= -1 := by rw [← hm]; norm_num
    have hi : (3:ℤ)*m= -1 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 fixedPoint,
      F ((4*z+5/3)/(-11*z+(-13/3)))=(-11*z+(-13/3))^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds fixedPoint_positive] with z hz
    simpa only [sub_eq_add_neg, neg_div] using he z hz
  have hh := SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected fixedPoint_positive
    (a:=4) (b:=5/3) (c:= -11) (d:= -13/3) (t:=(-1/3:ℚ))
    (by norm_num) (by simpa only [sub_eq_add_neg, neg_div] using fixedPoint_denom)
    (by simpa only [sub_eq_add_neg, neg_div] using fixedPoint_fixed) hk
    (by norm_num) hnon heq
  exact fun z hz => hh hz

#print axioms matrix_relation
#print axioms elliptic_factor
#print axioms elliptic_defect_zero

end SmallLevelEleven
