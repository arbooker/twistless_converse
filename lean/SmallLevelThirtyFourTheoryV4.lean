module

public import SmallLevelAnalyticRigidityTheoryV4
public import SmallLevelDoubleCosetDefectV1
public import SmallLevelSixPairV1

/-! Consolidated chapter: SmallLevelThirtyFour. Original declarations and local scopes are retained. -/

/-! ## SmallLevelThirtyFourBranchesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelThirtyFour

open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem sqrt_norm_ne : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'

def A : GL (Fin 2) ℝ := matrix (6/Real.sqrt 2) (1/Real.sqrt 2)
    (34/Real.sqrt 2) (6/Real.sqrt 2) (by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_norm_ne]
  nlinarith)

def B : GL (Fin 2) ℝ := matrix (6/Real.sqrt 2) (-1/Real.sqrt 2)
    (-34/Real.sqrt 2) (6/Real.sqrt 2) (by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_norm_ne]
  nlinarith)

theorem A_det : (GeneralLinearGroup.det A:ℝ)=1 := matrix_det _ _ _ _ _
theorem B_det : (GeneralLinearGroup.det B:ℝ)=1 := matrix_det _ _ _ _ _

theorem sqrt_conductor : Real.sqrt 612=3*Real.sqrt 34*Real.sqrt 2 := by
  rw [mul_assoc, ← Real.sqrt_mul (by norm_num : (0:ℝ)≤34)]
  rw [show (612:ℝ)=9*(34*2) by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem fricke_branch_pos : fricke 34 (by decide)*B*translation (1/6)=
    translation (1/6)*fricke 612 (by decide) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke, B, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two, sqrt_conductor] <;>
    field_simp [sqrt_norm_ne, hn] <;> norm_num [hs, ht]

theorem fricke_branch_neg : fricke 34 (by decide)*A*translation (-(1/6))=
    translation (-(1/6))*fricke 612 (by decide) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke, A, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two, sqrt_conductor] <;>
    field_simp [sqrt_norm_ne, hn] <;> norm_num [hs, ht]

/-- The actual modulus-six pair, with the same original root sign on
both branches and no restriction on a Hecke eigenvalue. -/
theorem original_pair {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 k f) :
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] B) ∣[(k:ℤ)] translation (1/6))+
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A) ∣[(k:ℤ)] translation (-(1/6)))=
    FinitenessNormalizedTwistProduct.root 34 f 6 • ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/6))+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(1/6)))) := by
  have hh := original_six_pair (by decide : 0<34) (by decide : 0<612) (by decide) hf
  have hp : (fricke 34 (by decide))⁻¹*translation (1/6)*fricke 612 (by decide)=B*translation (1/6) := by
    rw [mul_assoc, ← fricke_branch_pos]
    group
  have hn : (fricke 34 (by decide))⁻¹*translation (-(1/6))*fricke 612 (by decide)=A*translation (-(1/6)) := by
    rw [mul_assoc, ← fricke_branch_neg]
    group
  rw [hp, hn, SlashAction.slash_mul, SlashAction.slash_mul] at hh
  exact hh

#print axioms fricke_branch_pos
#print axioms fricke_branch_neg
#print axioms original_pair

end SmallLevelThirtyFour
end
end

/-! ## SmallLevelThirtyFourDefectV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelThirtyFour

open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelGenerators
open scoped MatrixGroups ModularForm

def E : GL (Fin 2) ℝ := matrix (6/Real.sqrt 2) (1/Real.sqrt 2)
    (-34/Real.sqrt 2) (-(16/3)/Real.sqrt 2) (by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_norm_ne]
  nlinarith)

theorem E_det : (GeneralLinearGroup.det E:ℝ)=1 := matrix_det _ _ _ _ _

theorem B_A : B*A=1 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, B, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_norm_ne] <;> nlinarith

theorem A_E : A*E=translation (2/6) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, E, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_norm_ne] <;> nlinarith

theorem E_branch : E*translation (-(1/6))=A⁻¹*translation (1/6) := by
  apply mul_left_cancel (a:=A)
  rw [← mul_assoc, A_E, translation_mul]
  rw [← mul_assoc, mul_inv_cancel, one_mul]
  norm_num

theorem B_inverse : B=A⁻¹ := by
  have h := congrArg (fun x : GL (Fin 2) ℝ => x*A⁻¹) B_A
  simpa only [mul_assoc, mul_inv_cancel, mul_one, one_mul] using h

/-- The exact original root gives the elliptic-square invariance of the defect. -/
theorem actual_defect_square {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 k f) :
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A)-
      FinitenessNormalizedTwistProduct.root 34 f 6 • SmallLevelOriginal.fourierFunction k f)
      ∣[(k:ℤ)] (E*E)=
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A)-
      FinitenessNormalizedTwistProduct.root 34 f 6 • SmallLevelOriginal.fourierFunction k f := by
  apply double_coset_defect _ _ A B 1 1 E (by simp) A_det E_det 1
    (FinitenessNormalizedTwistProduct.root 34 f 6) (Or.inl rfl)
    (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 6)
    (by simp) (by simp) (by simpa using B_inverse) (-(1/6))
  · simpa only [mul_one,neg_neg] using E_branch
  · simpa only [neg_neg,add_comm] using original_pair hf

#print axioms B_inverse
#print axioms actual_defect_square

end SmallLevelThirtyFour
end
end

/-! ## SmallLevelThirtyFourEllipticV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelThirtyFour

open Matrix ModularGroup Complex Filter Set
open scoped MatrixGroups Topology

def elliptic : SL(2,ℚ) := ⟨!![1,1/3;-34/3,-25/9], by norm_num [det_fin_two]⟩

def fixedPoint : ℂ := ⟨-1/6, Real.sqrt 17/102⟩

theorem fixedPoint_positive : 0<fixedPoint.im := by
  change 0<Real.sqrt 17/102
  positivity

theorem fixedPoint_denom : (-34/3:ℂ)*fixedPoint-25/9≠0 := by
  intro h
  have hh := congrArg Complex.im h
  simp [fixedPoint] at hh

theorem fixedPoint_fixed : (fixedPoint+1/3)/((-34/3)*fixedPoint-25/9)=fixedPoint := by
  apply (div_eq_iff fixedPoint_denom).mpr
  have hs : (Real.sqrt 17)^2=17 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [fixedPoint, Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- The explicit elliptic matrix found in the level-thirty-four modulus-six calculation
annihilates any positive-weight holomorphic invariant defect. -/
theorem elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F ((z+1/3)/((-34/3)*z-25/9))=((-34/3)*z-25/9)^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : (-16/9:ℚ)≠m := by
    intro hm
    have hh : (9:ℚ)*m= -16 := by rw [← hm]; norm_num
    have hi : (9:ℤ)*m= -16 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 fixedPoint,
      F ((z+1/3)/((-34/3)*z-25/9))=((-34/3)*z-25/9)^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds fixedPoint_positive] with z hz
    simpa only [sub_eq_add_neg, neg_div,one_mul] using he z hz
  have hh := SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected fixedPoint_positive
    (a:=1) (b:=1/3) (c:= -34/3) (d:= -25/9) (t:=(-16/9:ℚ))
    (by norm_num) (by simpa only [sub_eq_add_neg, neg_div,one_mul] using fixedPoint_denom)
    (by simpa only [sub_eq_add_neg, neg_div,one_mul] using fixedPoint_fixed) hk
    (by norm_num) hnon (by simpa only [sub_eq_add_neg, neg_div,one_mul] using heq)
  exact fun z hz => hh hz

def ellipticReal : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ elliptic

theorem E_square : E*E=ellipticReal := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E, ellipticReal, elliptic, SmallLevelNormalized.matrix,
      GeneralLinearGroup.mkOfDetNeZero, SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_norm_ne] <;> nlinarith

#print axioms E_square
#print axioms elliptic_defect_zero

end SmallLevelThirtyFour
end
end

/-! ## SmallLevelThirtyFourRigidityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelThirtyFour

open Matrix UpperHalfPlane ModularGroup
open scoped MatrixGroups ModularForm Manifold

theorem ellipticReal_det : (GeneralLinearGroup.det ellipticReal : ℝ)=1 := by
  simp [ellipticReal]

theorem ellipticReal_denom (z : ℍ) : denom ellipticReal z= (-34/3)*(z:ℂ)-25/9 := by
  norm_num [denom, ellipticReal, elliptic, SpecialLinearGroup.toGL,
    SpecialLinearGroup.map_apply_coe]
  ring

theorem ellipticReal_point (z : ℍ) :
    ((ellipticReal • z : ℍ):ℂ)=((z:ℂ)+1/3)/((-34/3)*(z:ℂ)-25/9) := by
  rw [coe_smul_of_det_pos (by rw [ellipticReal_det]; norm_num)]
  norm_num [num, denom, ellipticReal, elliptic, SpecialLinearGroup.toGL,
    SpecialLinearGroup.map_apply_coe]
  ring

theorem invariant_zero {k : ℕ} (hk : 0<k) (H : ℍ → ℂ)
    (hhol : MDiff H) (he : H ∣[(k:ℤ)] ellipticReal=H) : H=0 := by
  let F : ℂ → ℂ := H ∘ ofComplex
  have hr (w : ℍ) : H w=F (w:ℂ) := by simp [F]
  have ha : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hhol).analyticOnNhd isOpen_upperHalfPlaneSet
  have htrans (z : ℂ) (hz : 0<z.im) :
      F ((z+1/3)/((-34/3)*z-25/9))=((-34/3)*z-25/9)^k*F z := by
    let w : ℍ := ⟨z,hz⟩
    have hh := congrFun he w
    rw [ModularForm.slash_apply] at hh
    have hs : σ ellipticReal=ContinuousAlgEquiv.refl ℝ ℂ := by
      simp only [σ, ellipticReal_det]; norm_num
    rw [hs, ellipticReal_det, ellipticReal_denom] at hh
    norm_num only [ContinuousAlgEquiv.refl_apply, abs_one, Complex.ofReal_one,
      one_zpow, mul_one, zpow_neg, zpow_natCast] at hh
    rw [hr, hr, ellipticReal_point] at hh
    simp only [← neg_div] at hh
    change F ((z+1/3)/((-34/3)*z-25/9))*(((-34/3)*z-25/9)^k)⁻¹=F z at hh
    have hd : ((-34/3)*z-25/9:ℂ)≠0 := by
      simpa only [ellipticReal_denom] using denom_ne_zero ellipticReal w
    have hx := congrArg (fun v : ℂ => v*((-34/3)*z-25/9)^k) hh
    simp only [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hd), mul_one] at hx
    simpa only [mul_comm] using hx
  funext z
  rw [hr]
  exact elliptic_defect_zero ha hk htrans z z.im_pos

/-- Original input forces the modulus-six eigenmatrix at every positive weight. -/
theorem original_A {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A=
      FinitenessNormalizedTwistProduct.root 34 f 6 • SmallLevelOriginal.fourierFunction k f := by
  have he := actual_defect_square hf
  rw [E_square] at he
  have hhol := SmallLevelOriginal.fourierFunction_holomorphic hf
  have hs : MDiff (FinitenessNormalizedTwistProduct.root 34 f 6 •
      SmallLevelOriginal.fourierFunction k f) := by
    rcases FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 6 with h|h
    · rw [h]; simpa only [one_smul] using hhol
    · rw [h]; simpa only [neg_one_smul] using hhol.neg
  have hd := (hhol.slash (k:ℤ) A).sub hs
  exact sub_eq_zero.mp (invariant_zero hk _ hd he)

#print axioms invariant_zero
#print axioms original_A

end SmallLevelThirtyFour
end
end
