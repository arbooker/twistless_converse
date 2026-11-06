module

public import SmallLevelAnalyticRigidityTheoryV4
public import SmallLevelElevenDefectV1
public import SmallLevelModularCriterionV1
public import SmallLevelOddWordsV1
public import SmallLevelSixPairV1
public import SmallLevelThreeSlashV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyThree. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyThreePairsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelTwentyThree

open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelThree
open scoped MatrixGroups ModularForm

def A : SL(2,ℤ) := ⟨!![4,-1;-23,6], by decide⟩
def B : SL(2,ℤ) := ⟨!![6,-1;-23,4], by decide⟩

theorem A_inv : A⁻¹ = (⟨!![6,1;23,4], by decide⟩ : SL(2,ℤ)) := by decide
theorem B_inv : B⁻¹ = (⟨!![4,1;23,6], by decide⟩ : SL(2,ℤ)) := by decide

theorem root_four (f : ℕ → ℂ) : FinitenessNormalizedTwistProduct.root 23 f 4 = 1 := by
  have hp : Nat.primeFactors 4 = {2} := by
    rw [show (4:ℕ)=2*2 by norm_num, Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  simp [FinitenessNormalizedTwistProduct.root, hp, FinitenessNormalizedTwistLocal.sign]

theorem original_four_pair {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 23 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 23 (by decide))⁻¹*translation (1/4)*fricke 368 (by decide)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 23 (by decide))⁻¹*translation (-(1/4))*fricke 368 (by decide)))=
    FinitenessNormalizedTwistProduct.root 23 f 4 •
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/4))+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(1/4)))) := by
  obtain ⟨ε, _, hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<23) hf
  apply pair_of_fricke 23 368 k (by decide) (by decide) (1/4)
    (FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f k))
    (ε*Complex.I^k) _ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 4)
  · intro z hz
    simpa [FinitenessNormalizedTwistProduct.root, FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  · intro z hz
    have h := hlaw 4 (by decide) z hz
    rw [show Nat.lcm 23 (4^2)=368 by decide,
      SmallLevelThirty.twist_four _ (FinitenessFourierConstruction.periodic _),
      SmallLevelThirty.twist_four _ (FinitenessFourierConstruction.periodic _)] at h
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_assoc] using h

theorem sqrt_conductor_four : Real.sqrt 368 = 4 * Real.sqrt 23 := by
  rw [show (368:ℝ)=16*23 by norm_num, Real.sqrt_mul (by norm_num)]
  norm_num

theorem four_positive : fricke 23 (by decide) * SpecialLinearGroup.mapGL ℝ A *
    translation (1/4) = translation (1/4) * fricke 368 (by decide) := by
  have ht : (Real.sqrt 23)^2=23 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 23≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke, A, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, sqrt_conductor_four] <;>
    field_simp [hn] <;> norm_num [ht]

theorem four_negative : fricke 23 (by decide) * SpecialLinearGroup.mapGL ℝ B⁻¹ *
    translation (-(1/4)) = translation (-(1/4)) * fricke 368 (by decide) := by
  rw [B_inv]
  have ht : (Real.sqrt 23)^2=23 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 23≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, sqrt_conductor_four] <;>
    field_simp [hn] <;> norm_num [ht]

theorem original_four_reduced {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 23 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A) +
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] B⁻¹) ∣[(k:ℤ)] translation (-1/2)) =
    SmallLevelOriginal.fourierFunction k f +
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-1/2)) := by
  have h := original_four_pair hf
  have hp : (fricke 23 (by decide))⁻¹ * translation (1/4) * fricke 368 (by decide) =
      SpecialLinearGroup.mapGL ℝ A * translation (1/4) := by
    rw [mul_assoc, ← four_positive]
    group
  have hn : (fricke 23 (by decide))⁻¹ * translation (-(1/4)) * fricke 368 (by decide) =
      SpecialLinearGroup.mapGL ℝ B⁻¹ * translation (-(1/4)) := by
    rw [mul_assoc, ← four_negative]
    group
  rw [hp, hn, root_four, one_smul] at h
  have hh := congrArg (fun F : ℍ → ℂ => F ∣[(k:ℤ)] translation (-(1/4))) h
  simp only [SlashAction.add_slash, ← SlashAction.slash_mul, mul_assoc, translation_mul] at hh
  norm_num only [show (1/4:ℝ)+ -(1/4)=0 by ring,
    show (-(1/4):ℝ)+ -(1/4)= -1/2 by ring] at hh
  have ht : translation 0 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translation, matrix, GeneralLinearGroup.mkOfDetNeZero]
  change (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ A) +
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ B⁻¹) ∣[(k:ℤ)] translation (-1/2)) = _
  simpa only [ht, mul_one, SlashAction.slash_one, SlashAction.slash_mul, neg_div] using hh

theorem sqrt_conductor_six : Real.sqrt 828 = 6 * Real.sqrt 23 := by
  rw [show (828:ℝ)=36*23 by norm_num, Real.sqrt_mul (by norm_num)]
  norm_num

theorem six_positive : fricke 23 (by decide) * SpecialLinearGroup.mapGL ℝ B *
    translation (1/6) = translation (1/6) * fricke 828 (by decide) := by
  have ht : (Real.sqrt 23)^2=23 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 23≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke, B, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, sqrt_conductor_six] <;>
    field_simp [hn] <;> norm_num [ht]

theorem six_negative : fricke 23 (by decide) * SpecialLinearGroup.mapGL ℝ A⁻¹ *
    translation (-(1/6)) = translation (-(1/6)) * fricke 828 (by decide) := by
  rw [A_inv]
  have ht : (Real.sqrt 23)^2=23 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 23≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, sqrt_conductor_six] <;>
    field_simp [hn] <;> norm_num [ht]

theorem root_six (f : ℕ → ℂ) : FinitenessNormalizedTwistProduct.root 23 f 6 = 1 := by
  have hp : Nat.primeFactors 6 = {2,3} := by
    rw [show (6:ℕ)=2*3 by norm_num, Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  simp [FinitenessNormalizedTwistProduct.root, hp, FinitenessNormalizedTwistLocal.sign]

theorem original_six_reduced {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 23 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] B) +
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A⁻¹) ∣[(k:ℤ)] translation (-1/3)) =
    SmallLevelOriginal.fourierFunction k f +
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-1/3)) := by
  have h := original_six_pair (by decide : 0<23) (by decide : 0<828) (by decide) hf
  have hp : (fricke 23 (by decide))⁻¹ * translation (1/6) * fricke 828 (by decide) =
      SpecialLinearGroup.mapGL ℝ B * translation (1/6) := by
    rw [mul_assoc, ← six_positive]
    group
  have hn : (fricke 23 (by decide))⁻¹ * translation (-(1/6)) * fricke 828 (by decide) =
      SpecialLinearGroup.mapGL ℝ A⁻¹ * translation (-(1/6)) := by
    rw [mul_assoc, ← six_negative]
    group
  rw [hp, hn, root_six, one_smul] at h
  have hh := congrArg (fun F : ℍ → ℂ => F ∣[(k:ℤ)] translation (-(1/6))) h
  simp only [SlashAction.add_slash, ← SlashAction.slash_mul, mul_assoc, translation_mul] at hh
  norm_num only [show (1/6:ℝ)+ -(1/6)=0 by ring,
    show (-(1/6):ℝ)+ -(1/6)= -1/3 by ring] at hh
  have ht : translation 0 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translation, matrix, GeneralLinearGroup.mkOfDetNeZero]
  change (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ B) +
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ A⁻¹) ∣[(k:ℤ)] translation (-1/3)) = _
  simpa only [ht, mul_one, SlashAction.slash_one, SlashAction.slash_mul, neg_div] using hh

#print axioms original_four_reduced
#print axioms original_six_reduced

end QuantitativeArithmeticSmallLevelTwentyThree
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyThreeRigidityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelTwentyThree

open Matrix UpperHalfPlane SmallLevelNormalized Complex Filter Set
open scoped MatrixGroups ModularForm Manifold Topology

def elliptic : SL(2,ℚ) := ⟨!![1,-1/2;23/3,-17/6], by norm_num [det_fin_two]⟩
def ellipticReal : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ elliptic

theorem elliptic_factor : ellipticReal =
    SpecialLinearGroup.mapGL ℝ A⁻¹ * translation (-1/3) *
      SpecialLinearGroup.mapGL ℝ B⁻¹ * translation (-1/2) := by
  rw [A_inv, B_inv]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ellipticReal, elliptic, SmallLevelNormalized.translation, SmallLevelNormalized.matrix, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Two paired Ramanujan equations transport the two transformation defects
into each other. The algebra requires no division by any eigenvalue. -/
theorem pair_transport (g : ℍ → ℂ) (k : ℤ) (C D R : GL (Fin 2) ℝ)
    (hp : (g ∣[k] C) + ((g ∣[k] D⁻¹) ∣[k] R) = g + (g ∣[k] R)) :
    (g ∣[k] C) - g = ((g ∣[k] D) - g) ∣[k] (D⁻¹ * R) := by
  simp only [SmallLevelEleven.sub_slash, ← SlashAction.slash_mul,
    ← mul_assoc, mul_inv_cancel, one_mul]
  rw [SlashAction.slash_mul]
  linear_combination hp

theorem original_defect_elliptic {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 23 k f) :
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A) -
      SmallLevelOriginal.fourierFunction k f) ∣[(k:ℤ)] ellipticReal =
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A) -
      SmallLevelOriginal.fourierFunction k f := by
  let g := SmallLevelOriginal.fourierFunction k f
  let a := SpecialLinearGroup.mapGL ℝ A
  let b := SpecialLinearGroup.mapGL ℝ B
  have h3 : (g ∣[(k:ℤ)] a) + ((g ∣[(k:ℤ)] b⁻¹) ∣[(k:ℤ)] translation (-1/2)) =
      g + (g ∣[(k:ℤ)] translation (-1/2)) := by
    rw [show b⁻¹=SpecialLinearGroup.mapGL ℝ B⁻¹ from (map_inv _ _).symm]
    exact original_four_reduced hf
  have h6 : (g ∣[(k:ℤ)] b) + ((g ∣[(k:ℤ)] a⁻¹) ∣[(k:ℤ)] translation (-1/3)) =
      g + (g ∣[(k:ℤ)] translation (-1/3)) := by
    rw [show a⁻¹=SpecialLinearGroup.mapGL ℝ A⁻¹ from (map_inv _ _).symm]
    exact original_six_reduced hf
  have ht3 := pair_transport g k a b (translation (-1/2)) h3
  have ht6 := pair_transport g k b a (translation (-1/3)) h6
  have he : ellipticReal = (a⁻¹ * translation (-1/3)) * (b⁻¹ * translation (-1/2)) := by
    simpa only [a, b, map_inv, mul_assoc] using elliptic_factor
  change ((g ∣[(k:ℤ)] a)-g) ∣[(k:ℤ)] ellipticReal = (g ∣[(k:ℤ)] a)-g
  rw [he, SlashAction.slash_mul, ← ht6, ← ht3]

def fixedPoint : ℂ := ⟨1/4, Real.sqrt 23/92⟩

theorem fixedPoint_positive : 0 < fixedPoint.im := by
  change 0 < Real.sqrt 23/92
  positivity

theorem fixedPoint_denom : (23/3:ℂ)*fixedPoint-17/6 ≠ 0 := by
  intro h
  have hh := congrArg Complex.im h
  simp [fixedPoint] at hh

theorem fixedPoint_fixed : (fixedPoint-1/2)/((23/3)*fixedPoint-17/6) = fixedPoint := by
  apply (div_eq_iff fixedPoint_denom).mpr
  have hs : (Real.sqrt 23)^2=23 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [fixedPoint, Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F ((z-1/2)/((23/3)*z-17/6))=((23/3)*z-17/6)^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : (-11/6:ℚ)≠m := by
    intro hm
    have hh : (6:ℚ)*m = -11 := by rw [← hm]; norm_num
    have hi : (6:ℤ)*m = -11 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 fixedPoint,
      F ((1*z+(-1/2))/((23/3)*z+(-17/6)))=((23/3)*z+(-17/6))^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds fixedPoint_positive] with z hz
    simpa only [one_mul, sub_eq_add_neg, neg_div] using he z hz
  have hh := SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected fixedPoint_positive
    (a:=1) (b:= -1/2) (c:=23/3) (d:= -17/6) (t:=(-11/6:ℚ))
    (by norm_num) (by simpa only [sub_eq_add_neg, neg_div] using fixedPoint_denom)
    (by simpa only [one_mul, sub_eq_add_neg, neg_div] using fixedPoint_fixed) hk
    (by norm_num) hnon heq
  exact fun z hz => hh hz

theorem ellipticReal_det : (GeneralLinearGroup.det ellipticReal:ℝ)=1 := by
  simp [ellipticReal]

theorem ellipticReal_denom (z : ℍ) : denom ellipticReal z = (23/3)*(z:ℂ)-17/6 := by
  norm_num [denom, ellipticReal, elliptic, SpecialLinearGroup.toGL,
    SpecialLinearGroup.map_apply_coe]
  ring

theorem ellipticReal_point (z : ℍ) :
    ((ellipticReal • z : ℍ):ℂ)=((z:ℂ)-1/2)/((23/3)*(z:ℂ)-17/6) := by
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
      F ((z-1/2)/((23/3)*z-17/6))=((23/3)*z-17/6)^k*F z := by
    let w : ℍ := ⟨z,hz⟩
    have hh := congrFun he w
    rw [ModularForm.slash_apply] at hh
    have hs : σ ellipticReal=ContinuousAlgEquiv.refl ℝ ℂ := by
      simp only [σ, ellipticReal_det]; norm_num
    rw [hs, ellipticReal_det, ellipticReal_denom] at hh
    norm_num only [ContinuousAlgEquiv.refl_apply, abs_one, Complex.ofReal_one,
      one_zpow, mul_one, zpow_neg, zpow_natCast] at hh
    rw [hr, hr, ellipticReal_point] at hh
    change F ((z-1/2)/((23/3)*z-17/6))*(((23/3)*z-17/6)^k)⁻¹=F z at hh
    have hd : ((23/3)*z-17/6:ℂ)≠0 := by
      simpa only [ellipticReal_denom] using denom_ne_zero ellipticReal w
    have hx := congrArg (fun v : ℂ => v*((23/3)*z-17/6)^k) hh
    simp only [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hd), mul_one] at hx
    simpa only [mul_comm] using hx
  funext z
  rw [hr]
  exact elliptic_defect_zero ha hk htrans z z.im_pos

theorem original_A {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 23 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A =
      SmallLevelOriginal.fourierFunction k f := by
  have hhol := SmallLevelOriginal.fourierFunction_holomorphic hf
  have hd := (hhol.slash (k:ℤ) (SpecialLinearGroup.mapGL ℝ A)).sub hhol
  exact sub_eq_zero.mp (invariant_zero hk _ hd (original_defect_elliptic hf))

theorem original_B {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 23 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] B =
      SmallLevelOriginal.fourierFunction k f := by
  have ha := original_A hk hf
  have hi := congrArg (fun F : ℍ → ℂ => F ∣[(k:ℤ)] A⁻¹) ha
  simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] at hi
  have hh := original_six_reduced hf
  rw [← hi] at hh
  exact add_right_cancel hh

#print axioms original_defect_elliptic
#print axioms elliptic_defect_zero
#print axioms original_A
#print axioms original_B

end QuantitativeArithmeticSmallLevelTwentyThree
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyThreeExtraV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelTwentyThree

open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelThree SmallLevelGenerators
open scoped MatrixGroups ModularForm

def C : SL(2,ℤ) := ⟨!![10,3;23,7], by decide⟩
def D : SL(2,ℤ) := ⟨!![3,-1;-23,8], by decide⟩
def Dp : SL(2,ℤ) := ⟨!![3,1;23,8], by decide⟩

theorem D_relation : D = (-1)*A*B⁻¹*C⁻¹ := by decide
theorem Dp_relation : Dp = (-1)*lower 23*(oddMatrix 23 12 (by decide))⁻¹*C := by decide

theorem three_positive : lowerBranch 23 1 =
    SpecialLinearGroup.mapGL ℝ Dp * upperBranch (-1) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerBranch, upperBranch, Dp, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem three_negative : lowerBranch 23 (-1) =
    SpecialLinearGroup.mapGL ℝ D * upperBranch 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerBranch, upperBranch, D, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem three_ratio : upperBranch (-1) * (upperBranch 1)⁻¹ = translation (-2/3) := by
  apply (mul_right_cancel_iff (a := upperBranch 1)).mp
  rw [inv_mul_cancel_right]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperBranch, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem original_three_reduced {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 23 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] D) +
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] Dp) ∣[(k:ℤ)] translation (-2/3)) =
    SmallLevelOriginal.fourierFunction k f +
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-2/3)) := by
  have h := original_pair_slash (by decide : 0 < 23) (by decide) hf
  rw [three_positive, three_negative, SlashAction.slash_mul, SlashAction.slash_mul] at h
  have hh := congrArg (fun F : ℍ → ℂ => F ∣[(k:ℤ)] (upperBranch 1)⁻¹) h
  simp only [SlashAction.add_slash, ← SlashAction.slash_mul, mul_inv_cancel,
    SlashAction.slash_one, mul_assoc, three_ratio] at hh
  change (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ D) +
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ Dp) ∣[(k:ℤ)] translation (-2/3)) = _
  simpa only [SlashAction.slash_mul, SlashAction.slash_one, add_comm] using hh.symm

theorem original_D_action (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 23 (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] D =
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] C⁻¹ := by
  have ha := original_A (by omega : 0<2*m) hf
  have hb := original_B (by omega : 0<2*m) hf
  have hi := congrArg (fun F : ℍ → ℂ => F ∣[((2*m:ℕ):ℤ)] B⁻¹) hb
  simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] at hi
  rw [D_relation]
  simp only [SlashAction.slash_mul, SmallLevelThirtySix.slash_neg_one_even, ha, ← hi]

theorem original_Dp_action (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 23 (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Dp =
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] C := by
  have h2 := original_odd (by decide : 0<23) (by decide : 2*12=23+1) (by decide) hf
  have hi := congrArg (fun F : ℍ → ℂ =>
    F ∣[((2*m:ℕ):ℤ)] (oddMatrix 23 12 (by decide))⁻¹) h2
  simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] at hi
  rw [Dp_relation]
  simp only [SlashAction.slash_mul, SmallLevelThirtySix.slash_neg_one_even,
    original_lower (by decide : 0<23) hf, ← hi]

def extraElliptic : SL(2,ℚ) := ⟨!![7,5/3;-23,-16/3], by norm_num [det_fin_two]⟩
def extraEllipticReal : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ extraElliptic

theorem extra_factor : extraEllipticReal = SpecialLinearGroup.mapGL ℝ C⁻¹ * translation (2/3) := by
  have hi : C⁻¹ = (⟨!![7,-3;-23,10], by decide⟩ : SL(2,ℤ)) := by decide
  rw [hi]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [extraEllipticReal, extraElliptic, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem original_extra_defect (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 23 (2*m) f) :
    ((SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] C)-
      SmallLevelOriginal.fourierFunction (2*m) f) ∣[((2*m:ℕ):ℤ)] extraEllipticReal =
    (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] C)-
      SmallLevelOriginal.fourierFunction (2*m) f := by
  let g := SmallLevelOriginal.fourierFunction (2*m) f
  have h := original_three_reduced hf
  rw [original_D_action m hm hf, original_Dp_action m hf] at h
  have hh := congrArg (fun F : ℍ → ℂ => F ∣[((2*m:ℕ):ℤ)] translation (2/3)) h
  have ht : translation (-2/3) * translation (2/3) = 1 := by
    rw [translation_mul]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translation, matrix, GeneralLinearGroup.mkOfDetNeZero]
  simp only [SlashAction.add_slash, ← SlashAction.slash_mul, ht,
    SlashAction.slash_one] at hh
  change ((g ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ C)-g) ∣[((2*m:ℕ):ℤ)] extraEllipticReal =
    (g ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ C)-g
  rw [extra_factor]
  simp only [SmallLevelEleven.sub_slash, ← SlashAction.slash_mul, ← mul_assoc,
    ← map_mul, mul_inv_cancel, map_one, one_mul]
  change g ∣[((2*m:ℕ):ℤ)] translation (2/3) -
    (g ∣[((2*m:ℕ):ℤ)] (SpecialLinearGroup.mapGL ℝ C⁻¹ * translation (2/3))) =
    (g ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ C)-g
  rw [SlashAction.slash_mul]
  linear_combination -hh

#print axioms original_three_reduced
#print axioms original_extra_defect

end QuantitativeArithmeticSmallLevelTwentyThree
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyThreeFinalRigidityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelTwentyThree

open Matrix UpperHalfPlane Complex Filter Set
open scoped MatrixGroups ModularForm Manifold Topology

def extraFixedPoint : ℂ := ⟨-37/138, Real.sqrt 11/138⟩

theorem extraFixedPoint_positive : 0 < extraFixedPoint.im := by
  change 0 < Real.sqrt 11/138
  positivity

theorem extraFixedPoint_denom : (-23:ℂ)*extraFixedPoint-16/3 ≠ 0 := by
  intro h
  have hh := congrArg Complex.im h
  simp [extraFixedPoint] at hh

theorem extraFixedPoint_fixed : (7*extraFixedPoint+5/3)/((-23)*extraFixedPoint-16/3) = extraFixedPoint := by
  apply (div_eq_iff extraFixedPoint_denom).mpr
  have hs : (Real.sqrt 11)^2=11 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [extraFixedPoint, Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem extra_elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F ((7*z+5/3)/((-23)*z-16/3))=((-23)*z-16/3)^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : (5/3:ℚ)≠m := by
    intro hm
    have hh : (3:ℚ)*m = 5 := by rw [← hm]; norm_num
    have hi : (3:ℤ)*m = 5 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 extraFixedPoint,
      F ((7*z+(5/3))/((-23)*z+(-16/3)))=((-23)*z+(-16/3))^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds extraFixedPoint_positive] with z hz
    simpa only [one_mul, sub_eq_add_neg, neg_div] using he z hz
  have hh := SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected extraFixedPoint_positive
    (a:=7) (b:=5/3) (c:= -23) (d:= -16/3) (t:=(5/3:ℚ))
    (by norm_num) (by simpa only [sub_eq_add_neg, neg_div] using extraFixedPoint_denom)
    (by simpa only [one_mul, sub_eq_add_neg, neg_div] using extraFixedPoint_fixed) hk
    (by norm_num) hnon heq
  exact fun z hz => hh hz

theorem extraEllipticReal_det : (GeneralLinearGroup.det extraEllipticReal:ℝ)=1 := by
  simp [extraEllipticReal]

theorem extraEllipticReal_denom (z : ℍ) : denom extraEllipticReal z = (-23)*(z:ℂ)-16/3 := by
  norm_num [denom, extraEllipticReal, extraElliptic, SpecialLinearGroup.toGL,
    SpecialLinearGroup.map_apply_coe]
  ring

theorem extraEllipticReal_point (z : ℍ) :
    ((extraEllipticReal • z : ℍ):ℂ)=(7*(z:ℂ)+5/3)/((-23)*(z:ℂ)-16/3) := by
  rw [coe_smul_of_det_pos (by rw [extraEllipticReal_det]; norm_num)]
  norm_num [num, denom, extraEllipticReal, extraElliptic, SpecialLinearGroup.toGL,
    SpecialLinearGroup.map_apply_coe]
  ring

theorem extra_invariant_zero {k : ℕ} (hk : 0<k) (H : ℍ → ℂ)
    (hhol : MDiff H) (he : H ∣[(k:ℤ)] extraEllipticReal=H) : H=0 := by
  let F : ℂ → ℂ := H ∘ ofComplex
  have hr (w : ℍ) : H w=F (w:ℂ) := by simp [F]
  have ha : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hhol).analyticOnNhd isOpen_upperHalfPlaneSet
  have htrans (z : ℂ) (hz : 0<z.im) :
      F ((7*z+5/3)/((-23)*z-16/3))=((-23)*z-16/3)^k*F z := by
    let w : ℍ := ⟨z,hz⟩
    have hh := congrFun he w
    rw [ModularForm.slash_apply] at hh
    have hs : σ extraEllipticReal=ContinuousAlgEquiv.refl ℝ ℂ := by
      simp only [σ, extraEllipticReal_det]; norm_num
    rw [hs, extraEllipticReal_det, extraEllipticReal_denom] at hh
    norm_num only [ContinuousAlgEquiv.refl_apply, abs_one, Complex.ofReal_one,
      one_zpow, mul_one, zpow_neg, zpow_natCast] at hh
    rw [hr, hr, extraEllipticReal_point] at hh
    change F ((7*z+5/3)/((-23)*z-16/3))*(((-23)*z-16/3)^k)⁻¹=F z at hh
    have hd : ((-23)*z-16/3:ℂ)≠0 := by
      simpa only [extraEllipticReal_denom] using denom_ne_zero extraEllipticReal w
    have hx := congrArg (fun v : ℂ => v*((-23)*z-16/3)^k) hh
    simp only [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hd), mul_one] at hx
    simpa only [mul_comm] using hx
  funext z
  rw [hr]
  exact extra_elliptic_defect_zero ha hk htrans z z.im_pos

theorem original_C (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 23 (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] C =
      SmallLevelOriginal.fourierFunction (2*m) f := by
  have hhol := SmallLevelOriginal.fourierFunction_holomorphic hf
  have hd := (hhol.slash ((2*m:ℕ):ℤ) (SpecialLinearGroup.mapGL ℝ C)).sub hhol
  exact sub_eq_zero.mp (extra_invariant_zero (by omega : 0<2*m) _ hd (original_extra_defect m hm hf))

#print axioms extra_elliptic_defect_zero
#print axioms original_C

end QuantitativeArithmeticSmallLevelTwentyThree
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyThreeGeneratorsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
@[expose] public section

namespace QuantitativeArithmeticSmallLevelTwentyThree
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

def letter : Fin 13 → SL(2,ℤ)
  | 0 => T
  | 1 => T⁻¹
  | 2 => lower 23
  | 3 => (lower 23)⁻¹
  | 4 => -1
  | 5 => oddMatrix 23 12 (by decide)
  | 6 => (oddMatrix 23 12 (by decide))⁻¹
  | 7 => A
  | 8 => A⁻¹
  | 9 => B
  | 10 => B⁻¹
  | 11 => C
  | 12 => C⁻¹

def word (w : List (Fin 13)) : SL(2,ℤ) := (w.map letter).prod

theorem word_mem (K : Subgroup SL(2,ℤ))
    (hT : T∈K) (hU : lower 23∈K) (hZ : -1∈K)
    (h2 : oddMatrix 23 12 (by decide)∈K) (h3 : A∈K) (h6 : B∈K) (hC : C∈K)
    (w : List (Fin 13)) : word w∈K := by
  have hl (i : Fin 13) : letter i∈K := by
    fin_cases i
    · exact hT
    · exact K.inv_mem hT
    · exact hU
    · exact K.inv_mem hU
    · exact hZ
    · exact h2
    · exact K.inv_mem h2
    · exact h3
    · exact K.inv_mem h3
    · exact h6
    · exact K.inv_mem h6
    · exact hC
    · exact K.inv_mem hC
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hl i)

def rowClass (c d : ZMod 23) : ℕ :=
  if c=0 then 23 else (d.val * ([0, 1, 12, 8, 6, 14, 4, 10, 3, 18, 7, 21, 2, 16, 5, 20, 13, 19, 9, 17, 15, 11, 22] : List ℕ).getD c.val 0) % 23

def repRow (c d : ZMod 23) : SL(2,ℤ) :=
  match rowClass c d with
  | 0 => ⟨!![0,-1;1,0], by decide⟩
  | 1 => ⟨!![0,-1;1,1], by decide⟩
  | 2 => ⟨!![0,-1;1,2], by decide⟩
  | 3 => ⟨!![0,-1;1,3], by decide⟩
  | 4 => ⟨!![0,-1;1,4], by decide⟩
  | 5 => ⟨!![0,-1;1,5], by decide⟩
  | 6 => ⟨!![-1,0;-4,-1], by decide⟩
  | 7 => ⟨!![-1,1;-3,2], by decide⟩
  | 8 => ⟨!![-1,0;-3,-1], by decide⟩
  | 9 => ⟨!![-1,2;2,-5], by decide⟩
  | 10 => ⟨!![-1,1;2,-3], by decide⟩
  | 11 => ⟨!![-1,0;2,-1], by decide⟩
  | 12 => ⟨!![-1,0;-2,-1], by decide⟩
  | 13 => ⟨!![-1,-1;-2,-3], by decide⟩
  | 14 => ⟨!![-1,1;3,-4], by decide⟩
  | 15 => ⟨!![-1,0;3,-1], by decide⟩
  | 16 => ⟨!![1,1;-3,-2], by decide⟩
  | 17 => ⟨!![-1,0;4,-1], by decide⟩
  | 18 => ⟨!![0,-1;1,-5], by decide⟩
  | 19 => ⟨!![0,-1;1,-4], by decide⟩
  | 20 => ⟨!![0,-1;1,-3], by decide⟩
  | 21 => ⟨!![0,-1;1,-2], by decide⟩
  | 22 => ⟨!![0,-1;1,-1], by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 23) : List (Fin 13) :=
  match rowClass c d with
  | 0 => [4]
  | 1 => [1]
  | 5 => [9, 2, 6, 11]
  | 6 => [4]
  | 7 => [4]
  | 8 => [4]
  | 9 => [12, 5, 3, 10, 4]
  | 11 => [4]
  | 12 => [4]
  | 14 => [4, 9]
  | 15 => [4]
  | 16 => [4]
  | 17 => [4]
  | 18 => [10]
  | 22 => [0, 4]
  | _ => []

def edgeTRow (c d : ZMod 23) : List (Fin 13) :=
  match rowClass c d with
  | 23 => [0]
  | 5 => [4, 7]
  | 6 => [4, 10, 12]
  | 8 => [11, 9, 8, 6, 0]
  | 11 => [1, 4]
  | 13 => [11]
  | 15 => [4]
  | 16 => [12, 5, 3, 10]
  | 17 => [9]
  | _ => []

def rep (g : SL(2,ZMod 23)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)

theorem row_nonzero (g : SL(2,ZMod 23)) : g.1 1 0≠0 ∨ g.1 1 1≠0 := by
  by_contra h
  push Not at h
  have hd := g.det_coe
  rw [det_fin_two, h.1, h.2] at hd
  norm_num at hd
  exact (by decide : (0:ZMod 23)≠1) hd

theorem edgeSRow_checked : ∀ c d : ZMod 23, c≠0 ∨ d≠0 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by decide

theorem edgeTRow_checked : ∀ c d : ZMod 23, c≠0 ∨ d≠0 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by decide

theorem edgeS_checked (g : SL(2,ZMod 23)) :
    rep g*S*(rep (g*reduction 23 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 23 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 23 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 23)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_nonzero g)

theorem edgeT_checked (g : SL(2,ZMod 23)) :
    rep g*T*(rep (g*reduction 23 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 23 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 23 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 23)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_nonzero g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 23)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 23, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ))
    (hT : T∈K) (hU : lower 23∈K) (hZ : -1∈K)
    (h2 : oddMatrix 23 12 (by decide)∈K) (h3 : A∈K) (h6 : B∈K) (hC : C∈K)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 23) : γ∈K := by
  apply transversal_mem (reduction 23) rep K
  · intro g
    rw [edgeS_checked]
    exact word_mem K hT hU hZ h2 h3 h6 hC _
  · intro g
    rw [edgeT_checked]
    exact word_mem K hT hU hZ h2 h3 h6 hC _
  · exact rep_one
  · apply rep_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edgeS_checked
#print axioms edgeT_checked
#print axioms gamma0_mem

end QuantitativeArithmeticSmallLevelTwentyThree
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyThreeModularV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelTwentyThree

open Matrix ModularGroup SmallLevelGenerators SmallLevelOriginal
open scoped MatrixGroups ModularForm

theorem gamma_zero_twenty_three (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 23 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 23) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 23∈K := original_lower (by decide) hf
  have hz : -1∈K := SmallLevelThirtySix.slash_neg_one_even _ m
  change γ∈K
  exact gamma0_mem K ht hu hz
    (original_odd (by decide) (by decide : 2*12=23+1) (by decide) hf)
    (original_A (by omega) hf) (original_B (by omega) hf) (original_C m hm hf) γ hγ

/-- The literal Euler input gives a genuine Mathlib modular form at level
23 in every positive even weight, with no extra twist or eigenvalue premise. -/
theorem level_twenty_three {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 23 k f) : IsModular 23 k f := by
  obtain ⟨m,hm⟩ := heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf ⊢
  exact modular_of_transformations (by decide) hf (gamma_zero_twenty_three m (by omega) hf)

#print axioms gamma_zero_twenty_three
#print axioms level_twenty_three

end QuantitativeArithmeticSmallLevelTwentyThree
end
end
