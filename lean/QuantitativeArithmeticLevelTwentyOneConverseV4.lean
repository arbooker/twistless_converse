module

public import SmallLevelAnalyticRigidityTheoryV4
public import SmallLevelTwentyOneTheoryV4
public import SmallLevelTwentyOneConjugatesV1
public import SmallLevelTwentyOneKnownWordsV1
public import SmallLevelTwentyOneZeroKernelV1

/-! Consolidated converse argument. Large exact certificates remain
in their own modules; declarations and proof bodies are preserved. -/

/-! ## TwentyOneZeroRigidity -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneZeroRigidity
open Matrix UpperHalfPlane SmallLevelNormalized Complex Filter Set
open scoped MatrixGroups ModularForm Manifold Topology

def elliptic : SL(2,ℚ) := ⟨!![540,(-571);511,(-(1621/3))], by norm_num [det_fin_two]⟩
def ellipticReal : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ elliptic

def fixedPoint : ℂ := ⟨3241/3066, Real.sqrt 35/3066⟩

theorem fixedPoint_positive : 0 < fixedPoint.im := by
  change 0 < Real.sqrt 35/3066
  positivity

theorem fixedPoint_denom : (511:ℂ)*fixedPoint+(-(1621/3)) ≠ 0 := by
  intro h
  have hh := congrArg Complex.im h
  simp [fixedPoint] at hh

theorem fixedPoint_fixed : ((540)*fixedPoint+(-571))/((511)*fixedPoint+(-(1621/3))) = fixedPoint := by
  apply (div_eq_iff fixedPoint_denom).mpr
  have hs : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [fixedPoint, Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F (((540)*z+(-571))/((511)*z+(-(1621/3))))=((511)*z+(-(1621/3)))^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : ((-1/3):ℚ)≠m := by
    intro hm
    have hh : (3:ℚ)*m = -1 := by rw [← hm]; norm_num
    have hi : (3:ℤ)*m = -1 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 fixedPoint,
      F (((540)*z+((-571)))/((511)*z+((-(1621/3)))))=((511)*z+((-(1621/3))))^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds fixedPoint_positive] with z hz
    exact he z hz
  have hh := SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected fixedPoint_positive
    (a:= 540) (b:=(-571)) (c:= 511) (d:=(-(1621/3))) (t:=((-1/3):ℚ))
    (by norm_num) fixedPoint_denom
    fixedPoint_fixed hk
    (by norm_num) hnon heq
  exact fun z hz => hh hz

theorem ellipticReal_det : (GeneralLinearGroup.det ellipticReal:ℝ)=1 := by
  simp [ellipticReal]

theorem ellipticReal_denom (z : ℍ) : denom ellipticReal z = (511)*(z:ℂ)+(-(1621/3)) := by
  norm_num [denom, ellipticReal, elliptic, SpecialLinearGroup.toGL,
    SpecialLinearGroup.map_apply_coe]

theorem ellipticReal_point (z : ℍ) :
    ((ellipticReal • z : ℍ):ℂ)=((540)*(z:ℂ)+(-571))/((511)*(z:ℂ)+(-(1621/3))) := by
  rw [coe_smul_of_det_pos (by rw [ellipticReal_det]; norm_num)]
  norm_num [num, denom, ellipticReal, elliptic, SpecialLinearGroup.toGL,
    SpecialLinearGroup.map_apply_coe]

theorem invariant_zero {k : ℕ} (hk : 0<k) (H : ℍ → ℂ)
    (hhol : MDiff H) (he : H ∣[(k:ℤ)] ellipticReal=H) : H=0 := by
  let F : ℂ → ℂ := H ∘ ofComplex
  have hr (w : ℍ) : H w=F (w:ℂ) := by simp [F]
  have ha : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hhol).analyticOnNhd isOpen_upperHalfPlaneSet
  have htrans (z : ℂ) (hz : 0<z.im) :
      F (((540)*z+(-571))/((511)*z+(-(1621/3))))=((511)*z+(-(1621/3)))^k*F z := by
    let w : ℍ := ⟨z,hz⟩
    have hh := congrFun he w
    rw [ModularForm.slash_apply] at hh
    have hs : σ ellipticReal=ContinuousAlgEquiv.refl ℝ ℂ := by
      simp only [σ, ellipticReal_det]; norm_num
    rw [hs, ellipticReal_det, ellipticReal_denom] at hh
    norm_num only [ContinuousAlgEquiv.refl_apply, abs_one, Complex.ofReal_one,
      one_zpow, mul_one, zpow_neg, zpow_natCast] at hh
    rw [hr, hr, ellipticReal_point] at hh
    change F (((540)*z+(-571))/((511)*z+(-(1621/3))))*(((511)*z+(-(1621/3)))^k)⁻¹=F z at hh
    have hd : ((511)*z+(-(1621/3)):ℂ)≠0 := by
      simpa only [ellipticReal_denom] using denom_ne_zero ellipticReal w
    have hx := congrArg (fun v : ℂ => v*((511)*z+(-(1621/3)))^k) hh
    simp only [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hd), mul_one] at hx
    simpa only [mul_comm] using hx
  funext z
  rw [hr]
  exact elliptic_defect_zero ha hk htrans z z.im_pos


#print axioms invariant_zero
end SmallLevelTwentyOneZeroRigidity
end
end

/-! ## TwentyOneZeroFinalMatrices -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneZero
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open SmallLevelTwentyOneChiFiveGroup SmallLevelTwentyOneThree
open scoped MatrixGroups ModularForm

def L : SL(2,ℤ) := ⟨!![22,1;21,1],by decide⟩
def K : SL(2,ℤ) := ⟨!![29,8;-98,-27],by decide⟩
theorem L_word : L=ModularGroup.T*lower 21 := by decide

theorem J_relation : P*SpecialLinearGroup.mapGL ℝ L=SpecialLinearGroup.mapGL ℝ J*P := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P,J,L,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

theorem K_relation : P⁻¹*translation (2/3)*P=SpecialLinearGroup.mapGL ℝ K := by
  rw [P_inv]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P,K,matrixThree,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

theorem elliptic_factor : SpecialLinearGroup.mapGL ℝ L*SpecialLinearGroup.mapGL ℝ K*
    translation (-4/3)=SmallLevelTwentyOneZeroRigidity.ellipticReal := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [L,K,translation,matrix,SmallLevelTwentyOneZeroRigidity.ellipticReal,
      SmallLevelTwentyOneZeroRigidity.elliptic,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

theorem P_square : P*P=SpecialLinearGroup.mapGL ℝ A⁻¹ := by
  rw [show A⁻¹=(⟨!![-4,-1;21,5],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

#print axioms J_relation
#print axioms K_relation
#print axioms elliptic_factor
#print axioms P_square
end SmallLevelTwentyOneZero
end
end

/-! ## TwentyOneZeroDefect -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneZero
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open SmallLevelTwentyOneThree
open scoped MatrixGroups ModularForm Manifold

theorem original_P_zero {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (hf2 : f 2=0) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      delta f • SmallLevelOriginal.fourierFunction (2*m) f := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  let h := defect (2*m) f
  let g := inverseDefect (2*m) f
  have hd : delta f*delta f=1 := by
    rcases FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3 with h|h <;> simp [delta,h]
  have hpi : h ∣[k] P⁻¹=(-delta f) • g := by
    change ((F ∣[k] P)-delta f • F) ∣[k] P⁻¹=(-delta f) • ((F ∣[k] P⁻¹)-delta f • F)
    rw [SmallLevelEleven.sub_slash,det_one_smul _ (det_one_inv _ P_det),
      ← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one]
    funext z
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    linear_combination -F z*hd
  have hL : F ∣[k] L=F := by
    rw [L_word]
    exact (slashStabilizer k F).mul_mem (original_T (2*m) f) (original_lower (by decide : 0<21) hf)
  have hJ : F ∣[k] J=F := original_J hm hf hf2
  have hdL : h ∣[k] SpecialLinearGroup.mapGL ℝ L=h := by
    change ((F ∣[k] P)-delta f • F) ∣[k] SpecialLinearGroup.mapGL ℝ L=(F ∣[k] P)-delta f • F
    have hLg : F ∣[k] SpecialLinearGroup.mapGL ℝ L=F := hL
    rw [SmallLevelEleven.sub_slash,det_one_smul _ (by simp),hLg]
    have hh : (F ∣[k] P) ∣[k] L=F ∣[k] P := by
      change (F ∣[k] P) ∣[k] SpecialLinearGroup.mapGL ℝ L=_
      rw [← SlashAction.slash_mul,J_relation,SlashAction.slash_mul]
      change (F ∣[k] J) ∣[k] P=F ∣[k] P
      rw [hJ]
    change (F ∣[k] P) ∣[k] L-delta f • F=(F ∣[k] P)-delta f • F
    rw [hh]
  have hg : g ∣[k] translation (2/3)=g := original_inverse_period hm hf hf2
  have hdK : h ∣[k] SpecialLinearGroup.mapGL ℝ K=h := by
    rw [← K_relation,SlashAction.slash_mul,SlashAction.slash_mul,hpi,
      det_one_smul _ (translation_det _),hg,← hpi,
      ← SlashAction.slash_mul,inv_mul_cancel,SlashAction.slash_one]
  have h43 : h ∣[k] translation (4/3)=h := by
    convert translation_period_nat h k (2/3) (original_period_two_thirds hm hf) 2 using 1; norm_num
  have hback : h ∣[k] translation (-4/3)=h := by
    have hh := congrArg (fun G : ℍ → ℂ => G ∣[k] translation (-4/3)) h43
    simp only [← SlashAction.slash_mul,translation_mul] at hh
    norm_num only [show (4/3:ℝ)+ -4/3=0 by ring,translation_zero,SlashAction.slash_one] at hh
    simpa only [neg_div] using hh.symm
  have he : h ∣[k] SmallLevelTwentyOneZeroRigidity.ellipticReal=h := by
    rw [← elliptic_factor,SlashAction.slash_mul,SlashAction.slash_mul,hdL,hdK,hback]
  have hhol : MDiff F := SmallLevelOriginal.fourierFunction_holomorphic hf
  have hsm : MDiff (delta f • F) := hhol.const_smul (delta f)
  have hz : h=0 := SmallLevelTwentyOneZeroRigidity.invariant_zero (by omega : 0<2*m) h
    ((hhol.slash k P).sub hsm) he
  exact sub_eq_zero.mp hz

#print axioms original_P_zero
end SmallLevelTwentyOneZero
end
end

/-! ## TwentyOneNonzeroModular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyOneGeneration
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open SmallLevelTwentyOneChiFiveGroup SmallLevelTwentyOneThree SmallLevelOriginal
open scoped MatrixGroups ModularForm

theorem original_base {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (hA : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A=fourierFunction (2*m) f)
    (hB : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] B=fourierFunction (2*m) f)
    (i : Fin 7) : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] generator (i.castLE (by decide))=
      fourierFunction (2*m) f := by
  obtain ⟨hC,hD⟩ := original_C_D hm hf
  fin_cases i
  · exact original_T (2*m) f
  · exact original_lower (by decide : 0<21) hf
  · exact original_E hf
  · exact hC
  · exact hD
  · exact hA
  · exact hB

/-- The explicit64 transition certificates prove the full Gamma0 law from
A,B and the normalized P eigenrelation. -/
theorem modular_of_A_B_P {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (hA : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A=fourierFunction (2*m) f)
    (hB : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] B=fourierFunction (2*m) f)
    (hP : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=delta f • fourierFunction (2*m) f) :
    IsModular 21 (2*m) f := by
  obtain ⟨χ,_hχ,hW⟩ := original_fricke_sign (by decide : 0<21) m hf
  apply modular_of_transformations (by decide : 0<21) hf
  intro γ hγ
  apply gamma0_mem (slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f))
  · exact all_generators _ _ _ _ hP hW (original_base hm hf hA hB)
  · exact SmallLevelThirtySix.slash_neg_one_even _ m
  · exact hγ

theorem original_nonzero_modular {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (hf2 : f 2≠0) :
    IsModular 21 (2*m) f := by
  obtain ⟨hA,hB⟩ := original_A_B hm hf hf2
  exact modular_of_A_B_P hm hf hA hB (original_P_nonzero hm hf hf2)

#print axioms modular_of_A_B_P
#print axioms original_nonzero_modular
end SmallLevelTwentyOneGeneration
end
end

/-! ## TwentyOneModular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneZero
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open SmallLevelTwentyOneChiFiveGroup SmallLevelTwentyOneChiFive SmallLevelTwentyOneThree
open scoped MatrixGroups ModularForm

theorem original_A_of_P {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (hP : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      delta f • SmallLevelOriginal.fourierFunction (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  have hd : delta f*delta f=1 := by
    rcases FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3 with h|h <;> simp [delta,h]
  have hp : F ∣[k] P=delta f • F := hP
  have hai : F ∣[k] A⁻¹=F := by
    change F ∣[k] SpecialLinearGroup.mapGL ℝ A⁻¹=F
    rw [← P_square,SlashAction.slash_mul,hp,det_one_smul _ P_det,hp,smul_smul,hd,one_smul]
  have ha := (slashStabilizer k F).inv_mem hai
  change F ∣[k] (A⁻¹)⁻¹=F at ha
  change F ∣[k] A=F
  simpa only [inv_inv] using ha

theorem original_B_of_A {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (hA : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A=
      SmallLevelOriginal.fourierFunction (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] B=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨ε,_hε,hlaw,hquad⟩ := original_quadratic_fricke hm hf
  have hp := separated_first_pair ε hlaw hquad
  simp only [hA,sub_self,SlashAction.zero_slash,zero_add] at hp
  have hh := congrArg (fun H : ℍ → ℂ => H ∣[((2*m:ℕ):ℤ)] (translation (1/5))⁻¹) hp
  simp only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one,SlashAction.zero_slash] at hh
  exact sub_eq_zero.mp hh

theorem original_zero_modular {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (hf2 : f 2=0) :
    SmallLevelOriginal.IsModular 21 (2*m) f := by
  have hP := original_P_zero hm hf hf2
  have hA := original_A_of_P hf hP
  have hB := original_B_of_A hm hf hA
  exact SmallLevelTwentyOneGeneration.modular_of_A_B_P hm hf hA hB hP
end SmallLevelTwentyOneZero

namespace SmallLevelOriginal
/-- Level21 in the small-level theorem, including zero and nonzero Hecke2
values, all allowed signs, all positive even weights and every cusp. -/
theorem level_twenty_one {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 k f) : IsModular 21 k f := by
  obtain ⟨m,hm⟩ := heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf ⊢
  by_cases h2 : f 2=0
  · exact SmallLevelTwentyOneZero.original_zero_modular (by omega) hf h2
  · exact SmallLevelTwentyOneGeneration.original_nonzero_modular (by omega) hf h2

#print axioms level_twenty_one
end SmallLevelOriginal
end
end

/-! ## TwentyOnePoleLocus -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex

/-- An actual pole must reach the explicitly certified exponential
polynomial locus after a nonnegative integer shift. This is a necessary
pole condition, not a proof that the locus contains no poles. -/
theorem original_poles_on_locus {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∃ B : ℝ, ∃ G : ℂ → Fin 42 → ℂ,
      (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      (∀ z, B<z.re → G z=gridVector (2*m) f z) ∧
      ∀ x, (∃ i, meromorphicOrderAt (fun z => G z i) x<0) →
        ∃ n : ℕ, (∃ i, meromorphicOrderAt (fun z => G z i) (x+n)<0) ∧
          (∀ j : ℕ, 0<j → ∀ i, 0≤meromorphicOrderAt (fun z => G z i) (x+n+j)) ∧
          originalDeterminantFactor m f ε (x+n)=0 := by
  obtain ⟨ε,hε,B,G,hG,heG,hpole⟩ := original_pole_constraint hm hf
  refine ⟨ε,hε,B,G,hG,heG,?_⟩
  intro x hx
  obtain ⟨n,hn,hshift,_,hdet⟩ := hpole x hx
  exact ⟨n,hn,hshift,original_singular_factor hf hε hdet⟩

#print axioms original_poles_on_locus
end SmallLevelTwentyOne
end
end

/-! ## TwentyOnePoleNormalization -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Matrix

/-- Any pole gives a rightmost pole on the explicit determinant locus and
a unique normalized leading vector. All data and sign restrictions come
from the original Euler input. Pole exclusion remains a separate step. -/
theorem original_pole_normalization {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∃ B : ℝ, ∃ G : ℂ → Fin 42 → ℂ,
      (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      (∀ z, B<z.re → G z=gridVector (2*m) f z) ∧
      ∀ x, (∃ i, meromorphicOrderAt (fun z => G z i) x<0) →
        ∃ n : ℕ, (∃ i, meromorphicOrderAt (fun z => G z i) (x+n)<0) ∧
          (∀ j : ℕ, 0<j → ∀ i, 0≤meromorphicOrderAt (fun z => G z i) (x+n+j)) ∧
          originalDeterminantFactor m f ε (x+n)=0 ∧
          ∃! w : Fin 42 → ℂ, leadingMatrix m f ε (x+n) *ᵥ w=0 ∧ w 28=1 := by
  obtain ⟨ε,hε,B,G,hG,heG,hpole⟩ := original_pole_constraint hm hf
  refine ⟨ε,hε,B,G,hG,heG,?_⟩
  intro x hx
  obtain ⟨n,hn,hshift,hker,hdet⟩ := hpole x hx
  exact ⟨n,hn,hshift,original_singular_factor hf hε hdet,
    original_normalized_kernel_unique hf hε hker⟩

#print axioms original_pole_normalization
end SmallLevelTwentyOne
end
end
