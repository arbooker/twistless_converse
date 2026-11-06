module

public import SmallLevelGoodHeckeTwoV1
public import SmallLevelTwentyOneChiFiveDefectV1
public import SmallLevelTwentyOneChiFiveTheoryV4

/-! Consolidated chapter: SmallLevelTwentyOneChiFiveGroup. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyOneChiFiveTransformationsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFiveGroup
open Matrix UpperHalfPlane SmallLevelGenerators
open SmallLevelTwentyOneChiFive
open scoped MatrixGroups ModularForm Manifold

theorem original_E {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] E=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (SmallLevelOriginal.fourierFunction (2*m) f)
  rw [E_known]
  exact K.inv_mem (original_odd (by decide) (by decide : 2*11=21+1) (by decide) hf)

/-- The actual quadratic twist supplies both new determinant-one
transformations in every positive even weight and for every Hecke2 scalar. -/
theorem original_C_D {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] C=
      SmallLevelOriginal.fourierFunction (2*m) f) ∧
    (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] D=
      SmallLevelOriginal.fourierFunction (2*m) f) := by
  obtain ⟨ε,_hε,hlaw,hquad⟩ := original_quadratic_fricke hm hf
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  have hE : F ∣[k] E=F := original_E hf
  have hT : F ∣[k] ModularGroup.T=F := original_T (2*m) f
  have hU : F ∣[k] lower 21=F := original_lower (by decide : 0<21) hf
  have hp := separated_second_pair ε hlaw hquad
  have hell := defect_elliptic F k hE hT hU hp
  have hhol := SmallLevelOriginal.fourierFunction_holomorphic hf
  have hC : F ∣[k] C=F := sub_eq_zero.mp
    (SmallLevelTwentyOneChiFiveRigidity.invariant_zero (by omega : 0<2*m) _
      ((hhol.slash k (SpecialLinearGroup.mapGL ℝ C)).sub hhol) hell)
  refine ⟨hC,?_⟩
  let K := slashStabilizer k F
  have hi : F ∣[k] C⁻¹=F := K.inv_mem hC
  change F ∣[k] D=F
  rw [D_factor]
  simp only [SlashAction.slash_mul,hU,hE,hi,hT]

#print axioms original_E
#print axioms original_C_D
end SmallLevelTwentyOneChiFiveGroup
end
end

/-! ## SmallLevelTwentyOneChiFiveHeckeAV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFiveGroup
open Matrix UpperHalfPlane SmallLevelGenerators
open QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open scoped MatrixGroups ModularForm

def heckeLeft : SL(2,ℤ) := ⟨!![10,1;-21,-2],by decide⟩
def heckeRight : SL(2,ℤ) := ⟨!![-8,-3;-21,-8],by decide⟩

theorem heckeLeft_word : heckeLeft=(-1)*ModularGroup.T⁻¹*E⁻¹ := by decide
theorem heckeRight_word : heckeRight=E⁻¹*(lower 21)⁻¹*D := by decide

theorem A_branch_infinity : heckeInfinity*SpecialLinearGroup.mapGL ℝ A=
    SpecialLinearGroup.mapGL ℝ heckeLeft*heckeFinite 0 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeInfinity,heckeFinite,A,heckeLeft,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Fin.sum_univ_two]

theorem A_branch_zero : heckeFinite 0*SpecialLinearGroup.mapGL ℝ A=
    SpecialLinearGroup.mapGL ℝ C*heckeFinite 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeFinite,A,C,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Fin.sum_univ_two]

theorem A_branch_one : heckeFinite 1*SpecialLinearGroup.mapGL ℝ A=
    SpecialLinearGroup.mapGL ℝ heckeRight*heckeInfinity := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeFinite,heckeInfinity,A,heckeRight,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Fin.sum_univ_two]

/-- The nonzero Hecke2 eigenvalue and the proved C,D transformations force
A invariance. This is the only division by that eigenvalue in this step. -/
theorem original_A {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (hf2 : f 2≠0) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨hC,hD⟩ := original_C_D hm hf
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  let K := slashStabilizer k F
  have hE : F ∣[k] E=F := original_E hf
  have hT : F ∣[k] ModularGroup.T=F := original_T (2*m) f
  have hU : F ∣[k] lower 21=F := original_lower (by decide : 0<21) hf
  have hleft : F ∣[k] heckeLeft=F := by
    rw [heckeLeft_word]
    exact K.mul_mem (K.mul_mem (SmallLevelThirtySix.slash_neg_one_even F m)
      (K.inv_mem hT)) (K.inv_mem hE)
  have hright : F ∣[k] heckeRight=F := by
    rw [heckeRight_word]
    exact K.mul_mem (K.mul_mem (K.inv_mem hE) (K.inv_mem hU)) hD
  have he := SmallLevelGoodHeckeTwo.original_hecke_two (by decide : ¬2∣21) hf.toEulerData m
  have hh := congrArg (fun G : ℍ → ℂ => G ∣[k] A) he
  simp only [heckeTwo,SlashAction.add_slash,ModularForm.SL_smul_slash] at hh
  have hi : (F ∣[k] heckeInfinity) ∣[k] A=F ∣[k] heckeFinite 0 := by
    change (F ∣[k] heckeInfinity) ∣[k] SpecialLinearGroup.mapGL ℝ A=_
    rw [← SlashAction.slash_mul,A_branch_infinity,SlashAction.slash_mul]
    change (F ∣[k] heckeLeft) ∣[k] heckeFinite 0=_
    rw [hleft]
  have h0 : (F ∣[k] heckeFinite 0) ∣[k] A=F ∣[k] heckeFinite 1 := by
    change (F ∣[k] heckeFinite 0) ∣[k] SpecialLinearGroup.mapGL ℝ A=_
    rw [← SlashAction.slash_mul,A_branch_zero,SlashAction.slash_mul]
    change (F ∣[k] C) ∣[k] heckeFinite 1=_
    rw [hC]
  have h1 : (F ∣[k] heckeFinite 1) ∣[k] A=F ∣[k] heckeInfinity := by
    change (F ∣[k] heckeFinite 1) ∣[k] SpecialLinearGroup.mapGL ℝ A=_
    rw [← SlashAction.slash_mul,A_branch_one,SlashAction.slash_mul]
    change (F ∣[k] heckeRight) ∣[k] heckeInfinity=_
    rw [hright]
  let lam := FinitenessAllLevelHeckePower.scale 2 m*f 2/2
  change (F ∣[k] heckeInfinity) ∣[k] A+(F ∣[k] heckeFinite 0) ∣[k] A+
    (F ∣[k] heckeFinite 1) ∣[k] A=lam • (F ∣[k] A) at hh
  rw [hi,h0,h1] at hh
  have heq : lam • (F ∣[k] A)=lam • F := by
    calc
      _=(F ∣[k] heckeFinite 0)+(F ∣[k] heckeFinite 1)+(F ∣[k] heckeInfinity) := hh.symm
      _=heckeTwo k F := by dsimp [heckeTwo]; abel
      _=lam • F := he
  have hlam : lam≠0 := by
    apply div_ne_zero (mul_ne_zero _ hf2) (by norm_num)
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne')
  funext z
  have hz := congrFun heq z
  simp only [Pi.smul_apply,smul_eq_mul] at hz
  exact mul_left_cancel₀ hlam hz

#print axioms A_branch_infinity
#print axioms original_A
end SmallLevelTwentyOneChiFiveGroup
end
end

/-! ## SmallLevelTwentyOneChiFiveABV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFiveGroup
open Matrix UpperHalfPlane SmallLevelNormalized
open SmallLevelTwentyOneChiFive
open scoped MatrixGroups ModularForm

theorem A_fifth_branch : fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ A*translation (-1/5)=
    translation (1/5)*fricke 525 (by decide) := by
  have ht : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,A,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

theorem B_fifth_branch : fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ B*translation (1/5)=
    translation (-1/5)*fricke 525 (by decide) := by
  have ht : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,B,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

theorem separated_first_pair {k : ℕ} {f : ℕ → ℂ} (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 k f ε)
    (hquad : ∀ z : ℂ, 0<z.im → quadraticFourier k f z=
      (ε*Complex.I^k)/(((Real.sqrt 525:ℂ)*z)^k)*quadraticFourier k f (-1/((525:ℂ)*z))) :
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A)-SmallLevelOriginal.fourierFunction k f)
        ∣[(k:ℤ)] translation (-1/5)+
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] B)-SmallLevelOriginal.fourierFunction k f)
        ∣[(k:ℤ)] translation (1/5)=0 := by
  have h := first_pair_slash ε hlaw hquad
  have hp : (fricke 21 (by decide))⁻¹*translation (1/5)*fricke 525 (by decide)=
      SpecialLinearGroup.mapGL ℝ A*translation (-1/5) := by
    rw [mul_assoc,← A_fifth_branch]
    group
  have hn : (fricke 21 (by decide))⁻¹*translation (-1/5)*fricke 525 (by decide)=
      SpecialLinearGroup.mapGL ℝ B*translation (1/5) := by
    rw [mul_assoc,← B_fifth_branch]
    group
  rw [hp,hn,SlashAction.slash_mul,SlashAction.slash_mul] at h
  simp only [SmallLevelEleven.sub_slash]
  linear_combination h

/-- Both first-pair transformations from original input in the nonzero
Hecke2 branch. The zero branch remains a separate group argument. -/
theorem original_A_B {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (hf2 : f 2≠0) :
    (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A=
      SmallLevelOriginal.fourierFunction (2*m) f) ∧
    (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] B=
      SmallLevelOriginal.fourierFunction (2*m) f) := by
  have hA := original_A hm hf hf2
  obtain ⟨ε,_hε,hlaw,hquad⟩ := original_quadratic_fricke hm hf
  have hp := separated_first_pair ε hlaw hquad
  simp only [hA,sub_self,SlashAction.zero_slash,zero_add] at hp
  have hh := congrArg (fun H : ℍ → ℂ => H ∣[((2*m:ℕ):ℤ)] (translation (1/5))⁻¹) hp
  simp only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one,SlashAction.zero_slash] at hh
  exact ⟨hA,sub_eq_zero.mp hh⟩

#print axioms separated_first_pair
#print axioms original_A_B
end SmallLevelTwentyOneChiFiveGroup
end
end
