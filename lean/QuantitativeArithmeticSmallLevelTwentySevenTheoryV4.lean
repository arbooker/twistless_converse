module

public import FinitenessAllLevelHeckePowerV1
public import FinitenessNormalizedTwistProductV1
public import Mathlib.Tactic
public import QuantitativeArithmeticCubicTraceV1
public import QuantitativeArithmeticQuadraticMatricesTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenAffineTheoryV4
public import SmallLevelNormalizedFrickeV1
public import SmallLevelNormalizedMatricesV1
public import SmallLevelOddFrickeV1
public import SmallLevelOriginalTaylorRowsV1
public import SmallLevelTaylorTheoryV4
public import SmallLevelThirtySixFourierV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySeven. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenFourierV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySeven
open Complex UpperHalfPlane FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction QuantitativeArithmeticRetainedReconstruction
open scoped MatrixGroups ModularForm

def scaledFourier (k : ℕ) (f : ℕ → ℂ) (z : ℂ) : ℂ :=
  fourier (fullCoefficients f k) (z/3)

def scaledFunction (k : ℕ) (f : ℕ → ℂ) (z : ℍ) : ℂ := scaledFourier k f z

theorem scaled_period (k : ℕ) (f : ℕ → ℂ) (z : ℂ) :
    scaledFourier k f (z+3)=scaledFourier k f z := by
  unfold scaledFourier
  rw [show (z+3)/3=z/3+(1:ℂ) by ring,periodic]

/-- The ramified Euler factor gives the cubic trace, at every weight. -/
theorem scaled_trace {f : ℕ → ℂ} (hf : EulerData 27 f) (k : ℕ)
    {z : ℂ} (hz : 0<z.im) :
    scaledFourier k f z+scaledFourier k f (z+1)+scaledFourier k f (z+2)=0 := by
  have hh := SmallLevelThirtySix.square_prime_average_zero hf (p:=3)
    (by decide) (by decide) k (z:=z/3)
    (by simpa using div_pos hz (by norm_num : (0:ℝ)<3))
  norm_num [completeTwist,Finset.sum_range_succ] at hh
  dsimp only [scaledFourier]
  rw [show (z+1)/3=z/3+(1:ℂ)/3 by ring,
    show (z+2)/3=z/3+(2:ℂ)/3 by ring]
  exact hh

/-- The good-prime-two equation in the same rescaled coordinates. -/
theorem scaled_hecke_two {f : ℕ → ℂ} (hf : EulerData 27 f) (m : ℕ)
    {z : ℂ} (hz : 0<z.im) :
    (2:ℂ)^(2*m)*scaledFourier (2*m) f (2*z)+
      scaledFourier (2*m) f (z/2)+scaledFourier (2*m) f ((z+3)/2)=
      FinitenessAllLevelHeckePower.scale 2 m*f 2*scaledFourier (2*m) f z := by
  have hh := FinitenessAllLevelHeckePower.original_relation
    (N:=27) (p:=2) (by decide) (by decide) m hf
    (z:=z/3) (by simpa using div_pos hz (by norm_num : (0:ℝ)<3))
  have hs : FinitenessAllLevelHeckePower.scale 2 m≠0 := by
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have he := congrArg (fun v : ℂ => FinitenessAllLevelHeckePower.scale 2 m*v) hh
  simp only [mul_add,← mul_assoc,mul_inv_cancel₀ hs,one_mul] at he
  norm_num [completeTwist,Finset.sum_range_succ] at he
  dsimp only [scaledFourier]
  ring_nf at he ⊢
  linear_combination -he

theorem scaled_fricke {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 27 k f) :
    ∃ χ : ℂ, ‖χ‖=1 ∧ ∀ z : ℂ, 0<z.im → scaledFourier k f z=
      χ/(((Real.sqrt 3:ℂ)*z)^k)*scaledFourier k f (-1/((3:ℂ)*z)) := by
  obtain ⟨χ,hχ,hfr⟩ := FinitenessOriginalFricke.solution_fricke (by decide : 0<27) hf
  refine ⟨χ,hχ,fun z hz => ?_⟩
  have he := hfr (z/3) (by simpa using div_pos hz (by norm_num : (0:ℝ)<3))
  have hsqrt : Real.sqrt (27:ℝ)=3*Real.sqrt 3 := by
    rw [show (27:ℝ)=9*3 by norm_num,Real.sqrt_mul (by norm_num)]
    norm_num
  norm_num only [Nat.cast_ofNat] at he
  rw [hsqrt] at he
  norm_num only [Nat.cast_ofNat,ofReal_mul,ofReal_ofNat] at he
  rw [show (3*(Real.sqrt 3:ℂ))*(z/3)=(Real.sqrt 3:ℂ)*z by ring,
    show -1/((27:ℂ)*(z/3))=(-1/((3:ℂ)*z))/3 by ring] at he
  exact he

#print axioms scaled_trace
#print axioms scaled_hecke_two
#print axioms scaled_fricke
end QuantitativeArithmeticSmallLevelTwentySeven
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenOriginalBaseV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySeven
open Complex Matrix UpperHalfPlane SmallLevelNormalized FinitenessOriginalInput
open QuantitativeArithmeticQuadraticMatrices QuantitativeArithmeticSmallLevelTwentySevenAffine
open scoped MatrixGroups ModularForm

theorem base_translation (i : Fin 3) : baseGL (i.castLE (by decide))=translation i.val := by
  fin_cases i <;>
    apply Units.ext <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [baseGL,baseMatrix,liftMatrix,translation,matrix,
      GeneralLinearGroup.mkOfDetNeZero,Matrix.det_fin_two]

theorem scaled_base_translation (k : ℕ) (f : ℕ → ℂ) (i : Fin 3) (z : ℍ) :
    (scaledFunction k f ∣[(k:ℤ)] baseGL (i.castLE (by decide))) z=
      scaledFourier k f ((z:ℂ)+i.val) := by
  rw [base_translation,translation_slash]
  simp only [scaledFunction,translation_point,Complex.ofReal_natCast]

theorem original_upper_trace {f : ℕ → ℂ} (hf : EulerData 27 f) (m : ℕ) (a : ℂ) :
    baseSum m a (scaledFunction (2*m) f) 0=0 := by
  funext z
  change (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 0) z+
    (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 1) z+
    (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 2) z=0
  have h0 : (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 0) z=scaledFourier (2*m) f z := by
    simpa using scaled_base_translation (2*m) f 0 z
  have h1 : (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 1) z=scaledFourier (2*m) f ((z:ℂ)+1) := by
    simpa using scaled_base_translation (2*m) f 1 z
  have h2 : (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 2) z=scaledFourier (2*m) f ((z:ℂ)+2) := by
    simpa using scaled_base_translation (2*m) f 2 z
  rw [h0,h1,h2]
  exact scaled_trace hf (2*m) z.im_pos

theorem base_hecke_zero : baseGL 7=upperFinite 0 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseGL,baseMatrix,liftMatrix,upperFinite,upperInfinity,quadraticMatrix,matrix,
      GeneralLinearGroup.mkOfDetNeZero,Matrix.det_fin_two]
theorem base_hecke_one : baseGL 8=upperFinite 3 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseGL,baseMatrix,liftMatrix,upperFinite,upperInfinity,quadraticMatrix,matrix,
      GeneralLinearGroup.mkOfDetNeZero,Matrix.det_fin_two]
theorem base_hecke_infinity : baseGL 9=upperInfinity 0 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseGL,baseMatrix,liftMatrix,upperFinite,upperInfinity,quadraticMatrix,matrix,
      GeneralLinearGroup.mkOfDetNeZero,Matrix.det_fin_two]

theorem original_hecke_source {f : ℕ → ℂ} (hf : EulerData 27 f) (m : ℕ) :
    baseSum m ((Real.sqrt 2:ℂ)*f 2) (scaledFunction (2*m) f) 3=0 := by
  funext z
  change (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 7) z+
    (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 8) z+
    (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 9) z-
    ((Real.sqrt 2:ℂ)*f 2)*scaledFunction (2*m) f z=0
  rw [base_hecke_zero,base_hecke_one,base_hecke_infinity,
    upperFinite_slash,upperFinite_slash,upperInfinity_slash]
  simp only [scaledFunction,upperFinite_point,upperInfinity_point,Int.cast_zero,
    Int.cast_ofNat,add_zero]
  have hh := scaled_hecke_two hf m z.im_pos
  have hn : (2:ℂ)^m≠0 := pow_ne_zero _ (by norm_num)
  have hp : (2:ℂ)^(2*m)=((2:ℂ)^m)^2 := by rw [Nat.mul_comm 2 m,pow_mul]
  rw [hp] at hh
  dsimp only [FinitenessAllLevelHeckePower.scale] at hh
  field_simp [hn]
  ring_nf at hh ⊢
  linear_combination hh
#print axioms original_upper_trace
#print axioms original_hecke_source
end QuantitativeArithmeticSmallLevelTwentySeven
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenOriginalLowerV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySeven
open Complex Matrix UpperHalfPlane SmallLevelNormalized FinitenessOriginalInput
open QuantitativeArithmeticQuadraticMatrices QuantitativeArithmeticSmallLevelTwentySevenAffine
open scoped MatrixGroups ModularForm

theorem base_identity : baseGL 0=1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseGL,baseMatrix,liftMatrix,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.det_fin_two]

theorem base_upper_square : baseGL 1*baseGL 1=baseGL 2 :=
  lift_mul (baseMatrix 1) (baseMatrix 1) (baseMatrix 2)
    (baseGL_valid 1) (baseGL_valid 1) (baseGL_valid 2) (by decide)

theorem base_lower_square : baseGL 3*baseGL 3=baseGL 4 :=
  lift_mul (baseMatrix 3) (baseMatrix 3) (baseMatrix 4)
    (baseGL_valid 3) (baseGL_valid 3) (baseGL_valid 4) (by decide)

theorem original_upper_cubic {f : ℕ → ℂ} (hf : EulerData 27 f) (m : ℕ) :
    scaledFunction (2*m) f+(scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 1)+
      ((scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 1) ∣[((2*m:ℕ):ℤ)] baseGL 1)=0 := by
  have h := original_upper_trace hf m 0
  change (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 0)+
    (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 1)+
    (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  simpa only [base_identity,SlashAction.slash_one,← base_upper_square,SlashAction.slash_mul] using h

theorem scaled_fricke_eigen {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 27 k f) :
    ∃ χ : ℂ, ‖χ‖=1 ∧ scaledFunction k f ∣[(k:ℤ)] fricke 3 (by decide)=χ • scaledFunction k f := by
  obtain ⟨χ,hχ,hlaw⟩ := scaled_fricke hf
  have hh := fricke_law 3 k (by decide) (scaledFourier k f) χ hlaw
  have hn : χ≠0 := by intro hz; simp [hz] at hχ
  have ht := congrArg (fun G : ℍ → ℂ => χ⁻¹ • G) hh
  rw [smul_smul,inv_mul_cancel₀ hn,one_smul] at ht
  exact ⟨χ⁻¹,by simp [hχ],ht.symm⟩

theorem lower_fricke_product : baseGL 3*fricke 3 (by decide)*baseGL 1=fricke 3 (by decide) := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseGL,baseMatrix,liftMatrix,fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.det_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
  field_simp [hn]
  norm_num [hs]

theorem lower_fricke : baseGL 3*fricke 3 (by decide)=fricke 3 (by decide)*(baseGL 1)⁻¹ := by
  have h := congrArg (fun G : GL (Fin 2) ℝ => G*(baseGL 1)⁻¹) lower_fricke_product
  simpa only [mul_assoc,mul_inv_cancel,mul_one] using h

theorem original_lower_trace {f : ℕ → ℂ} (m : ℕ) (hf : IsSolution 27 (2*m) f) (a : ℂ) :
    baseSum m a (scaledFunction (2*m) f) 1=0 := by
  obtain ⟨χ,_hχ,hW⟩ := scaled_fricke_eigen hf
  have hi := QuantitativeArithmeticCubicTrace.inverse_trace _ _ _ (original_upper_cubic hf.toEulerData m)
  have ht := QuantitativeArithmeticCubicTrace.conjugate_trace _ _ _ (baseGL 3) (fricke 3 (by decide)) χ
    (det_one_inv _ (baseGL_det 1)) hi hW lower_fricke
  change (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 0)+
    (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 3)+
    (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 4)=0
  simpa only [base_identity,SlashAction.slash_one,← base_lower_square,SlashAction.slash_mul] using ht
#print axioms original_upper_cubic
#print axioms scaled_fricke_eigen
#print axioms original_lower_trace
end QuantitativeArithmeticSmallLevelTwentySeven
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenOriginalOddV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySeven
open Complex Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelOriginal SmallLevelGenerators
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticQuadraticMatrices QuantitativeArithmeticSmallLevelTwentySevenAffine
open scoped MatrixGroups ModularForm

def originalOdd : SL(2,ℤ) := ⟨!![2,-1;-27,14],by decide⟩
def scaledOdd : SL(2,ℤ) := ⟨!![2,-3;-9,14],by decide⟩

theorem original_odd_fixed {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 27 k f) :
    fourierFunction k f ∣[(k:ℤ)] originalOdd=fourierFunction k f := by
  have he : originalOdd=(oddMatrix 27 14 (by decide))⁻¹ := by decide
  rw [he]
  exact (slashStabilizer (k:ℤ) (fourierFunction k f)).inv_mem
    (original_odd (by decide) (by decide : 2*14=27+1) (by decide) hf)

theorem original_scaled_odd {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 27 k f) :
    scaledFunction k f ∣[(k:ℤ)] scaledOdd=scaledFunction k f := by
  funext z
  let w : ℍ := ⟨(z:ℂ)/3,by simpa using div_pos z.im_pos (by norm_num : (0:ℝ)<3)⟩
  have hh := congrFun (original_odd_fixed hf) w
  rw [ModularForm.SL_slash_apply] at hh ⊢
  have hd : denom originalOdd w=denom scaledOdd z := by
    norm_num [denom,ModularGroup.denom_apply,originalOdd,scaledOdd,w,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
    ring
  have hp : ((originalOdd • w : ℍ):ℂ)=((scaledOdd • z : ℍ):ℂ)/3 := by
    rw [coe_specialLinearGroup_apply,coe_specialLinearGroup_apply]
    norm_num [originalOdd,scaledOdd,w]
    ring
  rw [hd] at hh
  simpa only [fourierFunction,scaledFunction,scaledFourier,hp,w] using hh

def lowerThree : SL(2,ℤ) := ⟨!![1,0;3,1],by decide⟩

theorem base_upper_integral : baseGL 1=SpecialLinearGroup.mapGL ℝ T := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseGL,baseMatrix,liftMatrix,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.det_fin_two,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,ModularGroup.T]

theorem base_lower_integral : baseGL 3=SpecialLinearGroup.mapGL ℝ lowerThree := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseGL,baseMatrix,liftMatrix,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.det_fin_two,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,lowerThree]

theorem scaled_odd_word : SpecialLinearGroup.mapGL ℝ scaledOdd=
    (-1)*(baseGL 3)⁻¹*(baseGL 3)⁻¹*baseGL 1*(baseGL 3)⁻¹*(baseGL 1)⁻¹ := by
  have hi : scaledOdd=(-1)*lowerThree⁻¹*lowerThree⁻¹*T*lowerThree⁻¹*T⁻¹ := by decide
  have hn : SpecialLinearGroup.mapGL ℝ (-1 : SL(2,ℤ))=(-1 : GL (Fin 2) ℝ) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
  rw [hi,base_upper_integral,base_lower_integral]
  simp only [map_mul,map_inv,hn]

#print axioms original_scaled_odd
#print axioms scaled_odd_word
end QuantitativeArithmeticSmallLevelTwentySeven
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenOriginalAffineV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySeven
open Complex Matrix UpperHalfPlane ModularGroup SmallLevelNormalized FinitenessOriginalInput
open QuantitativeArithmeticQuadraticMatrices QuantitativeArithmeticSmallLevelTwentySevenAffine
open scoped MatrixGroups ModularForm

theorem base_SR : baseGL 3*baseGL 1=baseGL 5 :=
  lift_mul (baseMatrix 3) (baseMatrix 1) (baseMatrix 5)
    (baseGL_valid 3) (baseGL_valid 1) (baseGL_valid 5) (by decide)
theorem base_RS : baseGL 1*baseGL 3=baseGL 6 :=
  lift_mul (baseMatrix 1) (baseMatrix 3) (baseMatrix 6)
    (baseGL_valid 1) (baseGL_valid 3) (baseGL_valid 6) (by decide)

theorem original_commutator {f : ℕ → ℂ} (m : ℕ) (hf : IsSolution 27 (2*m) f) (a : ℂ) :
    baseSum m a (scaledFunction (2*m) f) 2=0 := by
  have hs := original_lower_trace m hf a
  change (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 0)+
    (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 3)+
    (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 4)=0 at hs
  rw [base_identity,SlashAction.slash_one,← base_lower_square,SlashAction.slash_mul] at hs
  have he := original_scaled_odd hf
  change scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ scaledOdd=scaledFunction (2*m) f at he
  rw [scaled_odd_word] at he
  have hm : (-1)*(baseGL 3)⁻¹*(baseGL 3)⁻¹*baseGL 1*(baseGL 3)⁻¹*(baseGL 1)⁻¹=
      (-1)*((baseGL 3)⁻¹*(baseGL 3)⁻¹*baseGL 1*(baseGL 3)⁻¹*(baseGL 1)⁻¹) := by group
  rw [hm,SlashAction.slash_mul,central_even] at he
  have hc := QuantitativeArithmeticCubicTrace.commutator _ _ (baseGL 1) (baseGL 3) hs he
  change (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 5)-
    (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] baseGL 6)=0
  rw [← base_SR,← base_RS]
  exact sub_eq_zero.mpr hc

/-- All four operator inputs are derived from the original Euler product
and untwisted entire Fricke equation. -/
theorem original_base_system {f : ℕ → ℂ} (m : ℕ) (hf : IsSolution 27 (2*m) f) :
    ∀ i : Fin 4, baseSum m ((Real.sqrt 2:ℂ)*f 2) (scaledFunction (2*m) f) i=0 := by
  intro i
  fin_cases i
  · exact original_upper_trace hf.toEulerData m _
  · exact original_lower_trace m hf _
  · exact original_commutator m hf _
  · exact original_hecke_source hf.toEulerData m

/-- The level27 defect satisfies the affine Hecke recurrence without any
extra twist functional equation or eigenvalue nonvanishing condition. -/
theorem original_affine {f : ℕ → ℂ} (m : ℕ) (hf : IsSolution 27 (2*m) f) :
    ((Real.sqrt 2:ℂ)*f 2) • defect m (scaledFunction (2*m) f)=
      (defect m (scaledFunction (2*m) f) ∣[((2*m:ℕ):ℤ)] affineGL 0)-
      (defect m (scaledFunction (2*m) f) ∣[((2*m:ℕ):ℤ)] affineGL 1)+
      (defect m (scaledFunction (2*m) f) ∣[((2*m:ℕ):ℤ)] affineGL 2)-
      (defect m (scaledFunction (2*m) f) ∣[((2*m:ℕ):ℤ)] affineGL 3) :=
  affine_defect m _ _ (original_base_system m hf)
#print axioms original_commutator
#print axioms original_base_system
#print axioms original_affine
end QuantitativeArithmeticSmallLevelTwentySeven
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenDilationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySeven
open Complex Matrix UpperHalfPlane SmallLevelNormalized FinitenessOriginalInput
open QuantitativeArithmeticQuadraticMatrices QuantitativeArithmeticSmallLevelTwentySevenAffine
open scoped MatrixGroups ModularForm

/-- Positive real dilation and real translation on the upper half-plane. -/
def dilate (r b : ℝ) (hr : 0<r) (z : ℍ) : ℍ :=
  ⟨(r:ℂ)*(z:ℂ)+b, by simpa using mul_pos hr z.im_pos⟩

theorem dilate_coe (r b : ℝ) (hr : 0<r) (z : ℍ) :
    ((dilate r b hr z:ℍ):ℂ)=(r:ℂ)*(z:ℂ)+b := rfl

theorem dilate_comp (r b s c : ℝ) (hr : 0<r) (hs : 0<s) (z : ℍ) :
    dilate r b hr (dilate s c hs z)=dilate (r*s) (r*c+b) (mul_pos hr hs) z := by
  apply UpperHalfPlane.ext
  simp only [dilate_coe,Complex.ofReal_mul,Complex.ofReal_add]
  ring

theorem affine_zero : affineGL 0=upperFinite (-1) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [affineGL,affineMatrix,liftMatrix,upperFinite,quadraticMatrix,matrix,
      GeneralLinearGroup.mkOfDetNeZero,Matrix.det_fin_two]

theorem affine_positive (i : Fin 3) : affineGL i.succ=upperInfinity i.val := by
  fin_cases i <;> apply Units.ext <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [affineGL,affineMatrix,liftMatrix,upperInfinity,quadraticMatrix,matrix,
      GeneralLinearGroup.mkOfDetNeZero,Matrix.det_fin_two]

theorem affine_finite_point (z : ℍ) :
    upperFinite (-1) • dilate 2 1 (by norm_num) z=z := by
  apply UpperHalfPlane.ext
  rw [upperFinite_point,dilate_coe]
  norm_num

theorem affine_infinite_point (i : ℤ) (z : ℍ) :
    upperInfinity i • dilate 2 1 (by norm_num) z=
      dilate 4 (2+i) (by norm_num) z := by
  apply UpperHalfPlane.ext
  rw [upperInfinity_point,dilate_coe,dilate_coe]
  push_cast
  ring

/-- The affine slash identity moves every point strictly upward. -/
theorem affine_dilation (m : ℕ) (a : ℂ) (A : ℍ → ℂ)
    (h : a • A=(A ∣[((2*m:ℕ):ℤ)] affineGL 0)-
      (A ∣[((2*m:ℕ):ℤ)] affineGL 1)+
      (A ∣[((2*m:ℕ):ℤ)] affineGL 2)-
      (A ∣[((2*m:ℕ):ℤ)] affineGL 3)) (z : ℍ) :
    A z=(2:ℂ)^m*a*A (dilate 2 1 (by norm_num) z)+
      (2:ℂ)^(2*m)*(A (dilate 4 2 (by norm_num) z)-
        A (dilate 4 3 (by norm_num) z)+A (dilate 4 4 (by norm_num) z)) := by
  have h1 : affineGL 1=upperInfinity 0 := affine_positive 0
  have h2 : affineGL 2=upperInfinity 1 := affine_positive 1
  have h3 : affineGL 3=upperInfinity 2 := affine_positive 2
  have hh := congrFun h (dilate 2 1 (by norm_num) z)
  simp only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Pi.add_apply] at hh
  rw [affine_zero,h1,h2,h3,upperFinite_slash,upperInfinity_slash,
    upperInfinity_slash,upperInfinity_slash,affine_finite_point,
    affine_infinite_point,affine_infinite_point,affine_infinite_point] at hh
  norm_num only [Int.cast_zero,Int.cast_one,Int.cast_ofNat,add_zero,
    show (2:ℝ)+1=3 by norm_num,show (2:ℝ)+2=4 by norm_num] at hh
  have hn : (2:ℂ)^m≠0 := pow_ne_zero _ (by norm_num)
  have hp : (2:ℂ)^(2*m)=((2:ℂ)^m)^2 := by rw [Nat.mul_comm 2 m,pow_mul]
  rw [hp]
  field_simp [hn] at hh
  linear_combination -hh

theorem original_dilation {f : ℕ → ℂ} (m : ℕ) (hf : IsSolution 27 (2*m) f) (z : ℍ) :
    defect m (scaledFunction (2*m) f) z=
      (2:ℂ)^m*((Real.sqrt 2:ℂ)*f 2)*
        defect m (scaledFunction (2*m) f) (dilate 2 1 (by norm_num) z)+
      (2:ℂ)^(2*m)*(defect m (scaledFunction (2*m) f) (dilate 4 2 (by norm_num) z)-
        defect m (scaledFunction (2*m) f) (dilate 4 3 (by norm_num) z)+
        defect m (scaledFunction (2*m) f) (dilate 4 4 (by norm_num) z)) :=
  affine_dilation m _ _ (original_affine m hf) z
#print axioms original_dilation
end QuantitativeArithmeticSmallLevelTwentySeven
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenTwistRootsV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySeven
open FinitenessNormalizedTwistProduct FinitenessNormalizedTwistLocal

theorem prime_divisor (p : ℕ) (hp : p.Prime) (h : p∣27) : p=3 := by
  have hpow : p∣3^3 := by simpa using h
  have h3 : p∣3 := hp.dvd_of_dvd_pow hpow
  exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h3

/-- No Steinberg prime occurs at level27, so all Ramanujan twists have the
same root factor, independently of their modulus. -/
theorem ramanujan_root (f : ℕ → ℂ) (q : ℕ) : root 27 f q=1 := by
  unfold root
  apply Finset.prod_eq_one
  intro p hp
  have hnot : ¬(p∣27 ∧ ¬p^2∣27) := by
    rintro ⟨hd,hsq⟩
    have he := prime_divisor p (Nat.prime_of_mem_primeFactors hp) hd
    subst p
    exact hsq (by decide)
  simp only [sign,ite_eq_right hnot,ite_self]
#print axioms ramanujan_root
end QuantitativeArithmeticSmallLevelTwentySeven
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenOriginalTaylorV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySeven
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct FinitenessRamanujanFourier
open SmallLevelAdditive SmallLevelTaylor Complex Set MeasureTheory

theorem physical_sign (m : ℕ) {ε : ℂ} (hε : ε=1 ∨ ε= -1) :
    ε*Complex.I^(2*m)=1 ∨ ε*Complex.I^(2*m)= -1 := by
  have hi : Complex.I^(2*m)=(-1:ℂ)^m := by rw [pow_mul,Complex.I_sq]
  rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hε with rfl|rfl <;> simp [hi,h]

/-- The sign is chosen once for every modulus. Highly ramified level27 has
no modulus-dependent root factor. -/
theorem original_twisted_taylor (m : ℕ) {f : ℕ → ℂ} (hf : IsSolution 27 (2*m) f) :
    ∃ η : ℂ, (η=1 ∨ η= -1) ∧ ∀ q : ℕ, 0<q → ∀ r : ℝ, r≠0 →
      ∃ B : ℝ, ∀ M : ℕ,
        AnalyticOnNhd ℂ (mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
          (Nat.lcm 27 (q^2)) r η M)) {s : ℂ | B-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, B<s.re →
          transform (fullCoefficients (twisted f q) (2*m)) r s-
            η*(((Nat.lcm 27 (q^2):ℝ)*r^2:ℝ):ℂ)^(s-(((2*m:ℕ):ℂ)/2))*
              normalizedTaylorSum (2*m) (fullCoefficients (twisted f q) (2*m))
                (Nat.lcm 27 (q^2)) r M s=
            mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
              (Nat.lcm 27 (q^2)) r η M) s := by
  obtain ⟨ε,hε,hlaw⟩ := original_ramanujan_taylor_rows (by decide : 0<27) (even_two_mul m) hf
  refine ⟨ε*I^(2*m),physical_sign m hε,?_⟩
  intro q hq r hr
  simpa only [ramanujan_root,one_mul] using hlaw q hq r hr

/-- Every Ramanujan Taylor row is an actual finite sum of additive-twist
transforms. No continuation of the individual twists is assumed. -/
theorem original_ramanujan_rows (m : ℕ) {f : ℕ → ℂ} (hf : IsSolution 27 (2*m) f) :
    ∃ η : ℂ, (η=1 ∨ η= -1) ∧ ∀ q : ℕ, 0<q → ∀ r : ℝ, r≠0 →
      ∃ B : ℝ, ∀ M : ℕ,
        AnalyticOnNhd ℂ (mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
          (Nat.lcm 27 (q^2)) r η M)) {s : ℂ | B-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, B<s.re →
          ramanujanAdditive (2*m) f q r s-
            η*(((Nat.lcm 27 (q^2):ℝ)*r^2:ℝ):ℂ)^(s-(((2*m:ℕ):ℂ)/2))*
              ramanujanTaylorSum (2*m) f q (Nat.lcm 27 (q^2)) r M s=
            mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
              (Nat.lcm 27 (q^2)) r η M) s := by
  obtain ⟨η,hη,ht⟩ := original_twisted_taylor m hf
  refine ⟨η,hη,?_⟩
  intro q hq r hr
  obtain ⟨B,hB⟩ := ht q hq r hr
  obtain ⟨C,hC⟩ := ramanujan_additive_sum hf q
  refine ⟨max B C,?_⟩
  intro M
  constructor
  · intro s hs
    apply (hB M).1 s
    change max B C-(M:ℝ)<s.re at hs
    change B-(M:ℝ)<s.re
    linarith [le_max_left B C]
  · intro s hs
    have hsB : B<s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hsC : C<s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have hm := (hB M).2 s hsB
    rw [hC r s hsC] at hm
    have he : normalizedTaylorSum (2*m) (fullCoefficients (twisted f q) (2*m))
        (Nat.lcm 27 (q^2)) r M s=ramanujanTaylorSum (2*m) f q (Nat.lcm 27 (q^2)) r M s := by
      unfold normalizedTaylorSum ramanujanTaylorSum ramanujanAdditive
      apply Finset.sum_congr rfl
      intro n _
      rw [hC _ (s+(n:ℂ)) (by
        simp only [Complex.add_re,Complex.natCast_re]
        exact lt_of_lt_of_le hsC (le_add_of_nonneg_right (Nat.cast_nonneg n)))]
    rw [he] at hm
    exact hm
#print axioms original_twisted_taylor
#print axioms original_ramanujan_rows
end QuantitativeArithmeticSmallLevelTwentySeven
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenRamanujanSplitV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySeven
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessRamanujanFourier SmallLevelAdditive SmallLevelTaylor Complex Set MeasureTheory

/-- The actual leading and positive-shift source rows, with one sign for all
moduli. This does not assert closure of any finite observation space. -/
theorem original_ramanujan_split (m : ℕ) {f : ℕ → ℂ} (hf : IsSolution 27 (2*m) f) :
    ∃ η : ℂ, (η=1 ∨ η= -1) ∧ ∀ q : ℕ, 0<q → ∀ r : ℝ, r≠0 →
      ∃ B : ℝ, ∀ M : ℕ,
        AnalyticOnNhd ℂ (mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
          (Nat.lcm 27 (q^2)) r η (M+1))) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
        ∀ s : ℂ, B<s.re →
          ramanujanAdditive (2*m) f q r s-
            taylorRowScalar (2*m) (Nat.lcm 27 (q^2)) r η 0 s*
              ramanujanAdditive (2*m) f q (-1/((Nat.lcm 27 (q^2):ℝ)*r)) s=
            mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
              (Nat.lcm 27 (q^2)) r η (M+1)) s+
            ∑ n∈Finset.range M,
              taylorRowScalar (2*m) (Nat.lcm 27 (q^2)) r η (n+1) s*
                ramanujanAdditive (2*m) f q (-1/((Nat.lcm 27 (q^2):ℝ)*r)) (s+((n+1:ℕ):ℂ)) := by
  obtain ⟨η,hη,ht⟩ := original_ramanujan_rows m hf
  refine ⟨η,hη,?_⟩
  intro q hq r hr
  obtain ⟨B,hB⟩ := ht q hq r hr
  refine ⟨B,?_⟩
  intro M
  constructor
  · simpa only [Nat.cast_add,Nat.cast_one] using (hB (M+1)).1
  · intro s hs
    have h := (hB (M+1)).2 s hs
    rw [ramanujanTaylorSum_split] at h
    linear_combination h
#print axioms original_ramanujan_split
end QuantitativeArithmeticSmallLevelTwentySeven
end
end
