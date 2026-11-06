module

public import SmallLevelNormalizedFourBranchV1
public import SmallLevelSixPairV1

/-! Consolidated chapter: SmallLevelThirtyFourPrimeFive. Original declarations and local scopes are retained. -/

/-! ## SmallLevelThirtyFourPrimeFiveCentersV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourPrimeFive
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

def G1 : SL(2,ℤ) := ⟨!![5,-1;-34,7],by decide⟩
def Gm1 : SL(2,ℤ) := ⟨!![5,1;34,7],by decide⟩
def G2 : SL(2,ℤ) := ⟨!![5,2;-68,-27],by decide⟩
def Gm2 : SL(2,ℤ) := ⟨!![5,-2;68,-27],by decide⟩

theorem sqrt_conductor : Real.sqrt 850=5*Real.sqrt 34 := by
  rw [show (850:ℝ)=25*34 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem G1_branch : fricke 34 (by decide)*SpecialLinearGroup.mapGL ℝ G1*translation (1/5)=
    translation (1/5)*fricke 850 (by decide) := by
  have ht : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,G1,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

#print axioms G1_branch

theorem Gm1_branch : fricke 34 (by decide)*SpecialLinearGroup.mapGL ℝ Gm1*translation (-(1/5))=
    translation (-(1/5))*fricke 850 (by decide) := by
  have ht : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Gm1,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

#print axioms Gm1_branch

theorem G2_branch : fricke 34 (by decide)*SpecialLinearGroup.mapGL ℝ G2*translation (-(2/5))=
    translation (2/5)*fricke 850 (by decide) := by
  have ht : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,G2,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

#print axioms G2_branch

theorem Gm2_branch : fricke 34 (by decide)*SpecialLinearGroup.mapGL ℝ Gm2*translation (2/5)=
    translation (-(2/5))*fricke 850 (by decide) := by
  have ht : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Gm2,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

#print axioms Gm2_branch

end SmallLevelThirtyFourPrimeFive
end
end

/-! ## SmallLevelThirtyFourPrimeFiveOriginalV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourPrimeFive
open Matrix UpperHalfPlane SmallLevelNormalized
open FinitenessFourierConstruction FinitenessOriginalFourier FinitenessAnalyticReconstruction
open scoped MatrixGroups ModularForm

theorem twist_five (F : ℂ→ℂ) (hp : ∀ z,F (z+1)=F z) (z : ℂ) :
    twist F 5 z=F (z+1/5)+F (z-1/5)+F (z+2/5)+F (z-2/5) := by
  unfold twist
  rw [show (Finset.range 5).filter (fun a => Nat.Coprime a 5)={1,2,3,4} by decide]
  norm_num
  rw [show z+3/5=(z-2/5)+1 by ring,hp,show z+4/5=(z-1/5)+1 by ring,hp]
  ring

/-- The actual original prime-five Ramanujan law, valid at every
Hecke eigenvalue, before identifying its four matrix branches. -/
theorem original_five_fricke {k : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] ((fricke 34 (by decide))⁻¹*translation (1/5)*fricke 850 (by decide)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] ((fricke 34 (by decide))⁻¹*translation (-(1/5))*fricke 850 (by decide)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] ((fricke 34 (by decide))⁻¹*translation (2/5)*fricke 850 (by decide)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] ((fricke 34 (by decide))⁻¹*translation (-(2/5))*fricke 850 (by decide)))=
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/5))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(1/5)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (2/5))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(2/5))) := by
  obtain ⟨ε,_,hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<34) hf
  have hr : FinitenessNormalizedTwistProduct.root 34 f 5=1 := by
    unfold FinitenessNormalizedTwistProduct.root
    rw [Nat.prime_five.primeFactors]
    norm_num [FinitenessNormalizedTwistLocal.sign]
  apply four_branch_of_fricke 34 850 k (by decide) (by decide)
    (1/5) (-(1/5)) (2/5) (-(2/5))
    (FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f k))
    (ε*Complex.I^k)
  · intro z hz
    simpa [FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  · intro z hz
    have h := hlaw 5 (by decide) z hz
    rw [show Nat.lcm 34 (5^2)=850 by decide,hr,
      twist_five _ (FinitenessFourierConstruction.periodic _),
      twist_five _ (FinitenessFourierConstruction.periodic _)] at h
    simpa only [one_mul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,
      Complex.ofReal_neg,sub_eq_add_neg,mul_assoc] using h

#print axioms original_five_fricke
end SmallLevelThirtyFourPrimeFive
end
end
