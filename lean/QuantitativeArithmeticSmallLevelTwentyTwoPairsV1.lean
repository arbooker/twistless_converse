module

public import SmallLevelThirtyPairsV1
public import SmallLevelNormalizedEvenFrickeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelGenerators
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

def X : SL(2,ℤ) := ⟨!![3,-1;22,-7],by decide⟩
def Y : SL(2,ℤ) := ⟨!![3,1;-22,-7],by decide⟩
def E : GL (Fin 2) ℝ := (SmallLevelRamifiedTwo.Q 22 12 (by decide))⁻¹

theorem E_det : (GeneralLinearGroup.det E:ℝ)=1 :=
  det_one_inv _ (SmallLevelRamifiedTwo.Q_det _ _ _)

/-- The normalized ramified modulus-two matrix acts by its original sign. -/
theorem original_E {k : ℕ} {f : ℕ→ℂ} (hf : IsSolution 22 k f) :
    ∃ δ : ℂ, (δ=1 ∨ δ= -1) ∧
      SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] E=
        δ • SmallLevelOriginal.fourierFunction k f := by
  obtain ⟨δ,hδ,hQ⟩ := SmallLevelRamifiedTwo.original_eigen
    (by decide : 0<22) (by decide : 2*12=22+2) (by decide) hf
  refine ⟨δ,hδ,?_⟩
  have hh := congrArg (fun F : ℍ→ℂ => F ∣[(k:ℤ)] E) hQ
  rw [← SlashAction.slash_mul,show SmallLevelRamifiedTwo.Q 22 12 (by decide)*E=1 by
    exact mul_inv_cancel _,SlashAction.slash_one,
    det_one_smul _ E_det] at hh
  rcases hδ with rfl|rfl
  · simpa using hh.symm
  · simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg hh.symm

/-- The actual modulus-3 normalized two-branch relation. -/
theorem original_pair_three {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 22 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 22 (by decide))⁻¹*translation (1/3)*fricke 198 (by decide)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 22 (by decide))⁻¹*translation (-(1/3))*fricke 198 (by decide)))=
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/3))+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(1/3))) := by
  obtain ⟨ε,_,hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws
    (by decide : 0<22) hf
  have hr : FinitenessNormalizedTwistProduct.root 22 f 3=1 := by
    unfold FinitenessNormalizedTwistProduct.root
    rw [(by decide : Nat.Prime 3).primeFactors]
    simp [FinitenessNormalizedTwistLocal.sign,show ¬3∣(22:ℕ) by decide]
  have h := pair_of_fricke 22 198 k (by decide) (by decide) (1/3)
    (fourier (fullCoefficients f k)) (ε*Complex.I^k) 1 (Or.inl rfl)
  simp only [one_smul] at h
  apply h
  · intro z hz
    simpa [FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  · intro z hz
    have hh := hlaw 3 (by decide) z hz
    rw [show Nat.lcm 22 (3^2)=198 by decide, hr, one_mul,
      SmallLevelThree.twist_three _ (periodic _), SmallLevelThree.twist_three _ (periodic _)] at hh
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,one_mul] using hh


private theorem sqrt_198 : Real.sqrt 198=3*Real.sqrt 22 := by
  rw [show (198:ℝ)=9*22 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

private theorem pair_branches :
    ((fricke 22 (by decide))⁻¹*translation (1/3)*fricke 198 (by decide))=
      SpecialLinearGroup.mapGL ℝ Y*translation (-1/3) ∧
    ((fricke 22 (by decide))⁻¹*translation (-(1/3))*fricke 198 (by decide))=
      SpecialLinearGroup.mapGL ℝ X*translation (1/3) := by
  have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hi : (fricke 22 (by decide))⁻¹=matrix 0 (1/Real.sqrt 22) (-Real.sqrt 22) 0 (by
      field_simp; ring) := by
    apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply,Fin.sum_univ_two]
  rw [hi]
  constructor <;> apply Units.ext <;> ext i j <;>
    fin_cases i <;> fin_cases j <;>
      norm_num [X,Y,translation,fricke,sqrt_198,matrix,GeneralLinearGroup.mkOfDetNeZero,
        SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
        Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
      field_simp [hn] <;> nlinarith

/-- The auxiliary denominator-three defects are paired directly by the
original Ramanujan functional equation, without any continuation input. -/
theorem original_three_defect {k : ℕ} {f : ℕ→ℂ} (hf : IsSolution 22 k f) :
    let F:=SmallLevelOriginal.fourierFunction k f
    (F ∣[(k:ℤ)] X)-F= -((F ∣[(k:ℤ)] Y)-F) ∣[(k:ℤ)] translation (-2/3) := by
  let F:=SmallLevelOriginal.fourierFunction k f
  have hh:=original_pair_three hf
  rw [pair_branches.1,pair_branches.2,SlashAction.slash_mul,SlashAction.slash_mul] at hh
  have he:=congrArg (fun G : ℍ→ℂ => G ∣[(k:ℤ)] translation (-1/3)) hh
  simp only [SlashAction.add_slash,← SlashAction.slash_mul,mul_assoc,translation_mul] at he
  rw [show (1/3:ℝ)+(-1/3)=0 by ring,
    show (-1/3:ℝ)+(-1/3)= -2/3 by ring,
    show -(1/3:ℝ)+(-1/3)= -2/3 by ring] at he
  have h0 : translation 0=(1:GL (Fin 2) ℝ) := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]
  rw [h0] at he
  simp only [mul_one,SlashAction.slash_one,SlashAction.slash_mul] at he
  simp only [sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash]
  linear_combination he

#print axioms original_E
#print axioms original_three_defect
end QuantitativeArithmeticSmallLevelTwentyTwo
