module

public import QuantitativeArithmeticSmallLevelTwentyTwoDefectEquationsV1
public import QuantitativeArithmeticSmallLevelTwentyTwoEliminationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct
open scoped MatrixGroups ModularForm Manifold

/-- The original E eigenvalue is exactly the local Ramanujan root at two. -/
theorem original_E_root {k : ℕ} {f : ℕ→ℂ} (hf : IsSolution 22 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] E=
      root 22 f 2 • SmallLevelOriginal.fourierFunction k f := by
  obtain ⟨ε,_,hlaw⟩:=FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<22) hf
  have hQ : SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SmallLevelRamifiedTwo.Q 22 12 (by decide)=
      root 22 f 2 • SmallLevelOriginal.fourierFunction k f := by
    apply SmallLevelRamifiedTwo.eigen_of_fricke (by decide : 0<22) (by decide : 2*12=22+2) _ (ε*Complex.I^k)
    · intro z hz
      simpa [root,FinitenessAnalyticReconstruction.twist,Finset.sum_range_succ] using hlaw 1 (by decide) z hz
    · intro z hz
      have h:=hlaw 2 (by decide) z hz
      have ht (G : ℂ → ℂ) (w : ℂ) : FinitenessAnalyticReconstruction.twist G 2 w=G (w+1/2) := by
        unfold FinitenessAnalyticReconstruction.twist
        rw [show (Finset.range 2).filter (fun a => Nat.Coprime a 2)={1} by decide]
        simp
      have hsqrt : Real.sqrt 44=Real.sqrt 2*Real.sqrt 22 := by
        rw [show (44:ℝ)=2*22 by norm_num,Real.sqrt_mul (by norm_num)]
      rw [show Nat.lcm 22 (2^2)=44 by decide,Nat.cast_ofNat,hsqrt,Complex.ofReal_mul,ht,ht] at h
      simpa only [Nat.cast_ofNat,mul_assoc,show (44:ℂ)=2*22 by norm_num] using h
  have hh:=congrArg (fun F : ℍ→ℂ => F ∣[(k:ℤ)] E) hQ
  rw [← SlashAction.slash_mul,show SmallLevelRamifiedTwo.Q 22 12 (by decide)*E=1 from mul_inv_cancel _,
    SlashAction.slash_one,det_one_smul _ E_det] at hh
  rcases root_unit hf.toEulerData 2 with h|h
  · rw [h] at hh ⊢; simpa using hh.symm
  · rw [h] at hh ⊢; simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg hh.symm

private theorem periodic_one (k : ℕ) (f : ℕ→ℂ) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation 1=SmallLevelOriginal.fourierFunction k f := by
  have ht : translation 1=SpecialLinearGroup.mapGL ℝ T := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero,T,
        SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
  rw [ht]
  exact original_T k f

private theorem periodic_minus (k : ℕ) (f : ℕ→ℂ) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-1)=
      SmallLevelOriginal.fourierFunction k f := by
  have ht : translation (-1)=SpecialLinearGroup.mapGL ℝ T⁻¹ := by
    rw [show T⁻¹=(⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ)) by decide]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero,T,
        SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
  rw [ht]
  have hh:=congrArg (fun F : ℍ→ℂ => F ∣[(k:ℤ)] (T⁻¹:SL(2,ℤ))) (original_T k f)
  simp only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] at hh
  exact hh.symm


/-- The complete finite level22 endgame up to the generating-subgroup step:
one separated denominator-five pair forces the actual Y and P laws.
The pair remains an explicit analytic input, not an asserted consequence. -/
theorem original_Y_P_of_five_pair (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : IsSolution 22 (2*m) f)
    (hfive : let F:=SmallLevelOriginal.fourierFunction (2*m) f
      F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ B5-F=
        -((F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ A5-F) ∣[((2*m:ℕ):ℤ)] translation (4/5))) :
    let F:=SmallLevelOriginal.fourierFunction (2*m) f
    (F ∣[((2*m:ℕ):ℤ)] Y=F) ∧ (F ∣[((2*m:ℕ):ℤ)] P=root 22 f 2 • F) := by
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let δ:=root 22 f 2
  have hδ : δ=1 ∨ δ= -1:=root_unit hf.toEulerData 2
  obtain ⟨η,hη,hW⟩:=original_fricke_sign (by decide : 0<22) m hf
  change F ∣[((2*m:ℕ):ℤ)] W=η • F at hW
  have hE : F ∣[((2*m:ℕ):ℤ)] E=δ • F:=original_E_root hf
  have hEi : F ∣[((2*m:ℕ):ℤ)] E⁻¹=δ • F := by
    have hh:=congrArg (fun G : ℍ→ℂ => G ∣[((2*m:ℕ):ℤ)] E⁻¹) hE
    rw [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one,det_one_smul _ (det_one_inv _ E_det)] at hh
    rcases hδ with h|h
    · rw [h] at hh ⊢; simpa using hh.symm
    · rw [h] at hh ⊢; simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg hh.symm
  have hT : F ∣[((2*m:ℕ):ℤ)] translation 1=F:=periodic_one (2*m) f
  have hTm : F ∣[((2*m:ℕ):ℤ)] translation (-1)=F:=periodic_minus (2*m) f
  have hHecke:=original_ramified_slash m hm hf
  have hthree:=original_three_defect hf
  change F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ X-F=
    -(auxiliaryDefect m F ∣[((2*m:ℕ):ℤ)] translation (-2/3)) at hthree
  have h1:=first_defect_relation m F δ η hδ hη hT hTm hE hEi hW hHecke hthree
  have h2:=second_defect_relation m F δ η hδ hη hT hTm hE hEi hW hHecke hthree hfive
  have hK:=original_K m hf η hη hW
  have hL:=original_L m hf δ η hδ hη hE hW
  have hF : MDiff F:=SmallLevelOriginal.fourierFunction_holomorphic hf
  have hu : MDiff (auxiliaryDefect m F):=(hF.slash ((2*m:ℕ):ℤ) (SpecialLinearGroup.mapGL ℝ Y)).sub hF
  have hz:=two_defects_zero (by omega : 0<2*m) (auxiliaryDefect m F) (pDefect m F δ) hu
    δ η hδ hη hK hL h1 h2
  exact ⟨sub_eq_zero.mp hz.1,sub_eq_zero.mp hz.2⟩

#print axioms original_E_root
#print axioms original_Y_P_of_five_pair
end QuantitativeArithmeticSmallLevelTwentyTwo
