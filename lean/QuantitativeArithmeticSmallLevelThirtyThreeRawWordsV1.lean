module
public import QuantitativeArithmeticSmallLevelThirtyThreeKnownWordsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups

def rawBase : Fin 5 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![1,1;0,1]
  | 1 => !![1,0;33,1]
  | 2 => !![2,-1;-33,17]
  | 3 => !![0,-1;33,0]
  | _ => !![6,-1;-33,6]

def rawScale : Fin 5 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1/Real.sqrt 33
  | _ => 1/Real.sqrt 3

def rawWord : Word → Matrix (Fin 2) (Fin 2) ℤ
  | .one => 1
  | .generator i => rawBase i
  | .mul u v => rawWord u * rawWord v
  | .inv w => (rawWord w).adjugate

def wordScale : Word → ℝ
  | .one => 1
  | .generator i => rawScale i
  | .mul u v => wordScale u * wordScale v
  | .inv w => wordScale w

theorem rawBase_coordinates (i : Fin 5) :
    (seed i).val=rawScale i • (rawBase i).map (Int.castRingHom ℝ) := by
  have h3 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have h33 : (Real.sqrt 33)^2=33 := Real.sq_sqrt (by norm_num)
  have hn3 : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn33 : Real.sqrt 33≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [seed,rawBase,rawScale,SmallLevelThirtyThree.B,fricke,matrix,
      GeneralLinearGroup.mkOfDetNeZero,T,lower,oddMatrix,SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe,SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.inv_def,Matrix.det_fin_two] <;>
    field_simp [hn3,hn33] <;> norm_num [h3,h33]

private theorem inverse_det_one (g : GL (Fin 2) ℝ)
    (hg : (GeneralLinearGroup.det g:ℝ)=1) :
    (g⁻¹).val=g.val.adjugate := by
  change g.val.det=1 at hg
  rw [GeneralLinearGroup.coe_inv,Matrix.inv_def,hg]
  simp

/-- Integer products and adjugates certify the actual normalized word. -/
theorem rawWord_coordinates (w : Word) :
    (value w).val=wordScale w • (rawWord w).map (Int.castRingHom ℝ) := by
  induction w with
  | one => simp [value,wordScale,rawWord]
  | generator i => exact rawBase_coordinates i
  | mul u v hu hv =>
    simp only [value,wordScale,rawWord,Units.val_mul,hu,hv]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.map_apply] <;> ring
  | inv w hw =>
    simp only [value,wordScale,rawWord]
    rw [inverse_det_one _ (value_det w),hw,Matrix.adjugate_smul]
    norm_num only [Fintype.card_fin,Nat.reduceSub,pow_one]
    congr 1
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.adjugate_fin_two,Matrix.map_apply]

/-- A finite integer identity suffices to certify a primitive matrix row. -/
theorem primitive_word_coordinates (w : Word)
    (G : Matrix (Fin 2) (Fin 2) ℤ) (d : ℤ) (hd : rawWord w=d • G) :
    (value w).val=(wordScale w*(d:ℝ)) • G.map (Int.castRingHom ℝ) := by
  rw [rawWord_coordinates,hd]
  ext a b
  simp only [Matrix.smul_apply,Matrix.map_apply,Int.coe_castRingHom,smul_eq_mul,Int.cast_mul]
  ring

#print axioms rawWord_coordinates
#print axioms primitive_word_coordinates
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
