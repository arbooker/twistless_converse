module

public import QuantitativeArithmeticSmallLevelThirtyFiveCentersV1
public import SmallLevelOddFrickeV1
public import SmallLevelOddWordsV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

def six : SL(2,ℤ) := ⟨!![6,-1;-35,6],by decide⟩
def row : Fin 7 → SL(2,ℤ)
  | 0 => ⟨!![1,-1;35,-34],by decide⟩
  | 1 => ⟨!![2,-1;-175,88],by decide⟩
  | 2 => ⟨!![2,-1;-105,53],by decide⟩
  | 3 => ⟨!![2,-1;-35,18],by decide⟩
  | 4 => ⟨!![2,-1;35,-17],by decide⟩
  | 5 => ⟨!![6,-5;-175,146],by decide⟩
  | 6 => ⟨!![6,-5;35,-29],by decide⟩

theorem original_six {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] six=
      SmallLevelOriginal.fourierFunction k f := by
  have he : SpecialLinearGroup.mapGL ℝ six=SmallLevelThirtyFive.B := by
    apply Units.ext
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [six,SmallLevelThirtyFive.B,matrix,GeneralLinearGroup.mkOfDetNeZero,
        SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
  change SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ six=_
  rw [he]
  exact SmallLevelSixEigen.thirty_five_B hk hf

theorem original_rows {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) (i : Fin 7) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] row i=
      SmallLevelOriginal.fourierFunction k f := by
  let K := slashStabilizer (k:ℤ) (SmallLevelOriginal.fourierFunction k f)
  have ht : T∈K := original_T k f
  have hu : lower 35∈K := original_lower (by decide) hf
  have he : (oddMatrix 35 18 (by decide))⁻¹∈K := K.inv_mem
    (original_odd (by decide) (by decide : 2*18=35+1) (by decide) hf)
  have hb : six∈K := original_six hk hf
  change row i∈K
  fin_cases i
  · change row 0∈K
    rw [show row 0=lower 35*T⁻¹ by decide]
    exact K.mul_mem hu (K.inv_mem ht)
  · change row 1∈K
    rw [show row 1=(lower 35)⁻¹*(lower 35)⁻¹*(oddMatrix 35 18 (by decide))⁻¹ by decide]
    exact K.mul_mem (K.mul_mem (K.inv_mem hu) (K.inv_mem hu)) he
  · change row 2∈K
    rw [show row 2=(lower 35)⁻¹*(oddMatrix 35 18 (by decide))⁻¹ by decide]
    exact K.mul_mem (K.inv_mem hu) he
  · change row 3∈K
    exact he
  · change row 4∈K
    rw [show row 4=lower 35*(oddMatrix 35 18 (by decide))⁻¹ by decide]
    exact K.mul_mem hu he
  · change row 5∈K
    rw [show row 5=(lower 35)⁻¹*six⁻¹*T⁻¹ by decide]
    exact K.mul_mem (K.mul_mem (K.inv_mem hu) (K.inv_mem hb)) (K.inv_mem ht)
  · change row 6∈K
    rw [show row 6=six⁻¹*T⁻¹ by decide]
    exact K.mul_mem (K.inv_mem hb) (K.inv_mem ht)

#print axioms original_six
#print axioms original_rows
end QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGroupFrickeRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

/-- The normalized matrices proportional to (0,1;-35,d), for
 d=-70,-35,0,35 respectively. All have determinant one. -/
def frickeRow (i : Fin 4) : GL (Fin 2) ℝ :=
  fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ (T^(2-(i.val:ℤ)))

theorem original_fricke_rows (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ i : Fin 4,
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] frickeRow i=
        χ • SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨χ,hχ,hF⟩ := original_fricke_sign (by decide : 0<35) m hf
  refine ⟨χ,hχ,?_⟩
  intro i
  let K := slashStabilizer ((2*m:ℕ):ℤ) (SmallLevelOriginal.fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hp := K.zpow_mem ht (2-(i.val:ℤ))
  rw [frickeRow,SlashAction.slash_mul,hF]
  change (χ • SmallLevelOriginal.fourierFunction (2*m) f) ∣[((2*m:ℕ):ℤ)]
    (T^(2-(i.val:ℤ)))=χ • SmallLevelOriginal.fourierFunction (2*m) f
  rw [ModularForm.SL_smul_slash]
  exact congrArg (fun G : ℍ → ℂ => χ • G) hp

#print axioms original_fricke_rows
end QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGroupFrickeCoordinatesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

/-- Exact normalized coordinates of the four selected Fricke rows. -/
theorem frickeRow_matrix (i : Fin 4) :
    (frickeRow i).val=!![0,-1/Real.sqrt 35;
      Real.sqrt 35,Real.sqrt 35*(2-(i.val:ℝ))] := by
  have hp : ∀ j : Fin 4, T^(2-(j.val:ℤ))=
      (⟨!![1,2-(j.val:ℤ);0,1],by simp [det_fin_two]⟩ : SL(2,ℤ)) := by decide
  unfold frickeRow
  rw [hp]
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [frickeRow,fricke,matrix,ModularGroup.T,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Fin.sum_univ_two,
      pow_two]

#print axioms frickeRow_matrix
end QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGroupFourierRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
  FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

/-- Literal Fourier transformation laws for all seven selected integral
rows, with no continuation or eigenvalue premise. -/
theorem original_rows_fourier {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) (i : Fin 7)
    (z : ℂ) (hz : 0<z.im) :
    fourier (fullCoefficients f k) z=
      1/(((row i).val 1 0:ℂ)*z+((row i).val 1 1:ℂ))^k*
        fourier (fullCoefficients f k)
          ((((row i).val 0 0:ℂ)*z+((row i).val 0 1:ℂ))/
            (((row i).val 1 0:ℂ)*z+((row i).val 1 1:ℂ))) := by
  have h := congrFun (original_rows hk hf i) ⟨z,hz⟩
  rw [ModularForm.SL_slash_apply] at h
  simp only [SmallLevelOriginal.fourierFunction,coe_specialLinearGroup_apply,
    zpow_neg,zpow_natCast] at h
  norm_num [denom,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe] at h
  simpa only [one_div,mul_comm] using h.symm

theorem frickeRow_det (i : Fin 4) : (GeneralLinearGroup.det (frickeRow i):ℝ)=1 := by
  change (frickeRow i).val.det=1
  rw [frickeRow_matrix]
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  norm_num [det_fin_two,hn]

/-- The four Fricke rows as literal Fourier laws in their determinant-one
normalization. The same original sign works for all four rows. -/
theorem original_fricke_rows_fourier (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ i : Fin 4, ∀ z : ℂ, 0<z.im →
      fourier (fullCoefficients f (2*m)) z=
        χ/(((Real.sqrt 35:ℂ)*z+(Real.sqrt 35:ℂ)*(2-(i.val:ℂ)))^(2*m))*
          fourier (fullCoefficients f (2*m))
            ((-1/(Real.sqrt 35:ℂ))/
              ((Real.sqrt 35:ℂ)*z+(Real.sqrt 35:ℂ)*(2-(i.val:ℂ)))) := by
  obtain ⟨χ,hχ,hF⟩ := original_fricke_rows m hf
  refine ⟨χ,hχ,?_⟩
  intro i z hz
  have hback : SmallLevelOriginal.fourierFunction (2*m) f=
      χ • (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] frickeRow i) := by
    rcases hχ with rfl|rfl
    · simpa using (hF i).symm
    · simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg (hF i).symm
  have h := congrFun hback ⟨z,hz⟩
  rw [Pi.smul_apply,smul_eq_mul,det_one_slash _ (frickeRow_det i),zpow_neg,zpow_natCast] at h
  simp only [SmallLevelOriginal.fourierFunction] at h
  rw [coe_smul_of_det_pos (by rw [frickeRow_det]; norm_num)] at h
  norm_num [num,denom,frickeRow_matrix,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Complex.ofReal_zero,zero_mul,zero_add,Complex.ofReal_div,Complex.ofReal_neg,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_ofNat,
    Complex.ofReal_natCast,zpow_neg,zpow_natCast] at h
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h

#print axioms original_rows_fourier
#print axioms original_fricke_rows_fourier
end QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
end
end
