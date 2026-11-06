module

public import SmallLevelNormalizedEvenFrickeV1
public import SmallLevelThirtySixFourierV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEighteen

open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelRamifiedTwo
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

abbrev Q₂ : GL (Fin 2) ℝ := Q 18 10 (by decide)
def C : SL(2,ℤ) := ⟨!![11,1;54,5], by decide⟩
def D : GL (Fin 2) ℝ := matrix 47 (13/3) 54 5 (by norm_num)
def H : GL (Fin 2) ℝ := matrix 31 (-27) 54 (-47) (by norm_num)
def E : GL (Fin 2) ℝ := matrix (-1) (-(2/3)) 0 (-1) (by norm_num)

private theorem branch_left :
    translation (-(1/3))*Q₂*translation (-(1/3))*Q₂=SpecialLinearGroup.mapGL ℝ C := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q₂, Q, C, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne] <;> nlinarith

private theorem branch_other :
    translation (1/3)*Q₂*translation (-(1/3))*Q₂=D := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q₂, Q, D, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne] <;> nlinarith

private theorem branch_right :
    Q₂*translation (-(1/3))*translation (-(1/3))*Q₂=E := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q₂, Q, E, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne] <;> nlinarith

private theorem cancellation_matrix :
    H=(-1 : GL (Fin 2) ℝ)*(Q₂*SpecialLinearGroup.mapGL ℝ (T⁻¹)*Q₂*
      SpecialLinearGroup.mapGL ℝ (T⁻¹)) := by
  have ht : (T:SL(2,ℤ))⁻¹=⟨!![1,-1;0,1],by decide⟩ := by decide
  rw [ht]
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q₂, Q, H, matrix, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne] <;> nlinarith

/-- The square-ramified prime 3 supplies the two-translate relation. -/
theorem original_pair {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 18 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(1/3)))+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/3))=
      -SmallLevelOriginal.fourierFunction k f := by
  funext z
  have h := SmallLevelThirtySix.square_prime_average_zero hf.toEulerData
    (p:=3) (by decide) (by decide) k (z:=(z:ℂ)-(1:ℂ)/3) (by simpa using z.im_pos)
  norm_num [QuantitativeArithmeticRetainedReconstruction.completeTwist,
    Finset.sum_range_succ] at h
  have hq : (z:ℂ)-(1:ℂ)/3+2/3=(z:ℂ)+1/3 := by ring
  rw [hq] at h
  simp only [Pi.add_apply, Pi.neg_apply, translation_slash, SmallLevelOriginal.fourierFunction,
    translation_point, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, ← sub_eq_add_neg]
  linear_combination h

/-- Finite group-algebra cancellation at level 18. The ramified-2 sign
is unrestricted. The central matrix is harmless at even weight. -/
theorem C_invariant (m : ℕ) (F : ℍ → ℂ) (δ : ℂ)
    (hδ : δ=1 ∨ δ= -1)
    (hQ : F ∣[((2*m:ℕ):ℤ)] Q₂=δ • F)
    (hT : F ∣[((2*m:ℕ):ℤ)] T=F)
    (hp : (F ∣[((2*m:ℕ):ℤ)] translation (-(1/3)))+
      (F ∣[((2*m:ℕ):ℤ)] translation (1/3))= -F) :
    F ∣[((2*m:ℕ):ℤ)] C=F := by
  let k : ℤ := ((2*m:ℕ):ℤ)
  change F ∣[k] T=F at hT
  change F ∣[k] Q₂=δ • F at hQ
  change (F ∣[k] translation (-(1/3)))+(F ∣[k] translation (1/3))= -F at hp
  have hTi : F ∣[k] (T:SL(2,ℤ))⁻¹=F := by
    have h := congrArg (fun G : ℍ → ℂ => G ∣[k] (T:SL(2,ℤ))⁻¹) hT
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using h.symm
  have hsq : F ∣[k] (Q₂*Q₂)=F := eigen_square 18 10 (by decide) F k δ hδ hQ
  have hED : F ∣[k] E=F ∣[k] D := by
    have he : E=H*D := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [E,H,D,matrix,GeneralLinearGroup.mkOfDetNeZero,
          Matrix.mul_apply,Fin.sum_univ_two]
    rw [he,cancellation_matrix, SlashAction.slash_mul, SlashAction.slash_mul,
      central_even, SlashAction.slash_mul, SlashAction.slash_mul,
      SlashAction.slash_mul, hQ]
    change ((((δ • F) ∣[k] (T:SL(2,ℤ))⁻¹) ∣[k] Q₂) ∣[k] (T:SL(2,ℤ))⁻¹) ∣[k] D=_
    rw [ModularForm.SL_smul_slash, hTi, Q_smul, hQ, smul_smul]
    rcases hδ with rfl|rfl <;> simp only [one_mul, neg_mul_neg, one_smul, hTi]
  have hc : ((F ∣[k] translation (-(1/3)))+(F ∣[k] translation (1/3))) ∣[k] Q₂=
      ((F ∣[k] Q₂) ∣[k] translation (-(1/3)))+
      ((F ∣[k] Q₂) ∣[k] translation (1/3)) := by
    rw [hp, hQ, det_one_smul _ (translation_det _),
      det_one_smul _ (translation_det _), ← smul_add, hp]
    rw [show -F=(-1:ℂ) • F by simp, Q_smul, hQ]
    simp [smul_smul, mul_comm]
  have hh := congrArg (fun G : ℍ → ℂ => G ∣[k] (translation (-(1/3))*Q₂)) hc
  simp only [SlashAction.add_slash, ← SlashAction.slash_mul] at hh
  rw [← mul_assoc, branch_left, ← mul_assoc, branch_other] at hh
  have ht : translation (1/3)*translation (-(1/3))=1 := by
    rw [translation_mul]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]
  have hr : Q₂*translation (1/3)*(translation (-(1/3))*Q₂)=Q₂*Q₂ := by
    rw [← mul_assoc, mul_assoc Q₂, ht, mul_one]
  rw [show Q₂*translation (-(1/3))*(translation (-(1/3))*Q₂)=E by
    rw [← mul_assoc,branch_right], hr, hsq, hED] at hh
  exact add_right_cancel (hh.trans (add_comm _ _))

theorem original_C (m : ℕ) {f : ℕ → ℂ} (hf : IsSolution 18 (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] C=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨δ,hδ,hQ⟩ := original_eigen (by decide : 0<18)
    (by decide : 2*10=18+2) (by decide) hf
  exact C_invariant m _ δ hδ hQ (SmallLevelGenerators.original_T _ _) (original_pair hf)

#print axioms original_pair
#print axioms C_invariant
#print axioms original_C

end QuantitativeArithmeticSmallLevelEighteen
