module
public import SmallLevelTwentySixPairMatricesV1
public import SmallLevelSignedPairsV1
public import SmallLevelTwentySixHyperbolicClassificationV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySix
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessNormalizedTwistProduct
open scoped MatrixGroups ModularForm

theorem original_reduced4 {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 k f) :
    (fourierFunction k f ∣[(k:ℤ)] P)+
      ((fourierFunction k f ∣[(k:ℤ)] Q) ∣[(k:ℤ)] translation (-1/2))=
      root 26 f 2 • (fourierFunction k f+
        (fourierFunction k f ∣[(k:ℤ)] translation (-1/2))) := by
  simpa only [show (2:ℝ)*(-(1/4))= -1/2 by ring] using
    SmallLevelSignedPairs.pair_reduction (fourierFunction k f) k
      (fricke 26 (by decide)) (fricke 208 (by decide)) P Q (-(1/4)) (root 26 f 2)
      P_factor4 (by simpa only [neg_neg] using Q_factor4)
      (by simpa only [neg_neg,root4,add_comm] using original_pair4 hf)

theorem original_reduced6 (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P⁻¹)+
      ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Q⁻¹)
        ∣[((2*m:ℕ):ℤ)] translation (-1/3))=
      root 26 f 2 • (fourierFunction (2*m) f+
        (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (-1/3))) := by
  have hh := SmallLevelSignedPairs.pair_reduction (fourierFunction (2*m) f) ((2*m:ℕ):ℤ)
    (fricke 26 (by decide)) (fricke 468 (by decide)) P6 Q6 (-(1/6)) (root 26 f 2)
    P_factor6 (by simpa only [neg_neg] using Q_factor6)
    (by simpa only [neg_neg,add_comm] using original_pair6 hf)
  rw [P6_inverse,Q6_inverse,SlashAction.slash_mul,SlashAction.slash_mul,
    central_even] at hh
  simpa only [show (2:ℝ)*(-(1/6))= -1/3 by ring] using hh

theorem hyperM_factor :
    (translation (-1/2))⁻¹*Q⁻¹*translation (-1/3)*P=(-1 : GL (Fin 2) ℝ)*hyperM := by
  have hr : (translation (-1/2))⁻¹=translation (1/2) := by
    apply inv_eq_of_mul_eq_one_right
    rw [translation_mul]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]
  rw [hr,← Q_inverse]
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hyperM,Qi,P,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne] <;> nlinarith

/-- The first hyperbolic invariance follows from the original Ramanujan
equations, for either sign of the local factor at two. -/
theorem original_hyperM (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P)-root 26 f 2 • fourierFunction (2*m) f)
      ∣[((2*m:ℕ):ℤ)] hyperM=
      (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P)-root 26 f 2 • fourierFunction (2*m) f := by
  have hh := SmallLevelSignedPairs.inverse_pairs (fourierFunction (2*m) f) ((2*m:ℕ):ℤ)
    P Q (translation (-1/2)) (translation (-1/3)) (root 26 f 2)
    (root_unit hf.toEulerData 2) (original_reduced4 hf) (original_reduced6 m hf)
  rw [hyperM_factor,SlashAction.slash_mul,central_even] at hh
  exact hh

#print axioms original_hyperM
end SmallLevelTwentySix
