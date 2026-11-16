module

public import AsymptoticFrickeNormalizerV1
public import QuantitativeArithmeticTwoInvolutionPolynomialV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticRationalGroup AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticReconstructionBranch AsymptoticIntegralSubgroup AsymptoticFreshMatrices
open scoped MatrixGroups

namespace QuantitativeArithmeticRepeatedTwoMatrices

theorem lower_square (L : ℕ) :
    (integralLabel (lowerSL (2*L) 1))^2 ∈ gamma (2*(2*L)) := by
  have he : lowerSL (2*L) 1 * lowerSL (2*L) 1 = lowerSL (2*(2*L)) 1 := by
    rw [lowerSL_mul]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerSL, AsymptoticFreshCRT.lower]
    ring
  rw [pow_two, ← map_mul, he]
  exact ⟨_, lowerSL_mem _ _, rfl⟩

def evenMatrix (t : ℤ) : SL(2,ℤ) :=
  ⟨!![1-2*t, t-1; 8*t*(1-t), 4*t^2-6*t+1], by
    simp [Matrix.det_fin_two]; ring⟩

def oddMatrix (t : ℤ) : SL(2,ℤ) :=
  ⟨!![4*t^2-2*t-1, -2*t^2+2*t;
      8*t*(t-1)*(2*t+1), -8*t^3+8*t^2+2*t-1], by
    simp [Matrix.det_fin_two]; ring⟩

/-- For an even remaining level the product of the two half-trace
reflections has order dividing two modulo the original congruence group. -/
theorem even_word (t : ℕ) :
    (integralLabel (lowerSL (2*(2*t)) 1) * translationLabel (-1/2))^2 ∈
      gamma (2*(2*(2*t))) := by
  have he : (rationalGL (lowerSL (2*(2*t)) 1) *
      AsymptoticMobiusFold.translation (-1/2))^2 = rationalGL (evenMatrix t) := by
    apply Units.ext
    change ((lowerSL (2*(2*t)) 1).val.map (fun x : ℤ => (x:ℚ)) *
      (AsymptoticMobiusFold.translation (-1/2)).val)^2 =
      (evenMatrix t).val.map (fun x : ℤ => (x:ℚ))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, lowerSL, AsymptoticFreshCRT.lower,
        AsymptoticMobiusFold.translation, GeneralLinearGroup.mkOfDetNeZero,
        evenMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  refine ⟨evenMatrix t, ?_, ?_⟩
  · change evenMatrix t ∈ CongruenceSubgroup.Gamma0 (2*(2*(2*t)))
    rw [gamma0_mem_dvd]
    change (2*(2*(2*(t:ℤ)))) ∣ 8*(t:ℤ)*(1-t)
    exact ⟨1-t, by ring⟩
  · apply Subtype.ext
    apply Subtype.ext
    change rationalMap (rationalGL (evenMatrix t)) =
      (rationalMap (rationalGL (lowerSL (2*(2*t)) 1)) *
        rationalMap (AsymptoticMobiusFold.translation (-1/2)))^2
    rw [← map_mul, ← map_pow, he]

/-- For an odd remaining level the corresponding product has order
dividing three. The witness is integral and has the required lower entry. -/
theorem odd_word (t : ℕ) :
    (integralLabel (lowerSL (2*(2*t+1)) 1) * translationLabel (-1/2))^3 ∈
      gamma (2*(2*(2*t+1))) := by
  have he : (rationalGL (lowerSL (2*(2*t+1)) 1) *
      AsymptoticMobiusFold.translation (-1/2))^3 = rationalGL (oddMatrix t) := by
    apply Units.ext
    change ((lowerSL (2*(2*t+1)) 1).val.map (fun x : ℤ => (x:ℚ)) *
      (AsymptoticMobiusFold.translation (-1/2)).val)^3 =
      (oddMatrix t).val.map (fun x : ℤ => (x:ℚ))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, lowerSL, AsymptoticFreshCRT.lower,
        AsymptoticMobiusFold.translation, GeneralLinearGroup.mkOfDetNeZero,
        oddMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  refine ⟨oddMatrix t, ?_, ?_⟩
  · change oddMatrix t ∈ CongruenceSubgroup.Gamma0 (2*(2*(2*t+1)))
    rw [gamma0_mem_dvd]
    change (2*(2*(2*(t:ℤ)+1))) ∣ 8*(t:ℤ)*(t-1)*(2*t+1)
    exact ⟨2*t*(t-1), by ring⟩
  · apply Subtype.ext
    apply Subtype.ext
    change rationalMap (rationalGL (oddMatrix t)) =
      (rationalMap (rationalGL (lowerSL (2*(2*t+1)) 1)) *
        rationalMap (AsymptoticMobiusFold.translation (-1/2)))^3
    rw [← map_mul, ← map_pow, he]

/-- Global Fricke exchanges the two repeated-prime reflections. -/
theorem fricke_half (L : ℕ) (hL : 0 < L) :
    frickeLabel (2*(2*L)) (by omega) * integralLabel (lowerSL (2*L) 1) =
      translationLabel (-1/2) * frickeLabel (2*(2*L)) (by omega) := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (branch ((2*(2*L):ℕ):ℚ) 0 0 _) *
      rationalMap (rationalGL (lowerSL (2*L) 1)) =
    rationalMap (AsymptoticMobiusFold.translation (-1/2)) *
      rationalMap (branch ((2*(2*L):ℕ):ℚ) 0 0 _)
  rw [← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  change (branch ((2*(2*L):ℕ):ℚ) 0 0 _).val *
    (lowerSL (2*L) 1).val.map (fun x : ℤ => (x:ℚ)) =
    (AsymptoticMobiusFold.translation (-1/2)).val * (branch ((2*(2*L):ℕ):ℚ) 0 0 _).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [branch, lowerSL, AsymptoticFreshCRT.lower,
      AsymptoticMobiusFold.translation, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two]
  ring

#print axioms even_word
#print axioms odd_word
#print axioms fricke_half
#print axioms lower_square

end QuantitativeArithmeticRepeatedTwoMatrices
