module

public import QuantitativeMaassCompressedGramEnergyV1
public import QuantitativeMaassNewtonEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open QuantitativeHolomorphic

namespace QuantitativeMaass

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Fintype ι]

def compressedNewtonPolynomial (G P : E →L[ℂ] E) (n : ℕ) : E →L[ℂ] E :=
  P*Polynomial.aeval (extendedCompressedGram G P) (inverseSqrtPolynomial n)

/-- The finite normalization can be formed after replacing the exact
projection. Its squared error has an explicit cost independent of band dimension. -/
theorem compressedNewtonPolynomial_energy (b : OrthonormalBasis ι ℂ E)
    (G P Q : E →L[ℂ] E) (hG : ‖G‖≤1) (hP : ‖P‖≤1) (hQ : ‖Q‖≤1) (n : ℕ) :
    finiteBandEnergy b (compressedNewtonPolynomial G Q n-compressedNewtonPolynomial G P n) ≤
      2*((6:ℝ)^(2*(4^n))+10*((3^n:ℕ):ℝ)*(9:ℝ)^(2*(4^n)))*finiteBandEnergy b (Q-P) := by
  let A := Polynomial.aeval (extendedCompressedGram G Q) (inverseSqrtPolynomial n)
  let B := Polynomial.aeval (extendedCompressedGram G P) (inverseSqrtPolynomial n)
  have hn : ‖A‖≤(6:ℝ)^(4^n) := by
    exact (polynomial_aeval_norm_le _ _ (extendedCompressedGram_norm G Q hG hQ)).trans
      (by simpa only [show (3:ℝ)+3=6 by norm_num] using polynomialMass_inverseSqrt_le (by norm_num : (0:ℝ)≤3) n)
  have hn2 : ‖A‖^2≤(6:ℝ)^(2*(4^n)) := by
    simpa only [←pow_mul,Nat.mul_comm (4^n) 2] using
      pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hpoly := finiteBandEnergy_newton_difference b (extendedCompressedGram G Q)
    (extendedCompressedGram G P) (by norm_num : (1:ℝ)≤3)
    (extendedCompressedGram_norm G Q hG hQ) (extendedCompressedGram_norm G P hG hP) n
  have hd : finiteBandEnergy b (A-B) ≤
      ((3^n:ℕ):ℝ)*(9:ℝ)^(2*(4^n))*(10*finiteBandEnergy b (Q-P)) := by
    apply hpoly.trans
    norm_num only [show (3:ℝ)+2*3=9 by norm_num]
    exact mul_le_mul_of_nonneg_left (extendedCompressedGram_energy b G P Q hG hP hQ)
      (by positivity)
  have hp2 : ‖P‖^2≤1 := by nlinarith [norm_nonneg P]
  have hl := (finiteBandEnergy_right b (Q-P) A).trans
    (mul_le_mul_of_nonneg_right hn2 (finiteBandEnergy_nonneg b _))
  have hr := (finiteBandEnergy_left b P (A-B)).trans
    (mul_le_mul_of_nonneg_right hp2 (finiteBandEnergy_nonneg b _))
  simp only [one_mul] at hr
  have hid : compressedNewtonPolynomial G Q n-compressedNewtonPolynomial G P n=
      (Q-P)*A+P*(A-B) := by
    change Q*A-P*B=(Q-P)*A+P*(A-B)
    noncomm_ring
  rw [hid]
  apply (finiteBandEnergy_add b _ _).trans
  have hh := add_le_add (mul_le_mul_of_nonneg_left hl (by norm_num : (0:ℝ)≤2))
    (mul_le_mul_of_nonneg_left (hr.trans hd) (by norm_num : (0:ℝ)≤2))
  exact hh.trans_eq (by ring)

#print axioms compressedNewtonPolynomial_energy

end QuantitativeMaass
