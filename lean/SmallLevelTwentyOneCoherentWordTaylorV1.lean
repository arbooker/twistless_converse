module

public import SmallLevelTwentyOneCoherentWordsV1
public import QuantitativeArithmeticTwoSequenceTaylorTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace SmallLevelTwentyOneKnownWords
open Matrix UpperHalfPlane SmallLevelNormalized Complex Set
open FinitenessOriginalFourier FinitenessFourierConstruction SmallLevelAdditive
open QuantitativeArithmeticTwoSequenceTaylor
open scoped MatrixGroups ModularForm

/-- Actual all-order Fourier/Taylor laws for every word used in the complete
row construction. The hypotheses on C and the source only exclude an affine
row or a source sent to infinity, which are treated separately. -/
theorem word_taylor_of_law {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε) :
    ∀ w : Word, coordC w≠0 →
      ∀ j : ℝ, coordC w*j+coordD w≠0 →
      ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
        AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, bound<s.re →
          transform (fullCoefficients f (2*m)) j s-
            character (ε*Complex.I^(2*m)) w*(((coordC w*j+coordD w)^2:ℝ):ℂ)^(s-(m:ℂ))*
              (∑ n∈Finset.range M, (Complex.I*((coordC w*(coordC w*j+coordD w):ℝ):ℂ))^n*
                Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
                transform (fullCoefficients f (2*m))
                  ((coordA w*j+coordB w)/(coordC w*j+coordD w)) (s+(n:ℂ)))=
            error M s := by
  obtain ⟨hχ,hfricke⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law
    (by decide : 0<21) m ε hε hlaw
  have hwords := words_of_fricke hf (ε*Complex.I^(2*m)) hχ hfricke
  intro w hC j hj
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hF := word_fourier_of_slash m f (ε*Complex.I^(2*m)) hχ w (hwords w)
  have hh := matrix_even_rows (polynomial_bound hf.zero hg (2*m))
    (fullCoefficients_zero hf.zero (2*m)) m
    (coordA w) (coordB w) (coordC w) (coordD w) j hC
    (by rw [coordinate_det]; norm_num) hj (character (ε*Complex.I^(2*m)) w) (by
      simpa only [coordinate_det,Complex.ofReal_one,one_pow,mul_one] using hF)
  simpa only [coordinate_det,div_one] using hh

#print axioms word_taylor_of_law
end SmallLevelTwentyOneKnownWords
