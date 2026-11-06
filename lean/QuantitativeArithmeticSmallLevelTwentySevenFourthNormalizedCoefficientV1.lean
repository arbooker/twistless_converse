module
public import QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamilyModelV1
public import QuantitativeArithmeticTaylorLayerNormalizationTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
open QuantitativeArithmeticTaylorLayerNormalization
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages (primeRate)
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)

theorem matrix_coefficient_normalized
    (r : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec)
    (m i n : ℕ) (s : ℂ) (h : scale (s-((2*m:ℕ):ℂ)) (i+(n+1))≠0) :
    matrixCoefficient r m n (s-((i+(n+1):ℕ):ℂ))*scale (s-((2*m:ℕ):ℂ)) i/
        scale (s-((2*m:ℕ):ℂ)) (i+(n+1))=
      (primeRate 2 m (s-((i+(n+1):ℕ):ℂ))^r.e₂*
        primeRate 3 m (s-((i+(n+1):ℕ):ℂ))^r.e₃*
        primeRate 5 m (s-((i+(n+1):ℕ):ℂ))^r.e₅*
        primeRate 7 m (s-((i+(n+1):ℕ):ℂ))^r.e₇)*
      ((QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry r.word 1 0:ℂ)*
        (QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.denominator point r:ℂ))^(n+1)/
          ((n+1).factorial:ℂ) := by
  unfold matrixCoefficient
  rw [show s-((i+(n+1):ℕ):ℂ)+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)=
    (s-((2*m:ℕ):ℂ))-(i:ℂ) by push_cast; ring]
  have hh := normalized_phase_coefficient (s-((2*m:ℕ):ℂ))
    ((QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry r.word 1 0:ℂ)*
      (QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.denominator point r:ℂ)) i (n+1) h
  calc
    _=(primeRate 2 m (s-((i+(n+1):ℕ):ℂ))^r.e₂*
        primeRate 3 m (s-((i+(n+1):ℕ):ℂ))^r.e₃*
        primeRate 5 m (s-((i+(n+1):ℕ):ℂ))^r.e₅*
        primeRate 7 m (s-((i+(n+1):ℕ):ℂ))^r.e₇)*
      (((Complex.I*((QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry r.word 1 0:ℂ)*
        (QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.denominator point r:ℂ)))^(n+1)*
        Ring.choose ((s-((2*m:ℕ):ℂ))-(i:ℂ)) (n+1)*scale (s-((2*m:ℕ):ℂ)) i)/
          scale (s-((2*m:ℕ):ℂ)) (i+(n+1))) := by ring
    _=_ := by rw [hh]; ring

theorem ramanujan_coefficient_normalized
    (r : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec)
    (m i n : ℕ) (η s : ℂ) (h : scale (s-((2*m:ℕ):ℂ)) (i+(n+1))≠0) :
    ramanujanCoefficient r m η n (s-((i+(n+1):ℕ):ℂ))*scale (s-((2*m:ℕ):ℂ)) i/
        scale (s-((2*m:ℕ):ℂ)) (i+(n+1))=
      SmallLevelTaylor.taylorRowScalar (2*m) (Nat.lcm 27 (r.q^2)) ((r.t:ℝ)/r.Q) η 0
        (s-((i+(n+1):ℕ):ℂ))*
      ((Nat.lcm 27 (r.q^2):ℂ)*(((r.t:ℝ)/r.Q:ℝ):ℂ))^(n+1)/((n+1).factorial:ℂ) := by
  exact normalized_taylor_coefficient (2*m) i (n+1)
    (Nat.lcm 27 (r.q^2)) ((r.t:ℝ)/r.Q) η s h

#print axioms matrix_coefficient_normalized
#print axioms ramanujan_coefficient_normalized
end QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
