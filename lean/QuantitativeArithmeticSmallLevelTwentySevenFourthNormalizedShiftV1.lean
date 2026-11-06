module
public import QuantitativeArithmeticSmallLevelTwentySevenFourthNormalizedCoefficientV1
public import QuantitativeArithmeticSmallLevelTwentySevenFourthNormalizedSourceModelV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
open QuantitativeArithmeticTaylorLayerNormalization
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages (primeRate)
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)

theorem matrix_shift_normalized (r : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec) (m i n : ℕ) (s : ℂ) (v : ℕ → ℂ)
    (h : scale (s-((2*m:ℕ):ℂ)) (i+(n+1))≠0) :
    QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.shift point r m n (s-((i+(n+1):ℕ):ℂ))
      (fun j => scale (s-((2*m:ℕ):ℂ)) i*v j)/scale (s-((2*m:ℕ):ℂ)) (i+(n+1))=
      matrixHigher r (primeRate 2 m (s-((i+(n+1):ℕ):ℂ)))
        (primeRate 3 m (s-((i+(n+1):ℕ):ℂ)))
        (primeRate 5 m (s-((i+(n+1):ℕ):ℂ)))
        (primeRate 7 m (s-((i+(n+1):ℕ):ℂ))) (n+1) v := by
  change (matrixCoefficient r m n (s-((i+(n+1):ℕ):ℂ))*(scale (s-((2*m:ℕ):ℂ)) i*v r.right))/
      scale (s-((2*m:ℕ):ℂ)) (i+(n+1))=_
  rw [show (matrixCoefficient r m n (s-((i+(n+1):ℕ):ℂ))*(scale (s-((2*m:ℕ):ℂ)) i*v r.right))/
      scale (s-((2*m:ℕ):ℂ)) (i+(n+1))=
      (matrixCoefficient r m n (s-((i+(n+1):ℕ):ℂ))*scale (s-((2*m:ℕ):ℂ)) i/
        scale (s-((2*m:ℕ):ℂ)) (i+(n+1)))*v r.right by ring]
  rw [matrix_coefficient_normalized r m i n s h]
  rfl

theorem sampleEval_scalar (q : ℕ) (a : ℕ → ℕ) (c : ℂ) (v : ℕ → ℂ) :
    QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval q a (fun j => c*v j)=c*QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval q a v := by
  simp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,Finset.mul_sum]

theorem ramanujan_shift_normalized (r : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec) (hr : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point r)
    (m i n : ℕ) (ε : ℚ) (s : ℂ) (v : ℕ → ℂ)
    (h : scale (s-((2*m:ℕ):ℂ)) (i+(n+1))≠0) :
    QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.shift r m (ε:ℂ) n (s-((i+(n+1):ℕ):ℂ))
      (fun j => scale (s-((2*m:ℕ):ℂ)) i*v j)/scale (s-((2*m:ℕ):ℂ)) (i+(n+1))=
      ramanujanHigher r ε (primeRate 2 m (s-((i+(n+1):ℕ):ℂ)))
        (primeRate 3 m (s-((i+(n+1):ℕ):ℂ)))
        (primeRate 5 m (s-((i+(n+1):ℕ):ℂ)))
        (primeRate 7 m (s-((i+(n+1):ℕ):ℂ))) (n+1) v := by
  unfold QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.shift
  rw [sampleEval_scalar]
  change (ramanujanCoefficient r m (ε:ℂ) n (s-((i+(n+1):ℕ):ℂ))*
      (scale (s-((2*m:ℕ):ℂ)) i*QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval r.q r.right v))/
        scale (s-((2*m:ℕ):ℂ)) (i+(n+1))=_
  rw [show (ramanujanCoefficient r m (ε:ℂ) n (s-((i+(n+1):ℕ):ℂ))*
      (scale (s-((2*m:ℕ):ℂ)) i*QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval r.q r.right v))/
        scale (s-((2*m:ℕ):ℂ)) (i+(n+1))=
      (ramanujanCoefficient r m (ε:ℂ) n (s-((i+(n+1):ℕ):ℂ))*scale (s-((2*m:ℕ):ℂ)) i/
        scale (s-((2*m:ℕ):ℂ)) (i+(n+1)))*QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval r.q r.right v by ring]
  rw [ramanujan_coefficient_normalized r m i n (ε:ℂ) s h]
  have ht := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.taylor_zero_physical (Nat.lcm 27 (r.q^2)) m ((r.t:ℚ)/r.Q)
    r.e₂ r.e₃ r.e₅ r.e₇ hr.2.2.2.2.2.1 (ε:ℂ) (s-((i+(n+1):ℕ):ℂ))
  simp only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] at ht
  rw [ht]
  unfold ramanujanHigher
  push_cast
  ring

#print axioms matrix_shift_normalized
#print axioms ramanujan_shift_normalized
end QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
