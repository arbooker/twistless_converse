module
public import SmallLevelNormalizedFrickeV1
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticQuadraticFive
open Complex FinitenessOriginalFourier FinitenessFourierConstruction FinitenessAnalyticReconstruction

/-- The four additive translates underlying the quadratic-five twist.
This level-independent interface avoids importing an entire level-specific
pole-exclusion proof merely to use the elementary Fourier identity. -/
def quadraticFourier (k : ℕ) (f : ℕ → ℂ) (z : ℂ) : ℂ :=
  fourier (fullCoefficients f k) (z+(1/5:ℝ))+
  fourier (fullCoefficients f k) (z+(-1/5:ℝ))-
  fourier (fullCoefficients f k) (z+(2/5:ℝ))-
  fourier (fullCoefficients f k) (z+(-2/5:ℝ))

theorem twist_five (F : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z) (z : ℂ) :
    twist F 5 z=F (z+1/5)+F (z-1/5)+F (z+2/5)+F (z-2/5) := by
  unfold twist
  rw [show (Finset.range 5).filter (fun a => Nat.Coprime a 5)={1,2,3,4} by decide]
  norm_num
  rw [show z+3/5=(z-2/5)+1 by ring,show z+4/5=(z-1/5)+1 by ring,hp,hp]
  ring

#print axioms twist_five
end QuantitativeArithmeticQuadraticFive
