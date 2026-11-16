module

public import QuantitativeMaassRectangularEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeMaass

variable {E F H ι κ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Fintype ι] [Fintype κ]

/-- Squared energy on a finite source basis with unrestricted output. -/
def finiteSourceEnergy (b : OrthonormalBasis ι ℂ E) (A : E →L[ℂ] H) : ℝ :=
  ∑ i,‖A (b i)‖^2

theorem finiteSourceEnergy_nonneg (b : OrthonormalBasis ι ℂ E) (A : E →L[ℂ] H) :
    0≤finiteSourceEnergy b A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem finiteSourceEnergy_add (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] H) :
    finiteSourceEnergy b (A+B)≤2*finiteSourceEnergy b A+2*finiteSourceEnergy b B := by
  unfold finiteSourceEnergy
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change ‖A (b i)+B (b i)‖^2≤_
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (A (b i)) (B (b i))) 2
  nlinarith [sq_nonneg (‖A (b i)‖-‖B (b i)‖)]

theorem finiteSourceEnergy_left (b : OrthonormalBasis ι ℂ E)
    (A : F →L[ℂ] H) (B : E →L[ℂ] F) :
    finiteSourceEnergy b (A.comp B)≤‖A‖^2*finiteSourceEnergy b B :=
  rectangular_energy_left b A B

theorem finiteSourceEnergy_right [CompleteSpace E] [CompleteSpace F] [CompleteSpace H]
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ F)
    (A : F →L[ℂ] H) (B : E →L[ℂ] F) :
    finiteSourceEnergy b (A.comp B)≤‖B‖^2*finiteSourceEnergy c A :=
  rectangular_energy_right b c A B

#print axioms finiteSourceEnergy_nonneg
#print axioms finiteSourceEnergy_add
#print axioms finiteSourceEnergy_left
#print axioms finiteSourceEnergy_right

end QuantitativeMaass
