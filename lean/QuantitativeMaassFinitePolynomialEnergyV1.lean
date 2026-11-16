module

public import QuantitativeMaassFiniteEnergyPerturbationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open scoped BigOperators

namespace QuantitativeMaass

variable {E ι J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Fintype ι]

omit [CompleteSpace E] in
theorem finiteBandEnergy_sum (b : OrthonormalBasis ι ℂ E)
    (s : Finset J) (A : J → E →L[ℂ] E) :
    finiteBandEnergy b (∑ j ∈ s,A j) ≤ (s.card:ℝ)*∑ j ∈ s,finiteBandEnergy b (A j) := by
  classical
  have hpoint (i : ι) : ‖∑ j ∈ s,A j (b i)‖^2 ≤
      (s.card:ℝ)*∑ j ∈ s,‖A j (b i)‖^2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _)
      (norm_sum_le s (fun j => A j (b i))) 2
    have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ))
      (fun j => ‖A j (b i)‖)
    exact hh.trans (by simpa using hc)
  calc
    _ = ∑ i,‖∑ j ∈ s,A j (b i)‖^2 := by
      simp [finiteBandEnergy]
    _ ≤ ∑ i,(s.card:ℝ)*∑ j ∈ s,‖A j (b i)‖^2 :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = _ := by
      simp only [finiteBandEnergy, Finset.mul_sum]
      rw [Finset.sum_comm]

omit [CompleteSpace E] in
theorem finiteBandEnergy_real_smul (b : OrthonormalBasis ι ℂ E)
    (A : E →L[ℂ] E) (c : ℝ) :
    finiteBandEnergy b (c • A)=c^2*finiteBandEnergy b A := by
  simp [finiteBandEnergy, norm_smul, Real.norm_eq_abs, mul_pow, Finset.mul_sum]

/-- A finite polynomial transports squared error without a factor depending
on the dimension of the band. Coefficients and degrees are explicit. -/
theorem finiteBandEnergy_polynomial_difference (b : OrthonormalBasis ι ℂ E)
    (A B : E →L[ℂ] E) {D : ℝ} (hD : 1≤D) (hA : ‖A‖≤D) (hB : ‖B‖≤D)
    (s : Finset ℕ) (c : ℕ → ℝ) :
    finiteBandEnergy b ((∑ j ∈ s,c j • A^j)-(∑ j ∈ s,c j • B^j)) ≤
      ((s.card:ℝ)*∑ j ∈ s,(c j)^2*(4*D^2)^j)*finiteBandEnergy b (A-B) := by
  classical
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  apply (finiteBandEnergy_sum b s (fun j => c j • (A^j-B^j))).trans
  calc
    _ = (s.card:ℝ)*∑ j ∈ s,(c j)^2*finiteBandEnergy b (A^j-B^j) := by
      simp_rw [finiteBandEnergy_real_smul]
    _ ≤ (s.card:ℝ)*∑ j ∈ s,(c j)^2*((4*D^2)^j*finiteBandEnergy b (A-B)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (finiteBandEnergy_power_difference b A B hD hA hB j) (sq_nonneg _)
    _ = _ := by simp only [Finset.sum_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

#print axioms finiteBandEnergy_sum
#print axioms finiteBandEnergy_real_smul
#print axioms finiteBandEnergy_polynomial_difference

end QuantitativeMaass
