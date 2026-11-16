module

public import QuantitativeMaassFiniteSourceEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeMaass

variable {E H ι J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]

theorem finiteSourceEnergy_sum (b : OrthonormalBasis ι ℂ E)
    (s : Finset J) (A : J → E →L[ℂ] H) :
    finiteSourceEnergy b (∑ j ∈ s,A j) ≤ (s.card:ℝ)*∑ j ∈ s,finiteSourceEnergy b (A j) := by
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
      simp [finiteSourceEnergy]
    _ ≤ ∑ i,(s.card:ℝ)*∑ j ∈ s,‖A j (b i)‖^2 :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = _ := by
      simp only [finiteSourceEnergy, Finset.mul_sum]
      rw [Finset.sum_comm]

theorem finiteSourceEnergy_real_smul (b : OrthonormalBasis ι ℂ E)
    (A : E →L[ℂ] H) (c : ℝ) :
    finiteSourceEnergy b (c • A)=c^2*finiteSourceEnergy b A := by
  simp [finiteSourceEnergy, norm_smul, Real.norm_eq_abs, mul_pow, Finset.mul_sum]

/-- Finite real combinations of maps out of one finite source space have
an explicit coefficient cost. The target space need not be finite. -/
theorem finiteSourceEnergy_combination_difference (b : OrthonormalBasis ι ℂ E)
    (s : Finset J) (c : J → ℝ) (A B : J → E →L[ℂ] H)
    (M : ℝ) (hM : ∀ j∈s,finiteSourceEnergy b (A j-B j)≤M) :
    finiteSourceEnergy b ((∑ j∈s,c j • A j)-(∑ j∈s,c j • B j))≤
      ((s.card:ℝ)*∑ j∈s,(c j)^2)*M := by
  classical
  rw [←Finset.sum_sub_distrib]
  simp_rw [←smul_sub]
  apply (finiteSourceEnergy_sum b s (fun j => c j • (A j-B j))).trans
  simp_rw [finiteSourceEnergy_real_smul]
  calc
    _ ≤ (s.card:ℝ)*∑ j∈s,(c j)^2*M := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hM j hj) (sq_nonneg _))
    _ = _ := by rw [←Finset.sum_mul,mul_assoc]

#print axioms finiteSourceEnergy_sum
#print axioms finiteSourceEnergy_real_smul
#print axioms finiteSourceEnergy_combination_difference

end QuantitativeMaass
