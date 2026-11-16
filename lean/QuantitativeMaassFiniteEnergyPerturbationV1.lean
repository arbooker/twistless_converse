module

public import QuantitativeMaassHilbertSchmidtIdealV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open scoped BigOperators

namespace QuantitativeMaass

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Fintype ι]

/-- Squared Hilbert--Schmidt error on a finite band. -/
def finiteBandEnergy (b : OrthonormalBasis ι ℂ E) (A : E →L[ℂ] E) : ℝ :=
  ∑ i, ‖A (b i)‖ ^ 2

omit [CompleteSpace E] in
theorem finiteBandEnergy_nonneg (b : OrthonormalBasis ι ℂ E) (A : E →L[ℂ] E) :
    0 ≤ finiteBandEnergy b A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem finiteBandEnergy_left (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    finiteBandEnergy b (A * B) ≤ ‖A‖ ^ 2 * finiteBandEnergy b B := by
  simpa [finiteBandEnergy, hilbertSchmidtEnergy, OrthonormalBasis.coe_toHilbertBasis,
    tsum_fintype] using (left_comp_energy_bound b.toHilbertBasis A B
      (hasSum_fintype _).summable).2

theorem finiteBandEnergy_right (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    finiteBandEnergy b (A * B) ≤ ‖B‖ ^ 2 * finiteBandEnergy b A := by
  simpa [finiteBandEnergy, hilbertSchmidtEnergy, OrthonormalBasis.coe_toHilbertBasis,
    tsum_fintype] using (right_comp_energy_bound b.toHilbertBasis A B
      (hasSum_fintype _).summable).2

omit [CompleteSpace E] in
theorem finiteBandEnergy_add (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    finiteBandEnergy b (A+B) ≤ 2*finiteBandEnergy b A+2*finiteBandEnergy b B := by
  unfold finiteBandEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change ‖A (b i)+B (b i)‖^2 ≤ _
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (A (b i)) (B (b i))) 2
  nlinarith [sq_nonneg (‖A (b i)‖-‖B (b i)‖)]

/-- Polynomial powers preserve a finite-band error with a dimension-free
exponential cost. The operators need not commute. -/
theorem finiteBandEnergy_power_difference (b : OrthonormalBasis ι ℂ E)
    (A B : E →L[ℂ] E) {D : ℝ} (hD : 1 ≤ D) (hA : ‖A‖ ≤ D) (hB : ‖B‖ ≤ D)
    (n : ℕ) :
    finiteBandEnergy b (A^n-B^n) ≤ (4*D^2)^n*finiteBandEnergy b (A-B) := by
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have he := finiteBandEnergy_nonneg b (A-B)
  induction n with
  | zero => simpa [finiteBandEnergy] using he
  | succ n ih =>
    have hid : A^(n+1)-B^(n+1)=(A^n-B^n)*A+B^n*(A-B) := by
      rw [pow_succ, pow_succ]
      noncomm_ring
    have hn : ‖B^n‖ ≤ D^n := by
      cases n with
      | zero =>
        change ‖ContinuousLinearMap.id ℂ E‖ ≤ 1
        exact ContinuousLinearMap.norm_id_le
      | succ k =>
        exact (norm_pow_le' B (Nat.succ_pos k)).trans
          (pow_le_pow_left₀ (norm_nonneg _) hB (k+1))
    have hleft := (finiteBandEnergy_right b (A^n-B^n) A).trans
      (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hA 2) ih
        (finiteBandEnergy_nonneg b _) (sq_nonneg D))
    have hright := (finiteBandEnergy_left b (B^n) (A-B)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2) he)
    have hd : (D^n)^2 ≤ (4*D^2)^n := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg D) (by nlinarith [sq_nonneg D]) n
    have hbase : 1 ≤ D^2 := by nlinarith
    rw [hid]
    calc
      _ ≤ 2*finiteBandEnergy b ((A^n-B^n)*A)+
          2*finiteBandEnergy b (B^n*(A-B)) := finiteBandEnergy_add b _ _
      _ ≤ 2*(D^2*((4*D^2)^n*finiteBandEnergy b (A-B)))+
          2*((D^n)^2*finiteBandEnergy b (A-B)) := by gcongr
      _ ≤ 2*(D^2*((4*D^2)^n*finiteBandEnergy b (A-B)))+
          2*(D^2*((4*D^2)^n*finiteBandEnergy b (A-B))) := by
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (hd.trans (le_mul_of_one_le_left (by positivity) hbase)) he
      _ = _ := by rw [pow_succ]; ring

#print axioms finiteBandEnergy_nonneg
#print axioms finiteBandEnergy_left
#print axioms finiteBandEnergy_right
#print axioms finiteBandEnergy_add
#print axioms finiteBandEnergy_power_difference

end QuantitativeMaass
