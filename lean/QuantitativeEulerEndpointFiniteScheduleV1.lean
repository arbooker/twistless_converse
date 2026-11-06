module

public import QuantitativeEulerEndpointBlockScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBlocks
open Finset

/-- The finite-horizon endpoint needs only the actual constructed steps;
no extension by fictitious operator updates is required. -/
theorem finite_schedule_endpoint (n : ℕ) (e bad : ℕ → ℝ)
    {A B C : ℝ} (hA : 0≤A) (hB : 0≤B)
    (he : ∀ j, j≤n → 0≤e j) (hbad : ∀ j, 0≤bad j)
    (hbudget : (∑ j∈range n, bad j)≤C)
    (hstep : ∀ j, j<n → e (j+1)≤
      (Real.exp (bad j)/4+A*blockRelativeLoss n j)*e j+B*blockAdditiveLoss n j) :
    e n≤Real.exp (C+4*A)*(e 0+4*B)/(4:ℝ)^n := by
  classical
  let f : ℕ → ℝ := fun j => if j≤n then e j else 0
  have hf (j : ℕ) : 0≤f j := by
    dsimp only [f]
    split_ifs with hj
    · exact he j hj
    · rfl
  have hrec (j : ℕ) : f (j+1)≤
      (Real.exp (bad j)/4+A*blockRelativeLoss n j)*f j+B*blockAdditiveLoss n j := by
    by_cases hj : j<n
    · simpa only [f,ite_eq_left (show j+1≤n by omega),ite_eq_left (show j≤n by omega)] using hstep j hj
    · have hzero : f (j+1)=0 := ite_eq_right (by omega)
      rw [hzero]
      exact add_nonneg (mul_nonneg
        (add_nonneg (by positivity) (mul_nonneg hA (blockRelativeLoss_nonneg n j))) (hf j))
        (mul_nonneg hB (blockAdditiveLoss_nonneg n j))
  simpa only [f,ite_eq_left (le_refl n),ite_eq_left (Nat.zero_le n)] using
    finite_horizon_block_endpoint n f bad hA hB hf hbad hbudget hrec

#print axioms finite_schedule_endpoint
end QuantitativeEulerEndpointBlocks
