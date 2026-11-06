module

public import QuantitativeEulerEndpointInitialEffortV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointInitialWeighted

/-- The finite simultaneous initializer has polynomial cap whenever
its original detectors and inverse budgets do. Cardinality is included. -/
theorem cap_polynomial_bound {ι : Type*} [Fintype ι] (C a : ι → ℝ)
    (U A D : ℝ) (r s : ℕ) (hU : 1≤U) (hA : 0≤A) (_hD : 0≤D)
    (hcard : (Fintype.card ι:ℝ)≤U) (hC0 : ∀ i, 0≤C i)
    (hC : ∀ i, C i≤D*U^r) (_ha0 : ∀ i, 0≤(a i)⁻¹)
    (ha : ∀ i, (a i)⁻¹≤A*U^s) :
    cap C a≤(1+A*D^2)*U^(1+s+2*r) := by
  have hU0 : 0≤U := by linarith
  have hterm (i : ι) : (a i)⁻¹*(C i)^2≤A*D^2*U^(s+2*r) := by
    calc
      _ ≤ (A*U^s)*(D*U^r)^2 := mul_le_mul (ha i)
        (pow_le_pow_left₀ (hC0 i) (hC i) 2) (sq_nonneg _) (by positivity)
      _ = _ := by rw [mul_pow,←pow_mul,pow_add]; ring
  have hsum : (∑ i, (a i)⁻¹*(C i)^2)≤A*D^2*U^(1+s+2*r) := by
    calc
      _ ≤ ∑ _i : ι, A*D^2*U^(s+2*r) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (Fintype.card ι:ℝ)*(A*D^2*U^(s+2*r)) := by simp
      _ ≤ U*(A*D^2*U^(s+2*r)) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by simp only [pow_add,pow_one]; ring
  unfold cap
  have hp : 1≤U^(1+s+2*r) := one_le_pow₀ hU
  nlinarith only [hsum,hp]

#print axioms cap_polynomial_bound
end QuantitativeEulerEndpointInitialWeighted
