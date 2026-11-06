module

public import QuantitativeEulerEndpointBaselineEnvelopeV1
public import QuantitativeEulerEndpointInitialCapGrowthV1
public import QuantitativeEulerEndpointPreparedGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared

 theorem observation_transport_power {V O K Δ : ℝ} (t : ℕ)
    (hV : 1≤V) (hO : O≤V^(7+72*t)) (hK0 : 0≤K) (hK : K≤V)
    (hΔ0 : 0≤Δ) (hΔ : Δ≤V^26) : O*(K*(Δ^t)^2)≤V^(8+124*t) := by
  have hV0 : 0≤V := by linarith
  calc
    _ ≤ V^(7+72*t)*(V*((V^26)^t)^2) := mul_le_mul hO
      (mul_le_mul hK (pow_le_pow_left₀ (pow_nonneg hΔ0 t) (pow_le_pow_left₀ hΔ0 hΔ t) 2)
        (by positivity) hV0) (by positivity) (by positivity)
    _ = _ := by simp only [←pow_mul]; rw [←pow_succ',←pow_add]; congr 1; omega

theorem inverse_budget_power {V A : ℝ} (r : ℕ) (hV : 1≤V) (hA : A≤V^r) :
    ((2*(1+2*A))⁻¹)⁻¹≤6*V^r := by
  rw [inv_inv]
  have hh : 1≤V^r := one_le_pow₀ hV
  linarith

/-- The simultaneous initializer cap, with the actual inverse budgets,
including the n observation detectors. Geometry gives detector exponent
360+360t and inverse-budget exponent8+124t. -/
theorem initial_geometry_cap (n : ℕ) (V : ℝ) (t : ℕ)
    (detector cost : Fin n → ℝ) (hV : 1≤V) (hn : (n:ℝ)≤V)
    (hd0 : ∀ i, 0≤detector i)
    (hd : ∀ i, detector i≤(36*9^t)*V^(360+360*t))
    (hc0 : ∀ i, 0≤cost i) (hc : ∀ i, cost i≤V^(8+124*t)) :
    QuantitativeEulerEndpointInitialWeighted.cap detector (fun i => (2*(1+2*cost i))⁻¹)≤
      (1+6*(36*9^t)^2)*V^(729+844*t) := by
  have h := QuantitativeEulerEndpointInitialWeighted.cap_polynomial_bound
    detector (fun i => (2*(1+2*cost i))⁻¹) V 6 (36*9^t) (360+360*t) (8+124*t)
    hV (by norm_num) (by positivity) (by simpa using hn) hd0 hd
    (fun i => by rw [inv_inv]; have hh := hc0 i; positivity) (fun i => inverse_budget_power _ hV (hc i))
  convert h using 1
  congr 2
  omega

#print axioms observation_transport_power
#print axioms initial_geometry_cap
end QuantitativeEulerEndpointPrepared
