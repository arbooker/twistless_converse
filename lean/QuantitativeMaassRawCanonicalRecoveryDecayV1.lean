module

public import QuantitativeMaassRawHorizonPowerDecayV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass

/-- Both terms of the constructed regular canonical error tend to zero
with every fixed propagation loss. The square-root source recovery term
is included with its actual rate. -/
theorem raw_canonical_recovery_decay (ε R : ℝ→ℝ) (C D K I : ℝ) (hC : 0≤C) (hK : 0≤K)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hR : Tendsto (fun t => R t/slowScale t) atTop (𝓝 0)) :
    Tendsto (fun t => Real.exp (C*R t)*
      (D/(2:ℝ)^rawBlockHorizon t+4*Real.sqrt (K/(2:ℝ)^rawBlockHorizon t)*I)/ε t)
      atTop (𝓝 0) := by
  have hs : 0<Real.sqrt (1/2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : Real.sqrt (1/2:ℝ)<1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤1/2)]
  have hhalf := (rawBlockHorizon_power_decay ε R (1/2) C (by norm_num) (by norm_num) hC hε hp hR).const_mul D
  have hroot := (rawBlockHorizon_power_decay ε R (Real.sqrt (1/2)) C hs hs1 hC hε hp hR).const_mul
    (4*Real.sqrt K*I)
  have hh := hhalf.add hroot
  simp only [mul_zero,add_zero] at hh
  have hpow (n : ℕ) : Real.sqrt ((1/2:ℝ)^n)=(Real.sqrt (1/2:ℝ))^n := by
    induction n with
    | zero => simp only [pow_zero,Real.sqrt_one]
    | succ n ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg (by norm_num) n),ih,pow_succ]
  have hk (n : ℕ) : Real.sqrt (K/(2:ℝ)^n)=Real.sqrt K*(Real.sqrt (1/2:ℝ))^n := by
    rw [show K/(2:ℝ)^n=K*(1/2:ℝ)^n by rw [div_pow,one_pow]; ring,
      Real.sqrt_mul hK,hpow]
  convert hh using 1
  funext t
  rw [hk,div_pow,one_pow]
  ring

#print axioms raw_canonical_recovery_decay
end QuantitativeMaass
