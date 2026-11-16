module

public import QuantitativeMaassEnergyTraceLimitV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass

/-- A weighted squared-energy majorant yields a nonnegative weighted
trace majorant, allowing the extra inverse shrinking-window factor. -/
theorem weighted_trace_majorant (ε M : ℝ → ℝ) (C W : ℝ) (hC : 0≤C)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hM : Tendsto (fun t => Real.exp ((2*W+1)*fourthRootScale t)*M t/(t*ε t))
      atTop (𝓝 0)) :
    Tendsto (fun t => Real.exp (W*fourthRootScale t)*Real.sqrt (C*t*|M t|)/(t*ε t))
      atTop (𝓝 0) := by
  let E := fun t => Real.exp (2*W*fourthRootScale t)*|M t|
  have hE : Tendsto (fun t => Real.exp (fourthRootScale t)*E t/(t*ε t))
      atTop (𝓝 0) := by
    have hh := hM.abs
    simp only [abs_zero] at hh
    apply hh.congr'
    filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    dsimp only [E]
    rw [abs_div,abs_mul,abs_of_pos (Real.exp_pos _),abs_mul,
      abs_of_pos ht,abs_of_pos he,←mul_assoc,←Real.exp_add]
    rw [show fourthRootScale t+2*W*fourthRootScale t=(2*W+1)*fourthRootScale t by ring]
  apply weighted_energy_trace_limit ε E
    (fun t => Real.exp (W*fourthRootScale t)*Real.sqrt (C*t*|M t|)) C hε hproduct hE
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  dsimp only [E]
  rw [mul_pow,Real.sq_sqrt (by positivity),←Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  have hh : (2:ℝ)*(W*fourthRootScale t)=2*W*fourthRootScale t := by ring
  rw [hh]
  exact le_of_eq (by ring)

#print axioms weighted_trace_majorant

end QuantitativeMaass
