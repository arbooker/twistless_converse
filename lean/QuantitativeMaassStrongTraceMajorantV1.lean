module

public import QuantitativeMaassStrongMomentScheduleV1
public import QuantitativeMaassFiniteEnergyTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass.Strong

theorem weighted_energy_two_widths (ε E : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hE : Tendsto (fun t => Real.exp (strongScale t)*E t/(t*ε t)) atTop (𝓝 0)) :
    Tendsto (fun t => E t/(t*(ε t)^2)) atTop (𝓝 0) := by
  have hh := hE.mul (strong_exponential_div_width ε hε hproduct)
  simp only [mul_zero] at hh
  convert hh using 1
  funext t
  rw [div_mul_div_comm]
  have hn : Real.exp (strongScale t)*E t*Real.exp (-strongScale t)=E t := by
    calc
      _ = E t*(Real.exp (strongScale t)*Real.exp (-strongScale t)) := by ring
      _ = _ := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  rw [hn]
  congr 1
  ring


theorem weighted_energy_trace_limit (ε E F : ℝ → ℝ) (C : ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hE : Tendsto (fun t => Real.exp (strongScale t)*E t/(t*ε t)) atTop (𝓝 0))
    (hF : ∀ᶠ t in atTop,(F t)^2≤C*t*E t) :
    Tendsto (fun t => F t/(t*ε t)) atTop (𝓝 0) := by
  have hh := (weighted_energy_two_widths ε E hε hproduct hE).const_mul C
  simp only [mul_zero] at hh
  have hs : Tendsto (fun t => (F t/(t*ε t))^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun t => sq_nonneg _)) _ hh
    filter_upwards [hε,hF,eventually_gt_atTop (0:ℝ)] with t he hf ht
    rw [div_pow]
    calc
      _ ≤ C*t*E t/(t*ε t)^2 := div_le_div_of_nonneg_right hf (sq_nonneg _)
      _ = C*(E t/(t*(ε t)^2)) := by
        field_simp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hz := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,Real.sqrt_zero,Real.norm_eq_abs] using hz


theorem weighted_trace_majorant (ε M : ℝ → ℝ) (C W : ℝ) (hC : 0≤C)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hM : Tendsto (fun t => Real.exp ((2*W+1)*strongScale t)*M t/(t*ε t))
      atTop (𝓝 0)) :
    Tendsto (fun t => Real.exp (W*strongScale t)*Real.sqrt (C*t*|M t|)/(t*ε t))
      atTop (𝓝 0) := by
  let E := fun t => Real.exp (2*W*strongScale t)*|M t|
  have hE : Tendsto (fun t => Real.exp (strongScale t)*E t/(t*ε t))
      atTop (𝓝 0) := by
    have hh := hM.abs
    simp only [abs_zero] at hh
    apply hh.congr'
    filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    dsimp only [E]
    rw [abs_div,abs_mul,abs_of_pos (Real.exp_pos _),abs_mul,
      abs_of_pos ht,abs_of_pos he,←mul_assoc,←Real.exp_add]
    rw [show strongScale t+2*W*strongScale t=(2*W+1)*strongScale t by ring]
  apply weighted_energy_trace_limit ε E
    (fun t => Real.exp (W*strongScale t)*Real.sqrt (C*t*|M t|)) C hε hproduct hE
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  dsimp only [E]
  rw [mul_pow,Real.sq_sqrt (by positivity),←Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  have hh : (2:ℝ)*(W*strongScale t)=2*W*strongScale t := by ring
  rw [hh]
  exact le_of_eq (by ring)


#print axioms weighted_energy_two_widths
#print axioms weighted_energy_trace_limit
#print axioms weighted_trace_majorant
end QuantitativeMaass.Strong
