module

public import QuantitativeMaassMajorantRecoveryScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass.Scheduled

/-- The terminal cutoff that produces the sharp canonical rectangle
tends beyond every fixed positive starting height. -/
theorem half_height_eventually_ge (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (C : ℝ) (hC : 0≤C) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ t in atTop,δ≤Real.exp (Strong.strongScale t/2-C*radius ε t) := by
  filter_upwards [radius_mul_le_half_strong (2*C) (by positivity) ε hε hp,
    (Strong.strongScale_tendsto.atTop_div_const (by norm_num : (0:ℝ)<4)).eventually
      (eventually_ge_atTop (Real.log δ))] with t hr ht
  rw [←Real.exp_log hδ]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- Inverse-cap growth is negligible against the chosen upper cusp height.
The numerator is the actual finite inverse-band norm bound. -/
theorem inverse_band_half_height_tail_cost (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (ν : ℕ) (C : ℝ) (hC : 1≤C) :
    Tendsto (fun t =>
      let R := C*radius ε t
      let J := ⌈(ν:ℝ)*R+1⌉₊
      (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2*
        (Real.exp (Strong.strongScale t/2-R))⁻¹) atTop (𝓝 0) := by
  have hh := Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp
      (Strong.strongScale_tendsto.atTop_div_const (by norm_num : (0:ℝ)<4)))
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hh
  filter_upwards [radius_mul_le_half_strong (2*(6*(ν:ℝ)+15)*C)
    (by positivity) ε hε hp] with t hr
  let R := C*radius ε t
  let J := ⌈(ν:ℝ)*R+1⌉₊
  have hR1 : 1≤R := one_le_mul_of_one_le_of_one_le hC (le_max_left _ _)
  have hcap := inverse_band_mass_exp_bound ν hR1
  calc
    _≤(Real.exp ((3*(ν:ℝ)+7)*R))^2*(Real.exp (Strong.strongScale t/2-R))⁻¹ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcap 2) (by positivity)
    _=Real.exp ((6*(ν:ℝ)+15)*R-Strong.strongScale t/2) := by
      rw [←Real.exp_neg,show (6*(ν:ℝ)+15)*R-Strong.strongScale t/2=
        (3*(ν:ℝ)+7)*R+(3*(ν:ℝ)+7)*R+(-(Strong.strongScale t/2-R)) by ring,
        Real.exp_add,Real.exp_add]
      ring
    _≤_ := by
      apply Real.exp_le_exp.mpr
      dsimp only [Function.comp_apply,R]
      nlinarith

#print axioms half_height_eventually_ge
#print axioms inverse_band_half_height_tail_cost
end QuantitativeMaass.Scheduled
