module

public import QuantitativeMaassRawHorizonStrongCostV1
public import QuantitativeMaassMajorantRecoveryScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass.Scheduled

/-- The literal finite-expression cost after inverse cap and inverse
metric still has the geometric square-root saving at the raw horizon. -/
theorem raw_compact_geometric_cost (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (ν : ℕ) (C A B D U : ℝ) (hC : 1≤C) (hA : 0≤A) (hB : 0≤B) (hD : 0≤D) :
    Tendsto (fun t =>
      let J := ⌈(ν:ℝ)*(C*radius ε t)+1⌉₊
      let m := Real.exp (Real.exp (B*(4:ℝ)^rawBlockHorizon t))
      (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2*A*m*(1+128*m)^40*D*
        Real.sqrt t*(ε t)^2*Real.exp (U*radius ε t+120*Strong.strongScale t)/(t*ε t))
      atTop (𝓝 0) := by
  have hh := (rawBlockHorizon_strong_geometric_decay ε (radius ε) 41
    (2*(3*(ν:ℝ)+7)*C+U) B 120 0 hB (hε.mono (fun _ h => h.1)) hp
    (radius_div_slowScale ε hε hp)).const_mul (A*D*(129:ℝ)^40)
  rw [mul_zero] at hh
  apply squeeze_zero' _ _ hh
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    have he0 := heps.1.le
    positivity
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    let J := ⌈(ν:ℝ)*(C*radius ε t)+1⌉₊
    let q := Real.exp (B*(4:ℝ)^rawBlockHorizon t)
    let m := Real.exp q
    have hm : 1≤m := Real.one_le_exp (Real.exp_pos _).le
    have hb : 1+128*m≤129*m := by linarith
    have he2 : (ε t)^2≤1 := by nlinarith
    have hcap := inverse_band_mass_exp_bound ν (R:=C*radius ε t)
      (one_le_mul_of_one_le_of_one_le hC (le_max_left (1:ℝ) _))
    change (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2*A*m*(1+128*m)^40*D*
      Real.sqrt t*(ε t)^2*Real.exp (U*radius ε t+120*Strong.strongScale t)/(t*ε t)≤_
    calc
      _≤(Real.exp ((3*(ν:ℝ)+7)*(C*radius ε t)))^2*A*m*(129*m)^40*D*
        Real.sqrt t*1*Real.exp (U*radius ε t+120*Strong.strongScale t)/(t*ε t) := by
          gcongr
          exact (mul_pos ht heps.1).le
      _=A*D*(129:ℝ)^40*(Real.sqrt t*
        Real.exp (41*q+(2*(3*(ν:ℝ)+7)*C+U)*radius ε t+120*Strong.strongScale t+0)/(t*ε t)) := by
          dsimp only [m]
          rw [mul_pow,←Real.exp_nat_mul,←Real.exp_nat_mul]
          rw [show 41*q+(2*(3*(ν:ℝ)+7)*C+U)*radius ε t+120*Strong.strongScale t+0=
            2*((3*(ν:ℝ)+7)*(C*radius ε t))+q+40*q+
              (U*radius ε t+120*Strong.strongScale t) by ring]
          simp only [Real.exp_add]
          ring

#print axioms raw_compact_geometric_cost
end QuantitativeMaass.Scheduled
