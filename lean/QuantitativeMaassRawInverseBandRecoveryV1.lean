module

public import QuantitativeMaassMajorantRecoveryScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass.Scheduled

/-- The actual bounded weighted regular recovery rate absorbs the finite
inverse-cap mass at the chosen raw integer horizon. -/
theorem raw_inverse_band_recovery_decay (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (ν : ℕ) (C A D K I : ℝ) (hC : 1≤C) (hA : 0≤A) (hD : 0≤D) (hK : 0≤K) (hI : 0≤I) :
    Tendsto (fun t =>
      let J := ⌈(ν:ℝ)*(C*radius ε t)+1⌉₊
      (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2*A*
        (D/(2:ℝ)^rawBlockHorizon t+4*Real.sqrt (K/(2:ℝ)^rawBlockHorizon t)*I))
      atTop (𝓝 0) := by
  have hR : Tendsto (fun t => (C*radius ε t)/slowScale t) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_div_assoc] using (radius_div_slowScale ε hε hp).const_mul C
  have hh := (raw_canonical_recovery_decay ε (fun t => C*radius ε t) (2*(3*(ν:ℝ)+7))
    D K I (by positivity) hK (hε.mono (fun _ h => h.1)) hp hR).const_mul A
  rw [mul_zero] at hh
  apply squeeze_zero' _ _ hh
  · exact Eventually.of_forall (fun _ => by positivity)
  · filter_upwards [hε] with t heps
    let J := ⌈(ν:ℝ)*(C*radius ε t)+1⌉₊
    let err := D/(2:ℝ)^rawBlockHorizon t+4*Real.sqrt (K/(2:ℝ)^rawBlockHorizon t)*I
    have herr : 0≤err := by dsimp only [err]; positivity
    have hcap := inverse_band_mass_exp_bound ν (R:=C*radius ε t)
      (one_le_mul_of_one_le_of_one_le hC (le_max_left _ _))
    calc
      _≤(Real.exp ((3*(ν:ℝ)+7)*(C*radius ε t)))^2*A*err := by
        apply mul_le_mul_of_nonneg_right _ herr
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hcap 2) hA
      _=A*(Real.exp ((2*(3*(ν:ℝ)+7))*(C*radius ε t))*err) := by
        rw [show (2*(3*(ν:ℝ)+7))*(C*radius ε t)=
          (3*(ν:ℝ)+7)*(C*radius ε t)+(3*(ν:ℝ)+7)*(C*radius ε t) by ring,Real.exp_add]
        ring
      _≤_ := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply (le_div_iff₀ heps.1).mpr
        exact mul_le_of_le_one_right (mul_nonneg (Real.exp_pos _).le herr) heps.2

/-- A resolved window identity contribution may be included without any
extra loss in the recovery rate after division by the original t epsilon. -/
theorem raw_inverse_band_window_recovery_decay (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (ν : ℕ) (C A D K I B : ℝ) (hC : 1≤C) (hA : 0≤A) (hD : 0≤D) (hK : 0≤K) (hI : 0≤I)
    (w : ℝ→ℂ) (hw : ∀ᶠ t in atTop,‖w t‖≤B*(t*ε t)) :
    Tendsto (fun t =>
      let J := ⌈(ν:ℝ)*(C*radius ε t)+1⌉₊
      (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2*A*‖w t‖*
        (D/(2:ℝ)^rawBlockHorizon t+4*Real.sqrt (K/(2:ℝ)^rawBlockHorizon t)*I)/(t*ε t))
      atTop (𝓝 0) := by
  have hh := (raw_inverse_band_recovery_decay ε hε hp ν C A D K I hC hA hD hK hI).const_mul B
  rw [mul_zero] at hh
  apply squeeze_zero' _ _ hh
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    have he0 := heps.1.le
    positivity
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ),hw] with t heps ht hw
    let J := ⌈(ν:ℝ)*(C*radius ε t)+1⌉₊
    let err := D/(2:ℝ)^rawBlockHorizon t+4*Real.sqrt (K/(2:ℝ)^rawBlockHorizon t)*I
    have herr : 0≤err := by dsimp only [err]; positivity
    change (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2*A*‖w t‖*err/(t*ε t)≤_
    calc
      _≤(((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2*A*(B*(t*ε t))*err/(t*ε t) := by
        apply div_le_div_of_nonneg_right _ (mul_pos ht heps.1).le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by positivity)) herr
      _=_ := by
        dsimp only [J,err]
        field_simp [ht.ne',heps.1.ne']

#print axioms raw_inverse_band_recovery_decay
#print axioms raw_inverse_band_window_recovery_decay
end QuantitativeMaass.Scheduled
