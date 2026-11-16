module

public import QuantitativeMaassCompactTailScheduleV1
public import QuantitativeMaassCompactHeightScheduleV1
public import QuantitativeArithmeticMaassCylinderRectangleMassV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped Topology
namespace QuantitativeMaass.Scheduled

/-- The explicit centering remainder, including propagated rectangle area
and the finite inverse cap, has the geometric square-root saving. -/
theorem inverse_band_centering_cost (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    {δ : ℝ} (hδ : 0<δ) (ν : ℕ) (C B : ℝ) (hC : 1≤C) (hB : 0≤B)
    (T : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0)) :
    Tendsto (fun t =>
      let R := C*radius ε t
      let J := ⌈(ν:ℝ)*R+1⌉₊
      let K := terminalInverseWeightBand δ ν J
      let a := δ*Real.exp (-R)
      let b := Real.exp (Strong.strongScale t/2)
      2*‖K.comp (T.comp K.adjoint)‖*(max 0 (b*Real.exp R)*
        ((B*Real.sqrt t*(radius ε t)^2*(ε t)^2)*
          (Real.pi*(2*(2*(|Real.cosh (2*R)|+1)+1)+2)))*
        volume.real (upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R)))/(t*ε t))
      atTop (𝓝 0) := by
  let A := 24*‖T‖*B*Real.pi*δ⁻¹
  have hlim := Strong.compact_height_geometric_cost ε ((6*(ν:ℝ)+21)*C) (1/2) A
    (hε.mono (fun _ h => h.1)) hp
  have hh : Tendsto (fun t => A*Real.sqrt t*
      Real.exp ((6*(ν:ℝ)+21)*(C*radius ε t)+Strong.strongScale t/2)/(t*ε t)) atTop (𝓝 0) := by
    apply hlim.congr'
    filter_upwards [radius_eventually_eq ε hε hp] with t hr
    rw [Strong.log_compactCuspHeight,hr]
    congr 2
    ring
  apply squeeze_zero' _ _ hh
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    have he0 := heps.1.le
    positivity
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    let R := C*radius ε t
    let J := ⌈(ν:ℝ)*R+1⌉₊
    let K := terminalInverseWeightBand δ ν J
    let a := δ*Real.exp (-R)
    let b := Real.exp (Strong.strongScale t/2)
    have hR1 : 1≤R := one_le_mul_of_one_le_of_one_le hC (le_max_left _ _)
    have hR0 : 0≤R := zero_le_one.trans hR1
    have hmass := (terminalInverseWeightBand_norm hδ ν J).trans (inverse_band_mass_exp_bound ν hR1)
    have hnorm : ‖K.comp (T.comp K.adjoint)‖≤
        (Real.exp ((3*(ν:ℝ)+7)*R))^2*‖T‖ := by
      calc
        _≤‖K‖*(‖T‖*‖K.adjoint‖) := (opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
        _=‖K‖^2*‖T‖ := by rw [adjoint.norm_map]; ring
        _≤_ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hmass 2) (norm_nonneg _)
    have harea : volume.real (upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R))≤
        δ⁻¹*Real.exp (2*R) := by
      have hh := rectangle_area_le_inverse (a*Real.exp (-R)) (b*Real.exp R) (by dsimp only [a]; positivity)
      apply hh.trans_eq
      dsimp only [a]
      rw [mul_inv_rev,mul_inv_rev,Real.exp_neg,inv_inv,show 2*R=R+R by ring,Real.exp_add]
      ring
    have hcosh : Real.pi*(2*(2*(|Real.cosh (2*R)|+1)+1)+2)≤12*Real.pi*Real.exp (2*R) := by
      rw [abs_of_pos (Real.cosh_pos _)]
      have hc : Real.cosh (2*R)≤Real.exp (2*R) := by
        rw [Real.cosh_eq]
        have hh := Real.exp_le_exp.mpr (show -(2*R)≤2*R by linarith)
        linarith
      have he := Real.one_le_exp (by positivity : 0≤2*R)
      nlinarith [Real.pi_pos]
    have hr : (radius ε t)^2≤(Real.exp R)^2 := by
      apply pow_le_pow_left₀ (radius_pos ε t).le
      exact (le_mul_of_one_le_left (radius_pos ε t).le hC).trans (by linarith [Real.add_one_le_exp R] : R≤Real.exp R)
    have he2 : (ε t)^2≤1 := by nlinarith
    change 2*‖K.comp (T.comp K.adjoint)‖*(max 0 (b*Real.exp R)*
      ((B*Real.sqrt t*(radius ε t)^2*(ε t)^2)*
        (Real.pi*(2*(2*(|Real.cosh (2*R)|+1)+1)+2)))*
      volume.real (upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R)))/(t*ε t)≤_
    rw [max_eq_right (by dsimp only [b]; positivity : 0≤b*Real.exp R)]
    calc
      _≤2*((Real.exp ((3*(ν:ℝ)+7)*R))^2*‖T‖)*
        ((b*Real.exp R)*((B*Real.sqrt t*(Real.exp R)^2*1)*(12*Real.pi*Real.exp (2*R)))*
          (δ⁻¹*Real.exp (2*R)))/(t*ε t) := by
            gcongr
            exact (mul_pos ht heps.1).le
      _=_ := by
        dsimp only [A,b,R]
        rw [show (6*(ν:ℝ)+21)*(C*radius ε t)+Strong.strongScale t/2=
          (3*(ν:ℝ)+7)*(C*radius ε t)+(3*(ν:ℝ)+7)*(C*radius ε t)+
          Strong.strongScale t/2+C*radius ε t+C*radius ε t+C*radius ε t+
          2*(C*radius ε t)+2*(C*radius ε t) by ring]
        simp only [Real.exp_add]
        ring

#print axioms inverse_band_centering_cost
end QuantitativeMaass.Scheduled
