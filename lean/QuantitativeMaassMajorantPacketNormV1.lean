module

public import QuantitativeNinaMaassWindowEnergyUpperV1
public import QuantitativeArithmeticMaassScheduledPacketNormV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- The literal enlarged and normalized majorant packet has a uniform
cylinder norm bound, including its positive normalization. -/
theorem originalMajorant_cylinder_norm_le (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (ε : ℝ→ℝ) (t : ℝ) :
    ‖cylinderTimePacket (QuantitativeNinaMaass.originalWindowMajorant K hc ε t)
      ((QuantitativeNinaMaass.originalWindowMajorant K hc ε t).smooth ⊤)
      (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t)‖≤
      2*‖windowWavePacket 0 K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
        (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t))‖ := by
  let d := QuantitativeNinaMaass.windowEnergyDenominator K ε t
  have hd : 0<d := QuantitativeNinaMaass.windowEnergyDenominator_pos K ε t
  have hi : d⁻¹≤2 := by
    have hh := inv_anti₀ (by norm_num : (0:ℝ)<1/2)
      (le_max_left (1/2:ℝ) (1-(∫ u,|u| * K u)/
        (positiveWindowRadius ε t*smoothingWidth (slowScale t) (ε t))))
    simpa only [d,QuantitativeNinaMaass.windowEnergyDenominator,one_div,inv_inv] using hh
  apply opNorm_le_bound _ (mul_nonneg (by norm_num : (0:ℝ)≤2)
    (norm_nonneg (windowWavePacket 0 K hc (positiveWindowRadius ε t)
      (positiveWindowRadius_pos ε t) (t-smoothingWidth (slowScale t) (ε t))
      (t+ε t+smoothingWidth (slowScale t) (ε t)))))
  intro v
  change ‖Wave.shiftedQuotientWavePacket 0 (QuantitativeNinaMaass.originalWindowMajorant K hc ε t)
    (compactSmoothWaveWeight _ ((QuantitativeNinaMaass.originalWindowMajorant K hc ε t).smooth ⊤)
      (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t)) (cylinderAutomorphic v)‖≤_
  rw [QuantitativeNinaMaass.originalWindowMajorant_packet]
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
  apply (mul_le_mul hi ((windowWavePacket 0 K hc _ _ _ _).le_opNorm _)
    (norm_nonneg _) (by norm_num)).trans_eq
  rw [cylinderAutomorphic.norm_map]
  ring

/-- The actual original majorant, rather than the different one-sided
profile, satisfies the operator bound needed for finite-band reconstruction. -/
theorem originalMajorant_cylinder_scheduled_norm (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∀ᶠ t in atTop,‖cylinderTimePacket (QuantitativeNinaMaass.originalWindowMajorant K hc ε t)
      ((QuantitativeNinaMaass.originalWindowMajorant K hc ε t).smooth ⊤)
      (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t)‖^2≤
      Real.exp (Strong.strongScale t) := by
  obtain ⟨B,C,hB,hC,hbound⟩ := windowWavePacket_uniform_square_norm K hc
  have hprop := positiveWindowRadius_div_scale ε (hε.mono (fun _ h => h.1)) hp
  filter_upwards [hε,QuantitativeNinaMaass.originalWindowMajorant_parameters ε hε hp,
    slowScale_tendsto.eventually (eventually_ge_atTop (1:ℝ)),
    slowScale_tendsto.eventually (eventually_ge_atTop (16*C+B+2)),
    hprop.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
    with t he hparam hl hlarge hpR
  let L := slowScale t
  let R := positiveWindowRadius ε t
  let a := t-smoothingWidth L (ε t)
  let b := t+ε t+smoothingWidth L (ε t)
  have hLp : 0<L := zero_lt_one.trans_le hl
  have hRL : R≤L := (div_le_one hLp).mp hpR.le
  have hR : 0<R := positiveWindowRadius_pos ε t
  have hab : a≤b := by dsimp only [a,b,L]; linarith [hparam.1,he.1]
  have hwidth : b-a≤2 := by dsimp only [a,b,L]; linarith [hparam.2.1,he.2]
  have hn := pow_le_pow_left₀ (norm_nonneg _) (originalMajorant_cylinder_norm_le K hc ε t) 2
  have hmain := hbound 0 R hR a b hab
  have hC0 : 0≤16*C := by positivity
  have hLe : L≤Real.exp L := by linarith [Real.add_one_le_exp L]
  have hCe : 16*C≤Real.exp ((16*C)*L) := by
    have hh := Real.add_one_le_exp ((16*C)*L)
    have hx : 16*C≤(16*C)*L := by nlinarith [hC,hl]
    linarith
  calc
    _ ≤ 4*‖windowWavePacket 0 K hc R hR a b‖^2 := by simpa only [mul_pow,show (2:ℝ)^2=4 by norm_num] using hn
    _ ≤ (16*C)*R^2*Real.exp (B*R) := by
      have hw : (b-a)^2≤4 := by nlinarith [hab]
      calc
        _ ≤ 4*(C*(b-a)^2*R^2*Real.exp (B*R)) :=
          mul_le_mul_of_nonneg_left hmain (by norm_num)
        _ ≤ 4*(C*4*R^2*Real.exp (B*R)) := by gcongr
        _ = _ := by ring
    _ ≤ (16*C)*L^2*Real.exp (B*L) := by gcongr
    _ ≤ Real.exp ((16*C)*L)*(Real.exp L)^2*Real.exp (B*L) := by gcongr
    _ = Real.exp ((16*C+B+2)*L) := by
      rw [pow_two,←Real.exp_add,←Real.exp_add,←Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Strong.strongScale t) := by
      apply Real.exp_le_exp.mpr
      change (16*C+B+2)*L≤L^2
      nlinarith

#print axioms originalMajorant_cylinder_norm_le
#print axioms originalMajorant_cylinder_scheduled_norm
end QuantitativeMaass
