module

public import QuantitativeMaassMajorantCompactEnergyV1
public import QuantitativeMaassRawCanonicalRecoveryDecayV1
public import QuantitativeMaassInverseBandGrowthV1
public import QuantitativeMaassCappedColumnTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

theorem radius_div_slowScale (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => radius ε t/slowScale t) atTop (𝓝 0) := by
  apply (propagation_limits slowScale ε
    (slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ)))
    (hε.mono (fun _ h => h.1)) hp).1.congr'
  filter_upwards [radius_eventually_eq ε hε hp] with t ht
  rw [ht]

/-- Source recovery for the actual compact majorant columns at the raw
integer filter horizon. Only propagation losses occur in this term. -/
theorem originalMajorant_compact_recovery_limit {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    {δ : ℝ} (hδ : 0<δ) (ν : ℕ) (C : ℝ) (hC : 1≤C)
    (D : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
    (Kerr : ℝ) (hKerr : 0≤Kerr) :
    Tendsto (fun t =>
      let R := C*radius ε t
      let J := ⌈(ν:ℝ)*R+1⌉₊
      let a := movingLowerEdge δ C ε t
      let S := cutoffRectangle a t
      let P := AsymptoticRegionL2.projection (quotientMeasure 0) S
        (upperRectangle_compact 0 1 a _ (movingLowerEdge_pos hδ C ε t)).measurableSet
      let L := (terminalInverseWeightBand δ ν J).comp D
      (3*Real.sqrt (Kerr/(2:ℝ)^rawBlockHorizon t)*‖L‖^2)*
        (∫ z,‖P (originalMajorantColumn K hc he ε t z)‖^2 ∂quotientMeasure 0)/(t*ε t))
      atTop (𝓝 0) := by
  obtain ⟨B,hB,henergy⟩ := originalMajorant_compact_column_energy_uniform basis K hc he hK hm (1/2)
  let R := fun t => C*radius ε t
  have hR : Tendsto (fun t => R t/slowScale t) atTop (𝓝 0) := by
    have hh := (radius_div_slowScale ε hε hp).const_mul C
    rw [mul_zero] at hh
    convert hh using 1
    funext t
    dsimp only [R]
    ring
  have hdecay := raw_canonical_recovery_decay ε R (6*(ν:ℝ)+15) 0 Kerr (1/4)
    (by positivity) hKerr (hε.mono (fun _ h => h.1)) hp hR
  have hlim := hdecay.const_mul (3*‖D‖^2*δ⁻¹*B)
  rw [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    exact div_nonneg (mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _)))
      (mul_pos ht heps.1).le
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ),henergy ε hε hp] with t heps ht hmass
    let J := ⌈(ν:ℝ)*R t+1⌉₊
    let a := movingLowerEdge δ C ε t
    let P := AsymptoticRegionL2.projection (quotientMeasure 0) (cutoffRectangle a t)
      (upperRectangle_compact 0 1 a _ (movingLowerEdge_pos hδ C ε t)).measurableSet
    let L := (terminalInverseWeightBand δ ν J).comp D
    have hR1 : 1≤R t := one_le_mul_of_one_le_of_one_le hC (le_max_left _ _)
    have hLn : ‖L‖≤Real.exp ((3*(ν:ℝ)+7)*R t)*‖D‖ :=
      (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
        ((terminalInverseWeightBand_norm hδ ν J).trans (inverse_band_mass_exp_bound ν hR1)) (norm_nonneg _))
    have hmass' : (∫ z,‖P (originalMajorantColumn K hc he ε t z)‖^2 ∂quotientMeasure 0)≤
        δ⁻¹*Real.exp (R t)*B*(t*ε t) := by
      have hh := hmass a (Real.exp (Strong.strongScale t/2)) (movingLowerEdge_pos hδ C ε t)
        (Real.exp_pos _).le (by apply Real.exp_le_exp.mpr; linarith)
      calc
        _≤a⁻¹*B*(t*ε t) := hh
        _=_ := by
          dsimp only [a,movingLowerEdge,R]
          rw [mul_inv_rev,Real.exp_neg,inv_inv]
          ring
    change (3*Real.sqrt (Kerr/(2:ℝ)^rawBlockHorizon t)*‖L‖^2)*
      (∫ z,‖P (originalMajorantColumn K hc he ε t z)‖^2 ∂quotientMeasure 0)/(t*ε t)≤_
    calc
      _≤(3*Real.sqrt (Kerr/(2:ℝ)^rawBlockHorizon t)*
        (Real.exp ((3*(ν:ℝ)+7)*R t)*‖D‖)^2)*
        (δ⁻¹*Real.exp (R t)*B*(t*ε t))/(t*ε t) := by
          apply div_le_div_of_nonneg_right _ (mul_pos ht heps.1).le
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hLn 2) (by positivity)
          · exact hmass'
          · exact integral_nonneg (fun _ => sq_nonneg _)
          · positivity
      _=(3*‖D‖^2*δ⁻¹*B)*(Real.exp ((6*(ν:ℝ)+15)*R t)*
        Real.sqrt (Kerr/(2:ℝ)^rawBlockHorizon t)) := by
          rw [show (6*(ν:ℝ)+15)*R t=(3*(ν:ℝ)+7)*R t+(3*(ν:ℝ)+7)*R t+R t by ring,
            Real.exp_add,Real.exp_add]
          field_simp [ht.ne',heps.1.ne']
      _≤_ := by
        simp only [zero_div,zero_add]
        have hn : 0≤Real.exp ((6*(ν:ℝ)+15)*R t)*Real.sqrt (Kerr/(2:ℝ)^rawBlockHorizon t) := by positivity
        have hh := (le_div_iff₀ heps.1).mpr (mul_le_of_le_one_right hn heps.2)
        convert mul_le_mul_of_nonneg_left hh (by positivity : 0≤3*‖D‖^2*δ⁻¹*B) using 1
        ring

#print axioms radius_div_slowScale
#print axioms originalMajorant_compact_recovery_limit
end QuantitativeMaass.Scheduled
