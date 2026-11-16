module

public import QuantitativeArithmeticMaassWideReconstructionTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter Set MeasureTheory UpperHalfPlane ContinuousLinearMap
open QuantitativeNinaMaass QuantitativeHolomorphic AsymptoticClassicalPetersson
open scoped Topology SchwartzMap ContDiff FourierTransform
namespace QuantitativeMaass.Scheduled

/-- A tunable quadratic trace bound absorbs a growing spectral mass. The
energy error is measured with the stronger exponential weight dictated by
the Young parameter. -/
theorem weighted_trace_from_energy (ε E F : ℝ→ℝ) (C A W : ℝ) (hC : 0≤C) (hA : 0≤A)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hE : ∀ᶠ t in atTop,0≤E t)
    (hlim : Tendsto (fun t => Real.exp ((W+(|W|+A+1))*Strong.strongScale t)*E t/(t*ε t))
      atTop (𝓝 0))
    (hbound : ∀ᶠ t in atTop,|F t|≤
      Real.exp (-((|W|+A+1)*Strong.strongScale t))*(C*t*Real.exp (A*Strong.strongScale t))+
      (1+(Real.exp (-((|W|+A+1)*Strong.strongScale t)))⁻¹)*E t) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*F t/(t*ε t)) atTop (𝓝 0) := by
  have hmain := (Strong.strong_exponential_div_width ε hε hproduct).const_mul C
  have herr := hlim.const_mul 2
  simp only [mul_zero] at hmain herr
  have hsum := hmain.add herr
  simp only [zero_add] at hsum
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hsum
  filter_upwards [hbound,hε,hE,eventually_gt_atTop (0:ℝ)] with t hb heps he ht
  let s := Strong.strongScale t
  let Q := |W|+A+1
  have hs : 0≤s := sq_nonneg _
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hden : 0<t*ε t := mul_pos ht heps
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos hden]
  calc
    _ ≤ Real.exp (W*s)*(Real.exp (-(Q*s))*(C*t*Real.exp (A*s))+
        (1+(Real.exp (-(Q*s)))⁻¹)*E t)/(t*ε t) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le) hden.le
    _ ≤ (C*t*Real.exp (-s)+2*Real.exp ((W+Q)*s)*E t)/(t*ε t) := by
      apply div_le_div_of_nonneg_right _ hden.le
      rw [mul_add]
      apply add_le_add
      · calc
          _ = C*t*Real.exp ((W-Q+A)*s) := by
            rw [show (W-Q+A)*s=W*s+(-(Q*s))+A*s by ring,
              Real.exp_add,Real.exp_add]
            ring
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC ht.le)
            apply Real.exp_le_exp.mpr
            have hW := le_abs_self W
            dsimp [Q]
            nlinarith
      · have hi : (Real.exp (-(Q*s)))⁻¹=Real.exp (Q*s) := by rw [Real.exp_neg,inv_inv]
        rw [hi]
        have h1 : 1≤Real.exp (Q*s) := Real.one_le_exp (mul_nonneg hQ hs)
        calc
          _ ≤ Real.exp (W*s)*(2*Real.exp (Q*s))*E t := by
            rw [←mul_assoc]
            apply mul_le_mul_of_nonneg_right _ he
            exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
          _ = _ := by
            rw [show (W+Q)*s=W*s+Q*s by ring,Real.exp_add]
            ring
    _ = C*(Real.exp (-Strong.strongScale t)/ε t)+
        2*(Real.exp ((W+(|W|+A+1))*Strong.strongScale t)*E t/(t*ε t)) := by
      dsimp [s,Q]
      field_simp [ne_of_gt ht,ne_of_gt heps]

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

variable (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
  {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
  {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)

def newtonTraceDifference (he : Function.Even K) (ε : ℝ→ℝ)
    (A : AutomorphicSpace 0→L[ℂ]AutomorphicSpace N)
    (T : ℝ→Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
    (Dinput D t : ℝ) : ℝ :=
  let B := Real.exp (Dinput*Strong.strongScale t)
  let Bouter := WideInput.radius B (Real.exp (D*Strong.strongScale t))
    (inverseSqrtPolynomial (Strong.bandNewtonDepth t)).natDegree
  columnLinearTrace (quotientMeasure 0)
    (fun x => WideInput.ambientReconstruction S hδ hν χ t B (Strong.bandNewtonDepth t)
      (WideInput.bandTransfer S t B A (column K hc he ε t x))) (T t)-
  columnLinearTrace (quotientMeasure 0)
    (fun x => WideInput.bandReconstruction S hδ hν χ t B Bouter (Strong.bandNewtonDepth t)
      (WideInput.bandTransfer S t B A (column K hc he ε t x))) (T t)

/-- The scheduled actual cylinder trace is unchanged, up to arbitrarily
weighted o(t epsilon), by replacing ambient Newton reconstruction with a
single finite outer band. The output contraction may vary with t, so this
applies to the LV filters without assuming commutation with localization. -/
theorem localized_trace_compression (he : Function.Even K)
    (Ω : Set ℍ) (hΩ : IsCompact Ω) (a b : ℝ) (ha : 0<a)
    (hheight : ∀ x∈Ω,a≤x.im ∧ x.im≤b)
    (v : ℍ→ℂ) (hv : AEStronglyMeasurable v (volume.restrict Ω))
    {C : ℝ} (hC : ∀ᵐ x ∂volume.restrict Ω,‖v x‖≤C)
    (Dinput W : ℝ) (hDi : 0≤Dinput)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (T : ℝ→Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
    (hT : ∀ᶠ t in atTop,‖T t‖≤1) :
    ∃ D : ℝ,Dinput≤D ∧ 0<D ∧
      Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
        newtonTraceDifference K hc S hδ hν χ he ε
          (boundedCrossQuotientLocalization N 0 Ω hΩ v hv hC) T Dinput D t/(t*ε t))
        atTop (𝓝 0) := by
  let A := boundedCrossQuotientLocalization N 0 Ω hΩ v hv hC
  obtain ⟨Cdim,hCdim,hcount⟩ := fullBand_wide_finrank_bound N hN
  obtain ⟨D,hDiD,hD,herr⟩ := localized_newton_limit K hc S hδ hν χ he
    Ω hΩ a b ha hheight v hv hC Dinput (W+(|W|+(Dinput+1)+1)) hDi ε hε hproduct
  refine ⟨D,hDiD,hD,?_⟩
  apply weighted_trace_from_energy ε
    (newtonColumnError K hc S hδ hν χ he ε A Dinput D)
    (newtonTraceDifference K hc S hδ hν χ he ε A T Dinput D)
    (‖A‖^2*Cdim) (Dinput+1) W (by positivity) (by linarith)
    (hε.mono (fun _ h => h.1)) hproduct
    (Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))) herr
  filter_upwards [hT,packet_scheduled_norm K hc ε hε hproduct,
    Strong.exponential_band_width_quarter Dinput hDi,eventually_ge_atTop (6:ℝ)] with t hTt hp hBt ht
  let B := Real.exp (Dinput*Strong.strongScale t)
  let Bouter := WideInput.radius B (Real.exp (D*Strong.strongScale t))
    (inverseSqrtPolynomial (Strong.bandNewtonDepth t)).natDegree
  let η := Real.exp (-((|W|+(Dinput+1)+1)*Strong.strongScale t))
  have hη : 0<η := Real.exp_pos _
  have hcols : MemLp (fun x => A (cylinderAutomorphic (column K hc he ε t x)))
      2 (quotientMeasure 0) := by
    exact boundedCrossQuotientLocalization_column_memLp N (evenCoshLift (time K hc ε t))
      (evenCoshLift_smoothOn (time K hc ε t) ((time K hc ε t).smooth ⊤)
        (time_even K hc he ε t) (time_compact K hc ε t))
      (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
      (evenCoshLift_support_of_time_support (time K hc ε t) _
        (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le (time_support K hc ε t))
      Ω hΩ a b ha hheight v hv hC
  have hBB : B≤Bouter := WideInput.radius_mono B _ (Real.exp_pos _).le (Nat.zero_le _)
  have htrace := WideInput.reconstruction_column_trace S hδ hν χ t B Bouter hBB
    (Strong.bandNewtonDepth t) A (time K hc ε t) (time_compact K hc ε t)
    (time_even K hc he ε t) (time_real K hc he ε t)
    (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    (time_support K hc ε t) hcols (T t) η hη
  have hm : (‖cylinderTimePacket (time K hc ε t) ((time K hc ε t).smooth ⊤)
      (time_compact K hc ε t)‖*‖A‖)^2*(Module.finrank ℂ (S.band (t-B) (t+B)):ℝ)≤
      (‖A‖^2*Cdim)*t*Real.exp ((Dinput+1)*Strong.strongScale t) := by
    calc
      _ ≤ (Real.exp (Strong.strongScale t)*‖A‖^2)*(Cdim*t*B) := by
        rw [mul_pow]
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)
        · exact hcount S t B ht hBt.1 hBt.2
        · positivity
        · positivity
      _ = _ := by dsimp [B]; rw [add_mul,one_mul,Real.exp_add]; ring
  apply htrace.trans
  apply le_trans (mul_le_of_le_one_left (by positivity) hTt)
  exact add_le_add (mul_le_mul_of_nonneg_left hm hη.le) le_rfl

#print axioms weighted_trace_from_energy
#print axioms localized_trace_compression
end QuantitativeMaass.Scheduled
