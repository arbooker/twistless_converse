module

public import QuantitativeArithmeticMaassCylinderNewtonColumnsV1
public import QuantitativeArithmeticMaassScheduledPacketNormV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter Set MeasureTheory UpperHalfPlane ContinuousLinearMap
open QuantitativeNinaMaass QuantitativeHolomorphic AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap ContDiff
namespace QuantitativeMaass.Scheduled

def radius (ε : ℝ→ℝ) (t : ℝ) : ℝ := max 1 (propagation (slowScale t) (ε t))
theorem radius_pos (ε : ℝ→ℝ) (t : ℝ) : 0<radius ε t := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem radius_eventually_eq (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∀ᶠ t in atTop,radius ε t=propagation (slowScale t) (ε t) := by
  have hp := (propagation_limits slowScale ε
    (slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ)))
    (hε.mono (fun _ h => h.1)) hproduct).2
  filter_upwards [hε,hp.eventually (eventually_ge_atTop (1:ℝ))] with t he ht
  apply max_eq_right
  have hr : 0≤propagation (slowScale t) (ε t) := Real.sqrt_nonneg _
  nlinarith [he.2]

variable (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))

def time (ε : ℝ→ℝ) (t : ℝ) : SchwartzMap ℝ ℂ :=
  windowTimeSchwartz K hc (radius ε t) (radius_pos ε t) t (t+ε t)

theorem time_compact (ε : ℝ→ℝ) (t : ℝ) : HasCompactSupport (time K hc ε t : ℝ→ℂ) :=
  symmetricWindowTimeTest_compact K hc _ _ _ (radius_pos ε t)

theorem time_even (he : Function.Even K) (ε : ℝ→ℝ) (t : ℝ) : Function.Even (time K hc ε t) :=
  symmetricWindowTimeTest_even K he _ _ _

theorem time_real (he : Function.Even K) (ε : ℝ→ℝ) (t u : ℝ) :
    star (time K hc ε t u)=time K hc ε t u := symmetricWindowTimeTest_real K he _ _ _ u

def supportRadius : ℝ := Classical.choose (symmetricWindowTimeTest_uniform_support K hc)
theorem supportRadius_pos : 0<supportRadius K hc :=
  (Classical.choose_spec (symmetricWindowTimeTest_uniform_support K hc)).1

theorem time_support (ε : ℝ→ℝ) (t : ℝ) :
    Function.support (time K hc ε t)⊆Icc (-(supportRadius K hc*radius ε t))
      (supportRadius K hc*radius ε t) :=
  (Classical.choose_spec (symmetricWindowTimeTest_uniform_support K hc)).2 _ (radius_pos ε t) _ _

def column (he : Function.Even K) (ε : ℝ→ℝ) (t : ℝ) : ℍ→Lp ℂ 2 (quotientMeasure 0) :=
  cylinderTimeColumn (time K hc ε t) (time_compact K hc ε t) (time_even K hc he ε t)
    (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    (time_support K hc ε t)

theorem packet_scheduled_norm (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∀ᶠ t in atTop,‖cylinderTimePacket (time K hc ε t) ((time K hc ε t).smooth ⊤)
      (time_compact K hc ε t)‖^2≤Real.exp (Strong.strongScale t) := by
  filter_upwards [radius_eventually_eq ε hε hproduct,
    cylinderWindowPacket_scheduled_norm K hc ε hε hproduct] with t heq ht
  have hR : 0<propagation (slowScale t) (ε t) := heq ▸ radius_pos ε t
  simpa only [time,heq] using ht hR

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

variable {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
  {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)

def newtonColumnError (he : Function.Even K) (ε : ℝ→ℝ)
    (A : AutomorphicSpace 0→L[ℂ]AutomorphicSpace N) (Dinput D t : ℝ) : ℝ :=
  let B := Real.exp (Dinput*Strong.strongScale t)
  let Bouter := WideInput.radius B (Real.exp (D*Strong.strongScale t))
    (inverseSqrtPolynomial (Strong.bandNewtonDepth t)).natDegree
  ∫ x,‖WideInput.newtonDefect S hδ hν χ t B Bouter (Strong.bandNewtonDepth t)
    (WideInput.bandTransfer S t B A (column K hc he ε t x))‖^2 ∂quotientMeasure 0

/-- Actual compact cross-localizations of the scheduled cylinder packets
admit Newton compression with arbitrarily weighted o(t epsilon) error.
Column integrability, packet norm growth and all polynomial costs have
been derived; no finite-source error estimate is assumed here. -/
theorem localized_newton_limit (he : Function.Even K)
    (Ω : Set ℍ) (hΩ : IsCompact Ω) (a b : ℝ) (ha : 0<a)
    (hheight : ∀ x∈Ω,a≤x.im ∧ x.im≤b)
    (v : ℍ→ℂ) (hv : AEStronglyMeasurable v (volume.restrict Ω))
    {C : ℝ} (hC : ∀ᵐ x ∂volume.restrict Ω,‖v x‖≤C)
    (Dinput W : ℝ) (hDi : 0≤Dinput)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ D : ℝ,Dinput≤D ∧ 0<D ∧
      Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
        newtonColumnError K hc S hδ hν χ he ε
          (boundedCrossQuotientLocalization N 0 Ω hΩ v hv hC) Dinput D t/(t*ε t))
        atTop (𝓝 0) := by
  let A := boundedCrossQuotientLocalization N 0 Ω hΩ v hv hC
  obtain ⟨D,hDiD,hD,F,hF,hbound⟩ := WideInput.weighted_cylinder_newton S hδ hν χ
    Dinput (W+1) hDi ε (hε.mono (fun _ h => h.1)) hproduct
  refine ⟨D,hDiD,hD,?_⟩
  have hlim : Tendsto (fun t => ‖A‖^2*Real.exp ((W+1)*Strong.strongScale t)*|F t|/(t*ε t))
      atTop (𝓝 0) := by
    have hh := hF.abs.const_mul (‖A‖^2)
    simp only [abs_zero,mul_zero] at hh
    apply hh.congr'
    filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    rw [abs_div,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (mul_pos ht heps.1)]
    ring
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    apply div_nonneg _ (mul_pos ht heps.1).le
    exact mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => sq_nonneg _))
  · filter_upwards [hbound,packet_scheduled_norm K hc ε hε hproduct,
      hε,eventually_gt_atTop (0:ℝ)] with t ht hpacket heps ht0
    let B := Real.exp (Dinput*Strong.strongScale t)
    let Bouter := WideInput.radius B (Real.exp (D*Strong.strongScale t))
      (inverseSqrtPolynomial (Strong.bandNewtonDepth t)).natDegree
    have hB : 1≤B := Real.one_le_exp (mul_nonneg hDi (sq_nonneg _))
    have hcols : MemLp (fun x => A (cylinderAutomorphic (column K hc he ε t x)))
        2 (quotientMeasure 0) := by
      exact boundedCrossQuotientLocalization_column_memLp N (evenCoshLift (time K hc ε t))
        (evenCoshLift_smoothOn (time K hc ε t) ((time K hc ε t).smooth ⊤)
          (time_even K hc he ε t) (time_compact K hc ε t))
        (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
        (evenCoshLift_support_of_time_support (time K hc ε t) _
          (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le (time_support K hc ε t))
        Ω hΩ a b ha hheight v hv hC
    have hb := ht B hB le_rfl Bouter le_rfl A (time K hc ε t) (time_compact K hc ε t)
      (time_even K hc he ε t) (time_real K hc he ε t)
      (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
      (time_support K hc ε t) hcols
    have he : newtonColumnError K hc S hδ hν χ he ε A Dinput D t≤
        Real.exp (Strong.strongScale t)*‖A‖^2*|F t| := by
      apply hb.trans
      calc
        _ ≤ (‖cylinderTimePacket (time K hc ε t) ((time K hc ε t).smooth ⊤)
          (time_compact K hc ε t)‖*‖A‖)^2*|F t| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
        _ ≤ _ := by rw [mul_pow]; gcongr
    apply div_le_div_of_nonneg_right _ (mul_pos ht0 heps.1).le
    calc
      _ ≤ Real.exp (W*Strong.strongScale t)*(Real.exp (Strong.strongScale t)*‖A‖^2*|F t|) :=
        mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
      _ = _ := by rw [add_mul,one_mul,Real.exp_add]; ring

#print axioms packet_scheduled_norm
#print axioms localized_newton_limit
end QuantitativeMaass.Scheduled
