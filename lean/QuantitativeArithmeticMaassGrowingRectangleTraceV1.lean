module

public import QuantitativeArithmeticMaassVaryingTransferTraceV1
public import QuantitativeArithmeticMaassRectangleTransferNormV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter Set MeasureTheory UpperHalfPlane ContinuousLinearMap
open QuantitativeNinaMaass QuantitativeHolomorphic AsymptoticClassicalPetersson
open scoped Topology SchwartzMap ContDiff FourierTransform
namespace QuantitativeMaass.Scheduled

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

variable (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
  {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
  {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)

/-- Moving rectangle cutoffs satisfy the ordered trace estimate from
explicit geometric height bounds. Operator norm and global integrability
conditions are proved here, not included as trace hypotheses. -/
theorem growing_rectangle_trace_compression (he : Function.Even K)
    (a b : ℝ→ℝ) (ha : ∀ t,0<a t) (v : ℝ→ℍ→ℂ)
    (hv : ∀ t,AEStronglyMeasurable (v t) (volume.restrict (upperRectangle 0 1 (a t) (b t))))
    (hbound : ∀ t,∀ᵐ x ∂volume.restrict (upperRectangle 0 1 (a t) (b t)),‖v t x‖≤1)
    (Y : ℝ) (hY : 0≤Y)
    (hsize : ∀ᶠ t in atTop,(2+(b t)^2)/a t≤Real.exp (Y*Strong.strongScale t))
    (Dinput W : ℝ) (hDi : 0≤Dinput)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (T : ℝ→Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
    (hT : ∀ᶠ t in atTop,‖T t‖≤1) :
    ∃ D : ℝ,Dinput≤D ∧ 0<D ∧
      Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
        newtonTraceDifference K hc S hδ hν χ he ε
          (boundedCrossQuotientLocalization N 0 (upperRectangle 0 1 (a t) (b t))
            (upperRectangle_compact 0 1 (a t) (b t) (ha t)) (v t) (hv t) (hbound t))
          T Dinput D t/(t*ε t)) atTop (𝓝 0) := by
  let A := fun t => boundedCrossQuotientLocalization N 0 (upperRectangle 0 1 (a t) (b t))
    (upperRectangle_compact 0 1 (a t) (b t) (ha t)) (v t) (hv t) (hbound t)
  apply varying_transfer_trace_compression K hc S hδ hν χ he A (8*Y+1) (by positivity)
    (rectangle_transfer_norm_schedule N a b ha v hv hbound Y hY hsize)
    Dinput W hDi ε hε hproduct _ T hT
  apply Eventually.of_forall
  intro t
  exact boundedCrossQuotientLocalization_column_memLp N (evenCoshLift (time K hc ε t))
    (evenCoshLift_smoothOn (time K hc ε t) ((time K hc ε t).smooth ⊤)
      (time_even K hc he ε t) (time_compact K hc ε t))
    (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    (evenCoshLift_support_of_time_support (time K hc ε t) _
      (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le (time_support K hc ε t))
    (upperRectangle 0 1 (a t) (b t)) (upperRectangle_compact 0 1 (a t) (b t) (ha t))
    (a t) (b t) (ha t) (fun _ hz => hz.2) (v t) (hv t) (hbound t)

end QuantitativeMaass.Scheduled
namespace QuantitativeMaass.Scheduled

/-- The required moving rectangle may extend down through the whole
propagation range and up to exp(strongScale). Its geometric cost is still
bounded by a fixed exponential in strongScale. -/
theorem propagated_rectangle_size {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∀ᶠ t in atTop,(2+(Real.exp (Strong.strongScale t))^2)/
      (δ*Real.exp (-(C*radius ε t)))≤Real.exp (4*Strong.strongScale t) := by
  have hp := (propagation_limits slowScale ε
    (slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ)))
    (hε.mono (fun _ h => h.1)) hproduct).1
  filter_upwards [radius_eventually_eq ε hε hproduct,
    hp.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    slowScale_tendsto.eventually (eventually_ge_atTop (1:ℝ)),
    slowScale_tendsto.eventually (eventually_ge_atTop (C+|Real.log δ|+1)),
    (Real.tendsto_exp_atTop.comp Strong.strongScale_tendsto).eventually
      (eventually_ge_atTop (3:ℝ))] with t hr hp hL hbig h3
  change 3≤Real.exp (Strong.strongScale t) at h3
  have hLp : 0<slowScale t := by linarith
  have hR : radius ε t≤slowScale t := by
    rw [hr]
    exact (div_le_one hLp).mp hp.le
  have hlog : C*radius ε t-Real.log δ≤Strong.strongScale t := by
    have hc := mul_le_mul_of_nonneg_left hR hC
    have hl := neg_le_abs (Real.log δ)
    change _≤(slowScale t)^2
    nlinarith [abs_nonneg (Real.log δ)]
  have hi : (δ*Real.exp (-(C*radius ε t)))⁻¹≤Real.exp (Strong.strongScale t) := by
    have hid : (δ*Real.exp (-(C*radius ε t)))⁻¹=
        Real.exp (C*radius ε t-Real.log δ) := by
      rw [mul_inv_rev,Real.exp_neg,inv_inv,Real.exp_sub,Real.exp_log hδ]
      ring
    rw [hid]
    exact Real.exp_le_exp.mpr hlog
  have h1 : 1≤Real.exp (Strong.strongScale t) := by linarith
  have hn : 2+(Real.exp (Strong.strongScale t))^2≤3*(Real.exp (Strong.strongScale t))^2 := by nlinarith
  calc
    _ = (2+(Real.exp (Strong.strongScale t))^2)*(δ*Real.exp (-(C*radius ε t)))⁻¹ := div_eq_mul_inv _ _
    _ ≤ (3*(Real.exp (Strong.strongScale t))^2)*Real.exp (Strong.strongScale t) := by
      apply mul_le_mul hn hi (by positivity) (by positivity)
    _ ≤ (Real.exp (Strong.strongScale t))^4 := by
      have hh := mul_le_mul_of_nonneg_right h3
        (show 0≤(Real.exp (Strong.strongScale t))^3 by positivity)
      nlinarith only [hh]
    _ = _ := by rw [←Real.exp_nat_mul]; norm_num

/-- The concrete moving rectangle used with the propagation schedule. -/
def propagatedRectangle (δ C : ℝ) (ε : ℝ→ℝ) (t : ℝ) : Set ℍ :=
  upperRectangle 0 1 (δ*Real.exp (-(C*radius ε t))) (Real.exp (Strong.strongScale t))

theorem propagatedRectangle_compact {δ : ℝ} (hδ : 0<δ) (C : ℝ) (ε : ℝ→ℝ) (t : ℝ) :
    IsCompact (propagatedRectangle δ C ε t) :=
  upperRectangle_compact 0 1 _ _ (mul_pos hδ (Real.exp_pos _))

/-- No norm-growth or column-integrability premise remains for the actual
propagated rectangles and bounded measurable cutoffs. -/
theorem propagated_rectangle_trace_compression
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)
    (he : Function.Even K) (C : ℝ) (hC : 0≤C)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (v : ℝ→ℍ→ℂ)
    (hv : ∀ t,AEStronglyMeasurable (v t) (volume.restrict (propagatedRectangle δ C ε t)))
    (hbound : ∀ t,∀ᵐ x ∂volume.restrict (propagatedRectangle δ C ε t),‖v t x‖≤1)
    (Dinput W : ℝ) (hDi : 0≤Dinput)
    (T : ℝ→Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
    (hT : ∀ᶠ t in atTop,‖T t‖≤1) :
    ∃ D : ℝ,Dinput≤D ∧ 0<D ∧
      Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
        newtonTraceDifference K hc S hδ hν χ he ε
          (boundedCrossQuotientLocalization N 0 (propagatedRectangle δ C ε t)
            (propagatedRectangle_compact hδ C ε t) (v t) (hv t) (hbound t))
          T Dinput D t/(t*ε t)) atTop (𝓝 0) := by
  exact growing_rectangle_trace_compression K hc S hδ hν χ he
    (fun t => δ*Real.exp (-(C*radius ε t))) (fun t => Real.exp (Strong.strongScale t))
    (fun _ => mul_pos hδ (Real.exp_pos _)) v hv hbound 4 (by norm_num)
    (propagated_rectangle_size hδ C hC ε hε hproduct) Dinput W hDi ε hε hproduct T hT

#print axioms propagated_rectangle_trace_compression
#print axioms growing_rectangle_trace_compression
#print axioms propagated_rectangle_size
end QuantitativeMaass.Scheduled
