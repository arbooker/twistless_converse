module

public import QuantitativeArithmeticMaassScheduledTraceCompressionV1

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

/-- Newton column error from an arbitrary input width. -/
def newtonColumnErrorAtWidth (he : Function.Even K) (ε : ℝ→ℝ)
    (A : AutomorphicSpace 0→L[ℂ]AutomorphicSpace N) (B D t : ℝ) : ℝ :=
  let Bouter := WideInput.radius B (Real.exp (D*Strong.strongScale t))
    (inverseSqrtPolynomial (Strong.bandNewtonDepth t)).natDegree
  ∫ x,‖WideInput.newtonDefect S hδ hν χ t B Bouter (Strong.bandNewtonDepth t)
    (WideInput.bandTransfer S t B A (column K hc he ε t x))‖^2 ∂quotientMeasure 0

/-- Ordered trace error from the same arbitrary input width. -/
def newtonTraceDifferenceAtWidth (he : Function.Even K) (ε : ℝ→ℝ)
    (A : AutomorphicSpace 0→L[ℂ]AutomorphicSpace N)
    (T : ℝ→Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
    (B D t : ℝ) : ℝ :=
  let Bouter := WideInput.radius B (Real.exp (D*Strong.strongScale t))
    (inverseSqrtPolynomial (Strong.bandNewtonDepth t)).natDegree
  columnLinearTrace (quotientMeasure 0)
    (fun x => WideInput.ambientReconstruction S hδ hν χ t B (Strong.bandNewtonDepth t)
      (WideInput.bandTransfer S t B A (column K hc he ε t x))) (T t)-
  columnLinearTrace (quotientMeasure 0)
    (fun x => WideInput.bandReconstruction S hδ hν χ t B Bouter (Strong.bandNewtonDepth t)
      (WideInput.bandTransfer S t B A (column K hc he ε t x))) (T t)

theorem varying_width_transfer_newton_limit (he : Function.Even K)
    (A : ℝ→AutomorphicSpace 0→L[ℂ]AutomorphicSpace N) (Z : ℝ)
    (hA : ∀ᶠ t in atTop,‖A t‖^2≤Real.exp (Z*Strong.strongScale t))
    (Dinput W : ℝ) (hDi : 0≤Dinput)
    (width : ℝ→ℝ)
    (hwidth : ∀ᶠ t in atTop,1≤width t ∧ width t≤Real.exp (Dinput*Strong.strongScale t))
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hcols : ∀ᶠ t in atTop,MemLp (fun x => A t (cylinderAutomorphic (column K hc he ε t x)))
      2 (quotientMeasure 0)) :
    ∃ D : ℝ,Dinput≤D ∧ 0<D ∧
      Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
        newtonColumnErrorAtWidth K hc S hδ hν χ he ε (A t) (width t) D t/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨D,hDiD,hD,F,hF,hbound⟩ := WideInput.weighted_cylinder_newton S hδ hν χ
    Dinput (W+(Z+1)) hDi ε (hε.mono (fun _ h => h.1)) hproduct
  refine ⟨D,hDiD,hD,?_⟩
  have hlim : Tendsto (fun t => Real.exp ((W+(Z+1))*Strong.strongScale t)*|F t|/(t*ε t))
      atTop (𝓝 0) := by
    have hh := hF.abs
    simp only [abs_zero] at hh
    apply hh.congr'
    filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    rw [abs_div,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (mul_pos ht heps.1)]
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    apply div_nonneg _ (mul_pos ht heps.1).le
    exact mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => sq_nonneg _))
  · filter_upwards [hbound,packet_scheduled_norm K hc ε hε hproduct,hA,hcols,
      hε,eventually_gt_atTop (0:ℝ),hwidth] with t ht hpacket hAt hct heps ht0 hwt
    let B := width t
    let Bouter := WideInput.radius B (Real.exp (D*Strong.strongScale t))
      (inverseSqrtPolynomial (Strong.bandNewtonDepth t)).natDegree
    have hB : 1≤B := hwt.1
    have hb := ht B hB hwt.2 Bouter le_rfl (A t) (time K hc ε t) (time_compact K hc ε t)
      (time_even K hc he ε t) (time_real K hc he ε t)
      (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
      (time_support K hc ε t) hct
    have he : newtonColumnErrorAtWidth K hc S hδ hν χ he ε (A t) (width t) D t≤
        Real.exp ((Z+1)*Strong.strongScale t)*|F t| := by
      apply hb.trans
      calc
        _ ≤ (‖cylinderTimePacket (time K hc ε t) ((time K hc ε t).smooth ⊤)
          (time_compact K hc ε t)‖*‖A t‖)^2*|F t| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
        _ ≤ (Real.exp (Strong.strongScale t)*Real.exp (Z*Strong.strongScale t))*|F t| := by
          rw [mul_pow]
          gcongr
        _ = _ := by rw [add_mul,one_mul,Real.exp_add]; ring
    apply div_le_div_of_nonneg_right _ (mul_pos ht0 heps.1).le
    calc
      _ ≤ Real.exp (W*Strong.strongScale t)*(Real.exp ((Z+1)*Strong.strongScale t)*|F t|) :=
        mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
      _ = _ := by
        rw [show (W+(Z+1))*Strong.strongScale t=W*Strong.strongScale t+(Z+1)*Strong.strongScale t by ring,
          Real.exp_add]
        ring


theorem varying_width_transfer_trace_compression (he : Function.Even K)
    (A : ℝ→AutomorphicSpace 0→L[ℂ]AutomorphicSpace N) (Z : ℝ) (hZ : 0≤Z)
    (hA : ∀ᶠ t in atTop,‖A t‖^2≤Real.exp (Z*Strong.strongScale t))
    (Dinput W : ℝ) (hDi : 0≤Dinput)
    (width : ℝ→ℝ)
    (hwidth : ∀ᶠ t in atTop,1≤width t ∧ width t≤Real.exp (Dinput*Strong.strongScale t))
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hcols : ∀ᶠ t in atTop,MemLp (fun x => A t (cylinderAutomorphic (column K hc he ε t x)))
      2 (quotientMeasure 0))
    (T : ℝ→Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
    (hT : ∀ᶠ t in atTop,‖T t‖≤1) :
    ∃ D : ℝ,Dinput≤D ∧ 0<D ∧
      Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
        newtonTraceDifferenceAtWidth K hc S hδ hν χ he ε (A t) T (width t) D t/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨Cdim,hCdim,hcount⟩ := fullBand_wide_finrank_bound N hN
  obtain ⟨D,hDiD,hD,herr⟩ := varying_width_transfer_newton_limit K hc S hδ hν χ he A Z hA
    Dinput (W+(|W|+(Dinput+Z+1)+1)) hDi width hwidth ε hε hproduct hcols
  refine ⟨D,hDiD,hD,?_⟩
  apply weighted_trace_from_energy ε
    (fun t => newtonColumnErrorAtWidth K hc S hδ hν χ he ε (A t) (width t) D t)
    (fun t => newtonTraceDifferenceAtWidth K hc S hδ hν χ he ε (A t) T (width t) D t)
    Cdim (Dinput+Z+1) W hCdim.le (by linarith)
    (hε.mono (fun _ h => h.1)) hproduct
    (Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))) herr
  filter_upwards [hT,packet_scheduled_norm K hc ε hε hproduct,hA,hcols,
    Strong.exponential_band_width_quarter Dinput hDi,eventually_ge_atTop (6:ℝ),hwidth] with t hTt hp hAt hct hBt ht hwt
  let B := width t
  let Bouter := WideInput.radius B (Real.exp (D*Strong.strongScale t))
    (inverseSqrtPolynomial (Strong.bandNewtonDepth t)).natDegree
  let η := Real.exp (-((|W|+(Dinput+Z+1)+1)*Strong.strongScale t))
  have hη : 0<η := Real.exp_pos _
  have hBB : B≤Bouter := WideInput.radius_mono B _ (Real.exp_pos _).le (Nat.zero_le _)
  have htrace := WideInput.reconstruction_column_trace S hδ hν χ t B Bouter hBB
    (Strong.bandNewtonDepth t) (A t) (time K hc ε t) (time_compact K hc ε t)
    (time_even K hc he ε t) (time_real K hc he ε t)
    (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    (time_support K hc ε t) hct (T t) η hη
  have hm : (‖cylinderTimePacket (time K hc ε t) ((time K hc ε t).smooth ⊤)
      (time_compact K hc ε t)‖*‖A t‖)^2*(Module.finrank ℂ (S.band (t-B) (t+B)):ℝ)≤
      Cdim*t*Real.exp ((Dinput+Z+1)*Strong.strongScale t) := by
    calc
      _ ≤ (Real.exp (Strong.strongScale t)*Real.exp (Z*Strong.strongScale t))*(Cdim*t*B) := by
        rw [mul_pow]
        apply mul_le_mul
        · exact mul_le_mul hp hAt (sq_nonneg _) (Real.exp_pos _).le
        · exact hcount S t B ht hwt.1 (hwt.2.trans hBt.2)
        · positivity
        · positivity
      _ ≤ (Real.exp (Strong.strongScale t)*Real.exp (Z*Strong.strongScale t))*
          (Cdim*t*Real.exp (Dinput*Strong.strongScale t)) := by gcongr; exact hwt.2
      _ = _ := by rw [add_mul,add_mul,one_mul,Real.exp_add,Real.exp_add]; ring
  apply htrace.trans
  apply le_trans (mul_le_of_le_one_left (by positivity) hTt)
  exact add_le_add (mul_le_mul_of_nonneg_left hm hη.le) le_rfl

theorem varying_transfer_newton_limit (he : Function.Even K)
    (A : ℝ→AutomorphicSpace 0→L[ℂ]AutomorphicSpace N) (Z : ℝ)
    (hA : ∀ᶠ t in atTop,‖A t‖^2≤Real.exp (Z*Strong.strongScale t))
    (Dinput W : ℝ) (hDi : 0≤Dinput)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hcols : ∀ᶠ t in atTop,MemLp (fun x => A t (cylinderAutomorphic (column K hc he ε t x)))
      2 (quotientMeasure 0)) :
    ∃ D : ℝ,Dinput≤D ∧ 0<D ∧
      Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
        newtonColumnError K hc S hδ hν χ he ε (A t) Dinput D t/(t*ε t)) atTop (𝓝 0) := by
  exact varying_width_transfer_newton_limit K hc S hδ hν χ he A Z hA Dinput W hDi
    (fun t => Real.exp (Dinput*Strong.strongScale t))
    (Eventually.of_forall (fun t => ⟨Real.one_le_exp (mul_nonneg hDi (sq_nonneg _)),le_rfl⟩))
    ε hε hproduct hcols

theorem varying_transfer_trace_compression (he : Function.Even K)
    (A : ℝ→AutomorphicSpace 0→L[ℂ]AutomorphicSpace N) (Z : ℝ) (hZ : 0≤Z)
    (hA : ∀ᶠ t in atTop,‖A t‖^2≤Real.exp (Z*Strong.strongScale t))
    (Dinput W : ℝ) (hDi : 0≤Dinput)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hcols : ∀ᶠ t in atTop,MemLp (fun x => A t (cylinderAutomorphic (column K hc he ε t x)))
      2 (quotientMeasure 0))
    (T : ℝ→Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
    (hT : ∀ᶠ t in atTop,‖T t‖≤1) :
    ∃ D : ℝ,Dinput≤D ∧ 0<D ∧
      Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
        newtonTraceDifference K hc S hδ hν χ he ε (A t) T Dinput D t/(t*ε t)) atTop (𝓝 0) := by
  exact varying_width_transfer_trace_compression K hc S hδ hν χ he A Z hZ hA Dinput W hDi
    (fun t => Real.exp (Dinput*Strong.strongScale t))
    (Eventually.of_forall (fun t => ⟨Real.one_le_exp (mul_nonneg hDi (sq_nonneg _)),le_rfl⟩))
    ε hε hproduct hcols T hT

#print axioms varying_width_transfer_trace_compression
#print axioms varying_transfer_newton_limit
#print axioms varying_transfer_trace_compression
end QuantitativeMaass.Scheduled
