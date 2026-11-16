module

public import QuantitativeMaassSharpWindowComparisonV1
public import QuantitativeMaassLogPowerLeakageLimitV1
public import QuantitativeMaassTrimmedIdentityLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip
open scoped Topology SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- Scalar form of the proved exceptional spectral negligibility. -/
theorem exceptional_window_scalar_flexible_negligible {ι : Type*}
    (N : ℕ) (hN : 0<N) (K : SchwartzMap ℝ ℝ) (hKe : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (ε R a b : ℝ → ℝ) (hRp : ∀ t,0<R t)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0))
    (hab : ∀ᶠ t in atTop,a t≤b t ∧ b t-a t≤1) :
    Tendsto (fun t => (∑' i : {i // e i≤1/4},
      ‖smoothPacketMultiplier (windowTimeSchwartz K hc (R t) (hRp t) (a t) (b t)) (e i.val)‖^2)/(t*ε t))
      atTop (𝓝 0) := by
  have hh := windowWavePacket_exceptional_flexible_negligible N hN K hKe hc v hv hcusp e he hgraph
    ε R a b hRp hε hproduct hRlog hab
  apply hh.congr
  intro t
  congr 1
  apply tsum_congr
  intro i
  exact windowWavePacket_diagonal_scalar N K hKe hc _ (hRp t) _ _ _ (hv.norm_eq_one i.val)
    _ (he i.val) (hgraph i.val)

/-- Removing the smoothing loses only an arbitrarily small normalized error,
for every bounded nonnegative weight on an actual cusp energy family. -/
theorem window_weighted_sharp_eventual {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he0 : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (w : ι → ℝ) (hw : ∀ i,w i∈Icc (0:ℝ) 1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (c : ℝ) (hc0 : 0<c) (hc1 : c<1) (η : ℝ) (hη : 0<η) :
    ∀ᶠ t in atTop,
      (∑' i,‖smoothPacketMultiplier (windowTimeSchwartz K hc (logPowerRadius c t)
        (logPowerRadius_pos c t) (t+logPowerMargin c t) (t+ε t-logPowerMargin c t)) (e i)‖^2*w i)/(t*ε t)
        <principalWindowWeight e w t (t+ε t)/(t*ε t)+η := by
  have hp := principal_trimmed_leakage_logPower_negligible N hN v hv hcusp e he0 hgraph K hK c hc0 ε hε hproduct
  have hab : ∀ᶠ t in atTop,
      t+logPowerMargin c t≤t+ε t-logPowerMargin c t ∧
      (t+ε t-logPowerMargin c t)-(t+logPowerMargin c t)≤1 := by
    filter_upwards [hε,(logPowerMargin_trim_parameters c hc0 ε (hε.mono (fun _ h => h.1)) hproduct).1] with t ht hd
    constructor <;> linarith [hd.1,hd.2,ht.2]
  have hexc := exceptional_window_scalar_flexible_negligible N hN K he hc v hv hcusp e he0 hgraph
    ε (logPowerRadius c) (fun t => t+logPowerMargin c t) (fun t => t+ε t-logPowerMargin c t)
    (logPowerRadius_pos c) (hε.mono (fun _ h => h.1)) hproduct (logPowerRadius_div_log c hc0 hc1) hab
  have hlim := hp.add hexc
  rw [zero_add] at hlim
  have hnear := hlim.eventually (gt_mem_nhds hη)
  filter_upwards [hnear,hε,eventually_gt_atTop (0:ℝ)] with t hnear ht htp
  have hb := (window_weighted_sharp_comparison N hN v hv hcusp e he0 hgraph w hw K he hc hK hm
    t (ε t) (logPowerMargin c t) (logPowerRadius c t) htp ht.2 (logPowerMargin_pos _ _)
    (logPowerMargin_le_one _ _) (logPowerRadius_pos _ _)).2
  have hdiv := div_le_div_of_nonneg_right hb (mul_pos htp ht.1).le
  dsimp only at hdiv hnear
  rw [add_div,add_div] at hdiv
  linarith only [hdiv,hnear]

#print axioms exceptional_window_scalar_flexible_negligible
#print axioms window_weighted_sharp_eventual

end QuantitativeMaass
