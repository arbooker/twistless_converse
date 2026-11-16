module

public import QuantitativeMaassMajorantSectorProjectionTraceV1
public import QuantitativeMaassMovingCuspidalSectorTraceV1
public import QuantitativeMaassMajorantNoncuspidalTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter MeasureTheory ContinuousLinearMap AsymptoticSectorSigns
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

namespace Scheduled

/-- The same regular main term is valid after restricting the actual
moving-cutoff input to the cuspidal subspace. -/
theorem originalMajorant_cuspidal_sector_trace_decay {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (e : Sector N) (σ : ℝ) (hσ : σ^2=1)
    (δ P D : ℝ) (hδ : 0<δ) (hP : 0≤P) (hD : 0≤D)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    Tendsto (fun t =>
      let c := fun z => cutoffTransfer N (movingLowerEdge δ P ε t) D t
        (movingLowerEdge_pos hδ P ε t) (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))
      let F := ambientSectorNewFilter N hN e (growingLVDegree t)
      Real.exp (W*Strong.strongScale t)*
        (columnLinearTrace (quotientMeasure 0)
          (fun z => F (localCuspidalProjection N hN (c z))) (parityProjection N σ)-
          originalMajorantSectorProjectionMain N hN e δ P D hδ K hc ε t/2)/(t*ε t))
      atTop (𝓝 0) := by
  let F := fun t => ambientSectorNewFilter N hN e (growingLVDegree t)
  obtain ⟨C,_hC,hbound⟩ := ambientSectorNewFilter_uniform_norm N hN
  have hF : ∀ᶠ t in atTop,‖F t‖^2≤Real.exp (1*Strong.strongScale t) := by
    filter_upwards [(Real.tendsto_exp_atTop.comp Strong.strongScale_tendsto).eventually
      (eventually_ge_atTop (C^2))] with t ht
    change C^2 ≤ Real.exp (Strong.strongScale t) at ht
    rw [one_mul]
    exact (pow_le_pow_left₀ (norm_nonneg (F t)) (hbound e (growingLVDegree t)) 2).trans ht
  have hremove := originalMajorant_filtered_noncuspidal_trace_decay N p hN hpN hNp hpres a b hab
    δ P D hδ hP hD K hc he hK hm ε hε hp F 1 W hF
    (fun _ => parityProjection N σ)
    (Eventually.of_forall (fun _ => parityProjection_norm_le_one N σ hσ))
  have htrace := originalMajorant_sector_projection_trace_decay basis N hN hAd e σ δ P D hδ hP
    K hc he hK hm ε hε hp W
  have hh := htrace.sub hremove
  rw [sub_zero] at hh
  convert hh using 1
  funext t
  dsimp only [F]
  ring

#print axioms originalMajorant_cuspidal_sector_trace_decay
end Scheduled
end QuantitativeMaass
