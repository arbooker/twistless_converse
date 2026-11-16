module

public import QuantitativeMaassMajorantDifferenceCompressionV1
public import QuantitativeMaassMajorantCanonicalBandObservationV1
public import QuantitativeMaassMajorantCuspidalSectorTraceV1
public import QuantitativeMaassMajorantAmbientCanonicalTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter MeasureTheory ContinuousLinearMap QuantitativeNinaMaass AsymptoticSectorSigns
open AsymptoticClassicalPetersson QuantitativeArithmeticRepeatedTwoBands
open QuantitativeArithmeticNewBandProjections
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled
local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (p : ↥N.primeFactors) : NeZero p.val :=
  ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
local instance (N : ℕ) [NeZero N] (p : ↥N.primeFactors) : NeZero (N/p.val) :=
  ⟨(prime_quotient_pos N p.val (NeZero.pos N)
    (Nat.prime_of_mem_primeFactors p.property) (Nat.dvd_of_mem_primeFactors p.property)).ne'⟩

/-- The original completed canonical projection on full moving-cutoff
columns has the same regular counting main term. Filter and canonical
traces are compressed together, so no spectral-band compatibility is assumed.
The cutoff mass remains explicit for subsequent excess cancellation. -/
theorem originalMajorant_full_canonical_main_decay {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (T : CuspEnergySpectrum N hN)
    (S : ∀ q : ↥N.primeFactors, CuspEnergySpectrum (N/q.val)
      (prime_quotient_pos N q.val hN (Nat.prime_of_mem_primeFactors q.property)
        (Nat.dvd_of_mem_primeFactors q.property)))
    (e : Sector N) (σ : ℝ) (hσ : σ^2=1)
    (δ C D : ℝ) (hδ : 0<δ) (hC : 0≤C) (hD : 0≤D)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    Tendsto (fun t =>
      let c := fun z => cutoffTransfer N (movingLowerEdge δ C ε t) D t
        (movingLowerEdge_pos hδ C ε t) (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))
      Real.exp (W*Strong.strongScale t)*
        (columnLinearTrace (quotientMeasure 0) c
          (completedNewSignParitySpace N hN (sectorCharacter N hN e) σ).starProjection-
          originalMajorantSectorProjectionMain N hN e δ C D hδ K hc ε t/2)/(t*ε t))
      atTop (𝓝 0) := by
  let χ := sectorCharacter N hN e
  let Q := (completedNewSignParitySpace N hN χ σ).starProjection
  let F := fun t => ambientSectorNewFilter N hN e (growingLVDegree t)
  obtain ⟨M,hM,hbound⟩ := ambientSectorNewFilter_uniform_norm N hN
  obtain ⟨B,hB,hcomp⟩ := originalMajorant_difference_cutoff_exact_band_compression N hN T.basis T.energy
    T.energy_nonneg T.graph δ C D hδ hC hD K hc he hK hm ε hε hp F
    (fun _ => parityProjection N σ) M (zero_lt_one.trans_le hM)
    (Eventually.of_forall (fun t => hbound e (growingLVDegree t)))
    (Eventually.of_forall (fun _ => parityProjection_norm_le_one N σ hσ)) Q
    (completedNewSignParitySpace N hN χ σ).starProjection_norm_le
    (canonicalParityProjection_cusp_left N hN χ σ)
    (canonicalParityProjection_cusp_right N hN χ σ) W
  have hcan := originalMajorantBand_ambientCanonical_trace_limit N hN T S σ e hδ hAd hσ
    B W C D hB.le hC K hc he hK hm ε hε hp
  have hband : Tendsto (fun t =>
      let w := originalMajorantBandColumn N hN T.basis T.energy T.energy_nonneg T.graph δ C D hδ
        K hc he ε (exactBandParameter B t) t
      Real.exp (W*Strong.strongScale t)*
        (columnLinearTrace (quotientMeasure 0) (fun z => F t (w z)) (parityProjection N σ)-
         columnLinearTrace (quotientMeasure 0) w Q)/(t*ε t)) atTop (𝓝 0) := by
    apply hcan.congr'
    filter_upwards [originalMajorantBand_filtered_parity_eq N hN T σ hσ e δ C D B hδ hB K hc he ε,
      originalMajorantBand_canonical_parity_eq N hN T σ hσ χ δ C D B hδ hB K hc he ε] with t hf hq
    dsimp only [F,Q]
    rw [hf,hq]
  have htrace := originalMajorant_cuspidal_sector_trace_decay basis N p hN hAd hpN hNp hpres a b hab
    e σ hσ δ C D hδ hC hD K hc he hK hm ε hε hp W
  have hdiff := hcomp.add hband
  rw [add_zero] at hdiff
  have hh := htrace.sub hdiff
  rw [sub_zero] at hh
  convert hh using 1
  funext t
  dsimp only [F,Q,χ,localCuspidalProjection]
  ring

#print axioms originalMajorant_full_canonical_main_decay
end QuantitativeMaass.Scheduled
