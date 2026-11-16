module

public import QuantitativeMaassMajorantFullCanonicalMainV1
public import QuantitativeMaassCanonicalProjectionSumV1
public import QuantitativeMaassMajorantSharpProjectionMainV1
public import QuantitativeArithmeticMaassMajorantSmoothingTraceV1

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

/-- Summing the actual canonical parity traces retains the same spatial mass. -/
theorem originalMajorant_full_newSign_main_decay {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (T : CuspEnergySpectrum N hN)
    (S : ∀ q : ↥N.primeFactors, CuspEnergySpectrum (N/q.val)
      (prime_quotient_pos N q.val hN (Nat.prime_of_mem_primeFactors q.property)
        (Nat.dvd_of_mem_primeFactors q.property)))
    (e : Sector N)
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
          (completedNewSignSpace N hN (sectorCharacter N hN e)).starProjection-
          originalMajorantSectorProjectionMain N hN e δ C D hδ K hc ε t)/(t*ε t))
      atTop (𝓝 0) := by
  have hp1 := originalMajorant_full_canonical_main_decay basis N p hN hAd hpN hNp hpres a b hab T S
    e 1 (by norm_num) δ C D hδ hC hD K hc he hK hm ε hε hp W
  have hm1 := originalMajorant_full_canonical_main_decay basis N p hN hAd hpN hNp hpres a b hab T S
    e (-1) (by norm_num) δ C D hδ hC hD K hc he hK hm ε hε hp W
  have hh := hp1.add hm1
  rw [add_zero] at hh
  convert hh using 1
  funext t
  dsimp only
  rw [columnLinearTrace_canonical_sum (quotientMeasure 0) N hAd e 1 (by norm_num) _
    (originalMajorant_cutoff_memLp N hδ C D K hc he ε t)]
  ring

/-- The sharp canonical trace has precisely the same regular main term,
including the rectangle mass, for cancellation in the source excess. -/
theorem originalMajorant_sharp_newSign_main_decay {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (T : CuspEnergySpectrum N hN)
    (S : ∀ q : ↥N.primeFactors, CuspEnergySpectrum (N/q.val)
      (prime_quotient_pos N q.val hN (Nat.prime_of_mem_primeFactors q.property)
        (Nat.dvd_of_mem_primeFactors q.property)))
    (e : Sector N)
    (δ C : ℝ) (hδ : 0<δ) (hC : 0≤C)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    Tendsto (fun t =>
      let c := fun z => sharpCutoffTransfer N (movingLowerEdge δ C ε t) t
        (movingLowerEdge_pos hδ C ε t) (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))
      Real.exp (W*Strong.strongScale t)*
        (columnLinearTrace (quotientMeasure 0) c
          (completedNewSignSpace N hN (sectorCharacter N hN e)).starProjection-
          originalMajorantSharpSectorProjectionMain N hN e δ C K hc ε t)/(t*ε t))
      atTop (𝓝 0) := by
  let Q := (completedNewSignSpace N hN (sectorCharacter N hN e)).starProjection
  obtain ⟨D,hD,hDW,hsmooth⟩ := originalMajorant_sharp_smooth_cutoff_trace_limit_with_margin
    K hc he hK hm ε hε hp N hδ C hC W (fun _ => Q)
    (Eventually.of_forall (fun _ => Submodule.starProjection_norm_le _))
  have hfull := originalMajorant_full_newSign_main_decay basis N p hN hAd hpN hNp hpres a b hab T S
    e δ C D hδ hC hD K hc he hK hm ε hε hp W
  have hmass := originalMajorant_sharp_projection_main_decay N hN e δ C D hδ hC
    K hc he hK hm ε hε hp W hD hDW
  have hmain : Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (originalMajorantSharpSectorProjectionMain N hN e δ C K hc ε t-
        originalMajorantSectorProjectionMain N hN e δ C D hδ K hc ε t)/(t*ε t)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hmass
    filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    simp only [norm_div,norm_mul,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),abs_of_pos ht,abs_of_pos heps.1,le_refl]
  have hh := (hsmooth.add hfull).sub hmain
  simp only [add_zero,sub_zero] at hh
  convert hh using 1
  funext t
  dsimp only [Q]
  ring

#print axioms originalMajorant_full_newSign_main_decay
#print axioms originalMajorant_sharp_newSign_main_decay
end QuantitativeMaass.Scheduled
