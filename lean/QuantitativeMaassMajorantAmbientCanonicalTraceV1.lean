module

public import QuantitativeMaassMajorantSectorTraceV1
public import QuantitativeArithmeticMaassMovingCanonicalTraceV1
public import QuantitativeNinaMaassParityBandProjectionV1
public import QuantitativeMaassAmbientSectorNewFilterV1

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap
open QuantitativeNinaMaass AsymptoticClassicalPetersson AsymptoticSectorSigns
open QuantitativeNewGap QuantitativeArithmeticRepeatedTwoBands QuantitativeArithmeticNewBandProjections
open QuantitativeArithmeticNewBandProduct
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled
local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance




local instance (N : ℕ) (p : ↥N.primeFactors) : NeZero p.val :=
  ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩

local instance (N : ℕ) [NeZero N] (p : ↥N.primeFactors) : NeZero (N/p.val) :=
  ⟨(prime_quotient_pos N p.val (NeZero.pos N)
    (Nat.prime_of_mem_primeFactors p.property) (Nat.dvd_of_mem_primeFactors p.property)).ne'⟩

local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (T : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    CompleteSpace (T.parityBand a b σ) := FiniteDimensional.complete ℂ _

local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (T : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (K : Submodule ℂ (T.parityBand a b σ)) : K.HasOrthogonalProjection := by
  let : CompleteSpace K := FiniteDimensional.complete ℂ _
  infer_instance



local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (K : Submodule ℂ (S.parityBand a b σ)) :
    CompleteSpace K := FiniteDimensional.complete ℂ _



local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b

variable (N : ℕ) [NeZero N] (hN : 0<N) (T : CuspEnergySpectrum N hN)
    (S : ∀ p : ↥N.primeFactors, CuspEnergySpectrum (N/p.val)
      (prime_quotient_pos N p.val hN (Nat.prime_of_mem_primeFactors p.property)
        (Nat.dvd_of_mem_primeFactors p.property))) (σ : ℝ) (e : Sector N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)



/-- The filtered finite-band trace approximates the actual completed
canonical new/sign/parity trace on the moving-cutoff wave columns. -/
theorem originalMajorantBand_originalCanonical_trace_limit
    (hAd : GridAdmissibleGap.Admissible N) (hσ : σ^2=1)
    (B W C D : ℝ) (hB : 0≤B) (hC : 0≤C)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      let a := t-Real.exp (B*Strong.strongScale t)
      let b := t+Real.exp (B*Strong.strongScale t)
      let c := originalMajorantParityColumn N hN T σ hδ K hc he ε B C D t
      let F := sectorParityBandFilter N hN T S a b σ e (growingLVDegree t)
      Real.exp (W*Strong.strongScale t)*
        (columnLinearTrace (quotientMeasure 0) (fun z => inclusion T a b σ (F (c z))) 1-
         columnLinearTrace (quotientMeasure 0) (fun z => inclusion T a b σ (c z))
           (completedNewSignParitySpace N hN (sectorCharacter N hN e) σ).starProjection)/(t*ε t))
      atTop (𝓝 0) := by
  have hh := originalMajorant_canonicalSector_trace_limit N hN T S σ e hδ hAd B W C D hB hC K hc he hK hm ε hε hp
  convert hh using 1
  funext t
  dsimp only
  rw [canonicalParityColumn_trace_eq N hN T σ e hAd _ _ hσ]
  rfl

include S in
/-- The comparison uses the actual basis-independent finite polynomial
in cover, trace, Fricke and sector-normalizer operators. -/
theorem originalMajorantBand_ambientCanonical_trace_limit
    (hAd : GridAdmissibleGap.Admissible N) (hσ : σ^2=1)
    (B W C D : ℝ) (hB : 0≤B) (hC : 0≤C)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      let a := t-Real.exp (B*Strong.strongScale t)
      let b := t+Real.exp (B*Strong.strongScale t)
      let c := originalMajorantParityColumn N hN T σ hδ K hc he ε B C D t
      let F := ambientSectorNewFilter N hN e (growingLVDegree t)
      Real.exp (W*Strong.strongScale t)*
        (columnLinearTrace (quotientMeasure 0) (fun z => F (inclusion T a b σ (c z))) 1-
         columnLinearTrace (quotientMeasure 0) (fun z => inclusion T a b σ (c z))
           (completedNewSignParitySpace N hN (sectorCharacter N hN e) σ).starProjection)/(t*ε t))
      atTop (𝓝 0) := by
  have hh := originalMajorantBand_originalCanonical_trace_limit N hN T S σ e hδ hAd hσ B W C D hB hC
    K hc he hK hm ε hε hp
  convert hh using 1
  funext t
  dsimp only
  have hf (x : T.parityBand (t-Real.exp (B*Strong.strongScale t))
      (t+Real.exp (B*Strong.strongScale t)) σ) :
      inclusion T _ _ σ (sectorParityBandFilter N hN T S _ _ σ e (growingLVDegree t) x)=
        ambientSectorNewFilter N hN e (growingLVDegree t) (inclusion T _ _ σ x) :=
    ambientSectorNewFilter_band N hN T S _ _ σ e (growingLVDegree t) x
  simp only [hf]

#print axioms originalMajorantBand_originalCanonical_trace_limit
#print axioms originalMajorantBand_ambientCanonical_trace_limit
end QuantitativeMaass.Scheduled
