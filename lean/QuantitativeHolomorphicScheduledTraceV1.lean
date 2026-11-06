module

public import QuantitativeHolomorphicSimultaneousCutoffsV1
public import QuantitativeHolomorphicCutoffComplexityV1
public import QuantitativeHolomorphicUpperCutoffScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount AsymptoticFiniteBranch AsymptoticRegularTrace MeasureTheory
open AsymptoticUnweightedKernel

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) {ι : Type*}

/-- The literal sector trace assembly with all four reconstruction cutoffs
selected from the target error. Only the separate upper height and branch
geometry thresholds remain; no reconstruction-error assumption survives. -/
theorem sector_finrank_le_scheduled_source_trace (hN : 0<N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    {L U : ℝ} (hL : 0<L)
    (hre : ∀ i z, z∈s i → |z.re|≤1) (hlo : ∀ i z, z∈s i → L≤z.im)
    (hhi : ∀ i z, z∈s i → z.im≤U) (d : ℕ) {t : ℝ} (ht : 0<t) (ht1 : t≤1) :
    let D : ℝ := 2*d+2
    let n := newtonDepth A P D t
    let j := reconstructionDepth A P D t n
    let J := foldCutoff A P D t j n
    let Y := lowerCutoff A P D t n
    ∀ H : ℝ, 0<H → ∀ S : Finset ℤ,
      (h+1:ℝ)^(-(1/3:ℝ)) *
        (quantifiedFilterMatrixHeight A hN qs r L U j J n d*(H+2))≤1 →
      (∀ a : ℤ, a∉S → 2*compactBaseBound Y H 1≤1+|(a:ℝ)|) →
      let P' := AsymptoticReconstructedCount.parameters A P
      (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)/(2*h+2:ℝ) ≤
        signedTrace volume (fun z => (regularSourceFilter A hN P e qs r s hs d z).comp
          (AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P'.ε) z))/(4*Real.pi) +
        Terminal.closedSectorTraceError A hN P h qs r L U Y H j J n d S.card := by
  let D : ℝ := 2*d+2
  let n := newtonDepth A P D t
  let j := reconstructionDepth A P D t n
  let J := foldCutoff A P D t j n
  let Y := lowerCutoff A P D t n
  dsimp only
  intro H hH S hsmall hfar
  have hc := countFilterError_schedule A P d ht
  exact Terminal.sector_finrank_le_regular_source_trace_closed A hN P h e qs r s hs
    hL hre hlo hhi Y H hc.2.1 hH j J n d hc.1 hc.2.2.1 (hc.2.2.2.trans ht1) S hsmall hfar

#print axioms sector_finrank_le_scheduled_source_trace

end QuantitativeHolomorphic.Schedule
