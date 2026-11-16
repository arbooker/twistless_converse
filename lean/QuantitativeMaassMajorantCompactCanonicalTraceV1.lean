module

public import QuantitativeMaassMajorantSharpCanonicalMainV1
public import QuantitativeArithmeticMaassCanonicalLocalTraceV1
public import QuantitativeMaassCappedColumnTraceV1
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

/-- Exact compact canonical trace with the original inverse metric and
finite inverse cap. Its sharp quotient representative has coefficient one. -/
theorem originalMajorant_compact_canonical_trace_eq
    (N : ℕ) [NeZero N] (hAd : GridAdmissibleGap.Admissible N)
    (cover : AdmissibleScalarCover N hAd) (e : Sector N)
    (δ C : ℝ) (hδ : 0<δ) (hC : 0≤C) (ν : ℕ) (hν : 1≤ν)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) (t : ℝ) :
    let R := C*radius ε t
    let J := ⌈(ν:ℝ)*R+1⌉₊
    let a := movingLowerEdge δ C ε t
    let S := cutoffRectangle a t
    let Pc := AsymptoticRegionL2.projection (quotientMeasure 0) S
      (upperRectangle_compact 0 1 a _ (movingLowerEdge_pos hδ C ε t)).measurableSet
    let L := (terminalInverseWeightBand δ ν J).comp (cover.metric hδ hν).change.symm.toContinuousLinearMap
    let Q := cover.physicalNewSignProjection hδ hν (sectorCharacter N hAd.1 e)
      (sectorCharacter_norm N hAd.1 e)
    columnLinearTrace (quotientMeasure 0) (fun z => Pc (originalMajorantColumn K hc he ε t z))
      (L.comp (Q.comp L.adjoint))=
      columnLinearTrace (quotientMeasure 0)
        (fun z => sharpCutoffTransfer N a t (movingLowerEdge_pos hδ C ε t)
          (cylinderAutomorphic (originalMajorantColumn K hc he ε t z)))
        (completedNewSignSpace N hAd.1 (sectorCharacter N hAd.1 e)).starProjection := by
  intro R J a S Pc L Q
  simpa only [Pc,L,Q,J,R,S,sharpCutoffTransfer,cutoffRectangle,
    terminalInverseWeightBand,LogBands.rowInverseSum,zero_sub,zero_add] using
    cover.physicalNewSignProjection_rectangle_trace hδ hν
      (sectorCharacter N hAd.1 e) (sectorCharacter_norm N hAd.1 e)
      (mul_nonneg hC (radius_pos ε t).le) a (Real.exp (Strong.strongScale t/2))
      (movingLowerEdge_pos hδ C ε t) (le_rfl : δ*Real.exp (-R)≤a)
      (quotientMeasure 0) (originalMajorantColumn K hc he ε t)

theorem originalMajorant_compact_canonical_main_decay {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (T : CuspEnergySpectrum N hN)
    (S : ∀ q : ↥N.primeFactors, CuspEnergySpectrum (N/q.val)
      (prime_quotient_pos N q.val hN (Nat.prime_of_mem_primeFactors q.property)
        (Nat.dvd_of_mem_primeFactors q.property)))
    (cover : AdmissibleScalarCover N hAd) (e : Sector N) (ν : ℕ) (hν : 1≤ν)
    (δ C : ℝ) (hδ : 0<δ) (hC : 0≤C)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    Tendsto (fun t =>
      let R := C*radius ε t
      let J := ⌈(ν:ℝ)*R+1⌉₊
      let a := movingLowerEdge δ C ε t
      let Ω := cutoffRectangle a t
      let Pc := AsymptoticRegionL2.projection (quotientMeasure 0) Ω
        (upperRectangle_compact 0 1 a _ (movingLowerEdge_pos hδ C ε t)).measurableSet
      let L := (terminalInverseWeightBand δ ν J).comp (cover.metric hδ hν).change.symm.toContinuousLinearMap
      let Q := cover.physicalNewSignProjection hδ hν (sectorCharacter N hAd.1 e)
        (sectorCharacter_norm N hAd.1 e)
      Real.exp (W*Strong.strongScale t)*
        (columnLinearTrace (quotientMeasure 0) (fun z => Pc (originalMajorantColumn K hc he ε t z))
          (L.comp (Q.comp L.adjoint))-
          originalMajorantSharpSectorProjectionMain N hN e δ C K hc ε t)/(t*ε t))
      atTop (𝓝 0) := by
  have hh := originalMajorant_sharp_newSign_main_decay basis N p hN hAd hpN hNp hpres a b hab T S
    e δ C hδ hC K hc he hK hm ε hε hp W
  convert hh using 1
  funext t
  dsimp only
  rw [originalMajorant_compact_canonical_trace_eq N hAd cover e δ C hδ hC ν hν K hc he ε t]

#print axioms originalMajorant_compact_canonical_trace_eq
#print axioms originalMajorant_compact_canonical_main_decay
end QuantitativeMaass.Scheduled
