module

public import QuantitativeEulerEndpointNewGeometryCheckV1
public import QuantitativeSpectralObservabilityNewTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open AsymptoticRegularBranchFamily AsymptoticRegularObservationRows AsymptoticObservationStack
open QuantitativeSpectralObservability QuantitativeSpectralExceptionalReducedRows QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

def primeOldRegion (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (ε H : ℝ) : Set ℍ :=
  enlargedRegion (fun i => oldBranches (primeOldRepresentatives N hN i))
    (fun i => (primeOldData N hN S hS i).w)
    (fun i => wideCompactCover N (H/(primeOldData N hN S hS i).C)) (wordRegion W ε H)

theorem primeOldRegion_compact (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) {ε : ℝ} (hε : 0<ε) (H : ℝ) :
    IsCompact (primeOldRegion N hN S hS W ε H) :=
  enlargedRegion_compact (fun i => oldBranches (primeOldRepresentatives N hN i))
    (fun i => (primeOldData N hN S hS i).w)
    (fun i => wideCompactCover N (H/(primeOldData N hN S hS i).C))
    (fun i => wideCompactCover_compact N hN (H/(primeOldData N hN S hS i).C))
    (wordRegion_compact W hε H)

def primeOldRowsEnergy (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (H : ℝ) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (v : Space) : ℝ :=
  ∑ i : PrimeOldIndex N, ‖family (oldBranches (primeOldRepresentatives N hN i))
    (oldCoefficients (I:=PrimeOldClasses N hN i) N (primeOldGroup N hN i))
    (primeOldRegion_compact N hN S hS W hε H) hε t x v‖^2

/-- The actual total-new detector has its congruence part controlled by
original Euler observations, on one explicit region of polynomial size.
The original old-row energy remains visible and is not assumed zero. -/
theorem primeOldDetector_original_energy {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) :
    ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (ε : ℝ) (hε : 0<ε) (H : ℝ), 0≤H → ∀ (C : ℝ), B≤C →
      ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (w : ℂ), w*w=1 → ∀ (t : ℕ) (x : ℍ) (v : Space),
      let Y := min ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min hε (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      let hs := wideFreshRegion_compact L R R hZ
      ‖primeOldDetector N (NeZero.pos N) S hS W H hε t x v‖^2≤
        primeOldRowsEnergy N (NeZero.pos N) S hS W H hε t x v+
        K*((wideDistortion L R R)^t)^2*
          (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w hs hε t x v‖^2+
            ‖fixedPrimeStack N w hs hε t x v‖^2+
            ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
              hs hε t i x) v‖^2) := by
  obtain ⟨Bg,hBg,D,hD,hgeo⟩ := enlarged_new_region_geometry N W
    (fun i => oldBranches (primeOldRepresentatives N (NeZero.pos N) i))
    (fun i => (primeOldData N (NeZero.pos N) S hS i).w)
    (fun i => (primeOldData N (NeZero.pos N) S hS i).C)
  obtain ⟨B,hB,K,hK,hbound⟩ := wide_enlarged_detector_bound P (signedGenerators S)
    (signedGenerator_mem_gamma N S hS)
  refine ⟨Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro ε hε H hH C hBC q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := hbound C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro w hw t x v
  have hregion := hgeo ε hε H hH
  have hZ := div_pos (lt_min hε (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
  exact hqbound
    (fun i => oldBranches (primeOldRepresentatives N (NeZero.pos N) i))
    (fun i => oldCoefficients (I:=PrimeOldClasses N (NeZero.pos N) i) N
      (primeOldGroup N (NeZero.pos N) i))
    w hw (primeOldRegion_compact N (NeZero.pos N) S hS W hε H) hε hZ
    (fun z hz => (hregion hz).1) (fun z hz => (hregion hz).2.1)
    (fun z hz => (hregion hz).2.2) t x v

#print axioms primeOldRegion_compact
#print axioms primeOldDetector_original_energy
end QuantitativeEulerEndpointPrepared
