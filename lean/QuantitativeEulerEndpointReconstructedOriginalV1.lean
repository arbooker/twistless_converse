module

public import QuantitativeEulerEndpointSectorTerminalOriginalV1
public import QuantitativeSpectralObservabilityReconstructedSourceV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory QuantitativeEulerDensityGenerators
open AsymptoticSectorSigns AsymptoticOrbitDiagonal AsymptoticRegularReconstruction
open FinitenessCertificate FinitenessGlobalHeight QuantitativeHolomorphic
open QuantitativeSpectralObservability QuantitativeSpectralFiniteReduction QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

/-- Original-row observability on the actual normalized reconstruction source.
The certificate constant is independent of weight and block length. Lower
heights are reconstructed rather than discarded. The three displayed tails
are exact rows to be removed by the regular trace argument. -/
theorem exists_reconstructed_sector_original_observability {N Q : ℕ} [NeZero N]
    {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let U := normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P sector
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], D₀.Good q →
      ∃ hqN : ¬q∣N, ∀ (H : ℝ), max P'.ε⁻¹ 4≤H →
      (∀ i, sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      ∀ (x : ℍ), fundamentalGood N x → ∀ v : Space,
      v∈TerminalSpace A P' x →
      corner (AsymptoticCertificateOperators.highStrip P'.ε\AsymptoticHyperbolicArea.terminal P'.ε) x (U x v)=0 →
      corner (AsymptoticHyperbolicArea.terminal H) x (U x v)=0 →
      quotientTailStack N (fun i => H/sectorFamilyC N (NeZero.pos N) sector S hS i) P'.epsilon_pos
        (by omega : 1≤P'.s+4) (sectorFamilySampled N (NeZero.pos N) sector H P'.epsilon_pos
          (by omega : 1≤P'.s+4)) x (U x v)=0 →
      let Y := min P'.ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min P'.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant D₀*C)*(q : ℝ)^4
      let hs := wideFreshRegion_compact L R R hZ
      ‖v‖^2≤(countReconstructionBound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P'.ε (P'.s+4)*
          (K*((wideDistortion L R R)^(P'.s+4))^2*
            primeOldOriginalEnergy sector q hqN hs P'.epsilon_pos (P'.s+4) x (U x v)+
            ‖sectorSampling N (NeZero.pos N) sector H P'.epsilon_pos
              (by omega : 1≤P'.s+4) x (U x v)‖^2) := by
  dsimp only
  let P' := AsymptoticReconstructedCount.parameters A P
  let U := normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P sector
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hobs⟩ :=
    exists_sector_terminal_original_observability D₀ hN2 sector S hS P'.epsilon_pos
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hgood
  obtain ⟨hqN,hobs⟩ := hobs C hBC q hgood
  refine ⟨hqN,?_⟩
  intro H hH hdata x hx v hv hboundary hupper htail
  have hn := terminal_input_le_reconstructed_terminal A (NeZero.pos N) P sector x v hv
  rw [closed_terminal_corner_of_boundary_zero P'.ε x (U x v) hboundary] at hn
  have hn2 := pow_le_pow_left₀ (norm_nonneg v) hn 2
  rw [mul_pow] at hn2
  have ho := hobs H hH hdata (P'.s+4) (by omega) x hx (U x v) hupper htail
  have hh := mul_le_mul_of_nonneg_left ho (sq_nonneg (countReconstructionBound A P))
  exact hn2.trans (hh.trans_eq (by ring))

#print axioms exists_reconstructed_sector_original_observability
end QuantitativeEulerEndpointPrepared
