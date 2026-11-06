module

public import QuantitativeEulerEndpointSectorFullDetectorV1
public import QuantitativeSpectralObservabilityNewTerminalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane ContinuousLinearMap AsymptoticOrbitDiagonal AsymptoticSectorSigns
open AsymptoticCongruenceQuotient AsymptoticRegularBranchFamily
open QuantitativeSpectralObservability QuantitativeSpectralExceptionalReducedRows
open QuantitativeSpectralFiniteReduction
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

/-- The literal sector sampler controls the terminal part of ANY input.
The input itself need not be supported in a terminal band, so this estimate
can be applied to the actual reconstruction used by finite-count filters. -/
theorem exists_sector_terminal_observability (N : ℕ) (hN : 0<N) (sector : Sector N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (B : ℝ), 1≤B ∧
      ∀ H : ℝ, max ε⁻¹ 4≤H → (∀ i, sectorFamilyB N hN sector S hS i≤H) →
      ∀ (t : ℕ) (ht : 1≤t) (x : ℍ), fundamentalGood N x → ∀ u : Space,
      corner (AsymptoticHyperbolicArea.terminal H) x u=0 →
      quotientTailStack N (fun i => H/sectorFamilyC N hN sector S hS i) hε ht
        (sectorFamilySampled N hN sector H hε ht) x u=0 →
      ‖corner (AsymptoticHyperbolicArea.terminal ε) x u‖^2≤
        sectorObservationCost N hN sector S hS W B H ε t*
          (‖sectorDetector N hN sector S hS W H hε t x u‖^2+
            ‖sectorSampling N hN sector H hε ht x u‖^2) := by
  let b := sectorFamilyBranches N hN
  let c := sectorFamilyCoefficients N hN sector
  let w := sectorFamilyWords N hN sector S hS
  let regions := fun H i => wideCompactCover N (H/sectorFamilyC N hN sector S hS i)
  let hs := fun H i => wideCompactCover_compact N hN (H/sectorFamilyC N hN sector S hS i)
  obtain ⟨W,B,hB,_hW,hobs⟩ :=
    exists_enlarged_terminal_observability N hN S hS b w c regions hs hε
  refine ⟨W,B,hB,?_⟩
  intro H hH hdata t ht x hx u hupper htail
  have ho := hobs H hH t ht x hx u
  dsimp only at ho
  rw [hupper,norm_zero,zero_pow (by omega),add_zero] at ho
  have hsum := terminal_word_sum_bound S W B H
    ‖AsymptoticObservationStack.stack (enlargedRows (signedGenerators S) b c
      (enlargedRegion_compact b w (regions H) (hs H) (wordRegion_compact W hε H)) hε t x) u‖
    ‖fundamentalSampling N hN H hε ht x u‖ t
  have ho' := ho.trans hsum
  rw [← enlargedDetector_norm_apply] at ho'
  have hg := sectorSampling_distance_le_detector N hN sector S hS hdata
    (wordRegion_compact W hε H) hε ht x u htail
  have hK : 0≤terminalObservationConstant S W*(1+B^2*(H+3)^2)^(2*t) := by
    have hL := zero_le_one.trans (terminalObservationConstant_ge_one S W)
    positivity
  have hA : 0≤(sectorGap N hN)⁻¹*∑ i,(sectorFamilyCost N hN sector S hS H ε t i)^2 :=
    mul_nonneg (inv_nonneg.mpr (sectorGap_pos N hN).le) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact observability_projected (AsymptoticQuotientIncidence.space N hN hε ht sector x)
    (corner (AsymptoticHyperbolicArea.terminal ε) x u)
    (fundamentalSampling N hN H hε ht x u) _ _ _ hK hA ho' hg

#print axioms exists_sector_terminal_observability
end QuantitativeEulerEndpointPrepared
