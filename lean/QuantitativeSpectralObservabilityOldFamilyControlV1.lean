module

public import QuantitativeSpectralObservabilityOldResidualDataV1
public import QuantitativeSpectralObservabilityOldTailSurvivorV1
public import QuantitativeSpectralExceptionalStackDetectorV1

set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip
open AsymptoticRegularBranchFamily QuantitativeSpectralFiniteReduction
open AsymptoticObservationStack QuantitativeSpectralExceptionalReducedRows
open scoped MatrixGroups lp

variable {F : Type*} [Fintype F] {I : F → Type*} [∀ i, Fintype (I i)]

/-- The actual old-row energies are controlled simultaneously by the
single enlarged detector on the actual common tail kernel. All row
constants and word witnesses are supplied by `oldResidualData`. -/
theorem old_family_energy_le_detector
    (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (J : F → Subgroup OrbitGroup) (hJ : ∀ i, gamma N≤J i)
    [∀ i, Finite (J i ⧸ (gamma N).subgroupOf (J i))]
    (r : ∀ i, I i → J i) (d : ∀ i, OldResidualData N hN S (J i) (hJ i) (r i))
    {Y : ℝ} (hY : ∀ i, (d i).B≤Y) {u : Set ℍ} (hu : IsCompact u)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ))
    (hv : oldTailStack N hN J hJ Y (fun i => Y/(d i).C) hε ht x v=0) :
    let b := fun i => oldBranches (r i)
    let c := fun i => oldCoefficients (I:=I i) N (J i)
    let s := fun i => wideCompactCover N (Y/(d i).C)
    let hs := fun i => wideCompactCover_compact N hN (Y/(d i).C)
    let hu' := enlargedRegion_compact b (fun i => (d i).w) s hs hu
    ∑ i, ‖oldSampledRow N hN (J i) (hJ i) Y hε ht x v‖^2 ≤
      (∑ i, ((d i).L*(1+ε*(d i).K*(Y/(d i).C+3)^2)^(2*t))^2)*
        ‖enlargedDetector (signedGenerators S) b c hu' hε t x v‖^2 := by
  dsimp only
  rw [enlargedDetector_norm_apply,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hzero := (oldTailStack_eq_zero_iff N hN J hJ Y (fun i => Y/(d i).C) hε ht x v).mp hv i
  have hi := (d i).old_norm_le (hY i) hε ht x v hzero
  have hdom := commonResidualStack_norm_le_enlarged (signedGenerators S)
    (fun i => oldBranches (r i)) (fun i => (d i).w)
    (fun i => oldCoefficients (I:=I i) N (J i))
    (fun i => wideCompactCover N (Y/(d i).C))
    (fun i => wideCompactCover_compact N hN (Y/(d i).C)) hu hε t x i v
  have hL : 0≤(d i).L := zero_le_one.trans (d i).L_ge_one
  have hcost : 0≤(d i).L*(1+ε*(d i).K*(Y/(d i).C+3)^2)^(2*t) := by
    have hK : 0≤(d i).K := zero_le_one.trans (d i).K_ge_one
    positivity
  have hn := hi.trans (mul_le_mul_of_nonneg_left hdom hcost)
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2

#print axioms old_family_energy_le_detector

end QuantitativeSpectralObservability
