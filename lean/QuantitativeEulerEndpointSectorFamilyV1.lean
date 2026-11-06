module

public import QuantitativeEulerEndpointSectorSamplerV1
public import QuantitativeEulerEndpointQuotientTailStackV1
public import QuantitativeSpectralObservabilityOldFamilyControlV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticSectorSigns
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip AsymptoticRegularBranchFamily
open QuantitativeNewGap QuantitativeSpectralObservability QuantitativeSpectralExceptionalReducedRows
open AsymptoticObservationStack
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

abbrev SectorFamilyIndex (N : ℕ) := PrimeOldIndex N ⊕ SectorSignIndex N

def SectorFamilyBranchIndex (N : ℕ) (hN : 0<N) : SectorFamilyIndex N → Type
  | .inl i => PrimeOldClasses N hN i
  | .inr _ => Fin 2

instance sectorFamilyBranchIndex_fintype (N : ℕ) (hN : 0<N) (i : SectorFamilyIndex N) :
    Fintype (SectorFamilyBranchIndex N hN i) := by
  cases i <;> dsimp only [SectorFamilyBranchIndex] <;> infer_instance

def sectorFamilyBranches (N : ℕ) (hN : 0<N) : ∀ i : SectorFamilyIndex N, SectorFamilyBranchIndex N hN i → Branch
  | .inl i => oldBranches (primeOldRepresentatives N hN i)
  | .inr i => sectorSignBranches N hN i

def sectorFamilyCoefficients (N : ℕ) (hN : 0<N) (sector : Sector N) :
    ∀ i : SectorFamilyIndex N, SectorFamilyBranchIndex N hN i → ℂ
  | .inl i => oldCoefficients N (primeOldGroup N hN i)
  | .inr i => sectorSignCoefficients sector i

variable (N : ℕ) (hN : 0<N) (sector : Sector N) (S : Finset SL(2,ℤ))
  (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)

def sectorFamilyC : SectorFamilyIndex N → ℝ
  | .inl i => (primeOldData N hN S hS i).C
  | .inr i => (sectorResidualData N hN sector i S hS).C

def sectorFamilyB : SectorFamilyIndex N → ℝ
  | .inl i => (primeOldData N hN S hS i).B
  | .inr i => (sectorResidualData N hN sector i S hS).B

def sectorFamilyL : SectorFamilyIndex N → ℝ
  | .inl i => (primeOldData N hN S hS i).L
  | .inr i => (sectorResidualData N hN sector i S hS).L

def sectorFamilyK : SectorFamilyIndex N → ℝ
  | .inl i => (primeOldData N hN S hS i).K
  | .inr i => (sectorResidualData N hN sector i S hS).K

def SectorFamilyPieces : SectorFamilyIndex N → Type
  | .inl i => Fin (primeOldData N hN S hS i).n
  | .inr i => Fin (sectorResidualData N hN sector i S hS).n

instance sectorFamilyPieces_fintype (i : SectorFamilyIndex N) :
    Fintype (SectorFamilyPieces N hN sector S hS i) := by
  cases i <;> dsimp only [SectorFamilyPieces] <;> infer_instance

def sectorFamilyWords : ∀ i : SectorFamilyIndex N,
    SectorFamilyPieces N hN sector S hS i → SectorFamilyBranchIndex N hN i → List SL(2,ℤ)
  | .inl i => (primeOldData N hN S hS i).w
  | .inr i => (sectorResidualData N hN sector i S hS).w

theorem sectorFamilyC_pos (i : SectorFamilyIndex N) : 0<sectorFamilyC N hN sector S hS i := by
  cases i with
  | inl i => exact (primeOldData N hN S hS i).C_pos
  | inr i => exact (sectorResidualData N hN sector i S hS).C_pos

theorem sectorFamilyL_ge_one (i : SectorFamilyIndex N) : 1≤sectorFamilyL N hN sector S hS i := by
  cases i with
  | inl i => exact (primeOldData N hN S hS i).L_ge_one
  | inr i => exact (sectorResidualData N hN sector i S hS).L_ge_one

def sectorFamilyCost (Y ε : ℝ) (t : ℕ) (i : SectorFamilyIndex N) : ℝ :=
  sectorFamilyL N hN sector S hS i*
    (1+ε*sectorFamilyK N hN sector S hS i*(Y/sectorFamilyC N hN sector S hS i+3)^2)^(2*t)

theorem sectorFamilyCost_nonneg (Y ε : ℝ) (t : ℕ) (i : SectorFamilyIndex N) :
    0≤sectorFamilyCost N hN sector S hS Y ε t i := by
  unfold sectorFamilyCost
  rw [Nat.mul_comm 2 t,pow_mul]
  exact mul_nonneg (zero_le_one.trans (sectorFamilyL_ge_one N hN sector S hS i)) (sq_nonneg _)

def sectorFamilySampled (Y : ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) :
    SectorFamilyIndex N → Space →L[ℂ] Space
  | .inl i => oldSampledRow N hN (primeOldGroup N hN i) (primeOld_le N hN i) Y hε ht x
  | .inr i => sectorSampledRow N hN sector i Y hε ht x

theorem sectorFamily_norm_le {Y : ℝ} {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (x : ℍ) (v : Space) (i : SectorFamilyIndex N) (hY : sectorFamilyB N hN sector S hS i≤Y)
    (hz : quotientTailRow N (fun j => Y/sectorFamilyC N hN sector S hS j) hε ht
      (sectorFamilySampled N hN sector Y hε ht) x i v=0) :
    ‖sectorFamilySampled N hN sector Y hε ht x i v‖≤sectorFamilyCost N hN sector S hS Y ε t i*
      ‖commonResidualStack (signedGenerators S) (sectorFamilyBranches N hN i)
        (sectorFamilyWords N hN sector S hS i) (sectorFamilyCoefficients N hN sector i)
        (wideCompactCover_compact N hN (Y/sectorFamilyC N hN sector S hS i)) hε t x v‖ := by
  cases i with
  | inl i => exact (primeOldData N hN S hS i).old_norm_le hY hε ht x v hz
  | inr i => exact (sectorResidualData N hN sector i S hS).norm_le hY hε ht x v hz

/-- All actual sampled old and sign energies are controlled by one
literal enlarged detector, on the actual common quotient-tail kernel. -/
theorem sectorFamily_energy_le_detector {Y : ℝ}
    (hY : ∀ i, sectorFamilyB N hN sector S hS i≤Y)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (x : ℍ) (v : Space)
    (hz : quotientTailStack N (fun i => Y/sectorFamilyC N hN sector S hS i) hε ht
      (sectorFamilySampled N hN sector Y hε ht) x v=0) :
    let b := sectorFamilyBranches N hN
    let c := sectorFamilyCoefficients N hN sector
    let w := sectorFamilyWords N hN sector S hS
    let regions := fun i => wideCompactCover N (Y/sectorFamilyC N hN sector S hS i)
    let hs := fun i => wideCompactCover_compact N hN (Y/sectorFamilyC N hN sector S hS i)
    let hu' := enlargedRegion_compact b w regions hs hu
    ∑ i,‖sectorFamilySampled N hN sector Y hε ht x i v‖^2≤
      (∑ i,(sectorFamilyCost N hN sector S hS Y ε t i)^2)*
        ‖enlargedDetector (signedGenerators S) b c hu' hε t x v‖^2 := by
  dsimp only
  rw [enlargedDetector_norm_apply,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hzero := (stack_eq_zero_iff _ _).mp hz i
  have hn := sectorFamily_norm_le N hN sector S hS hε ht x v i (hY i) hzero
  have hd := commonResidualStack_norm_le_enlarged (signedGenerators S)
    (sectorFamilyBranches N hN) (sectorFamilyWords N hN sector S hS) (sectorFamilyCoefficients N hN sector)
    (fun i => wideCompactCover N (Y/sectorFamilyC N hN sector S hS i))
    (fun i => wideCompactCover_compact N hN (Y/sectorFamilyC N hN sector S hS i)) hu hε t x i v
  have he := hn.trans (mul_le_mul_of_nonneg_left hd (sectorFamilyCost_nonneg N hN sector S hS Y ε t i))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) he 2

#print axioms sectorFamily_energy_le_detector
end QuantitativeEulerEndpointPrepared
