module

public import QuantitativeMaassNormalizerParityBandV1
public import QuantitativeMaassAdmissibleNewBandFilterV1

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeNinaMaass QuantitativeNewGap AsymptoticSectorSigns AsymptoticSubspaceIntersection
open QuantitativeArithmeticRepeatedTwoBands QuantitativeArithmeticNewBandProjections
open QuantitativeArithmeticNewBandProduct
namespace QuantitativeMaass

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

variable {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (e : Sector N)

def sectorParitySignSpace (i : SectorSignIndex N) : Submodule ℂ (S.parityBand a b σ) :=
  involutionSignSpace (sectorParityBandNormalizer S a b σ i).toContinuousLinearMap (sectorNormalizerSign e i)

theorem sectorParitySignProjection_apply (i : SectorSignIndex N) (x : S.parityBand a b σ) :
    (sectorParitySignSpace S a b σ e i).starProjection x=
      (1/2:ℂ) • (x+(sectorNormalizerSign e i:ℂ) • sectorParityBandNormalizer S a b σ i x) :=
  involutionSignSpace_projection _ (sectorParityBandNormalizer_selfAdjoint S a b σ i)
    (sectorParityBandNormalizer_involutive S a b σ i) _ (sectorNormalizerSign_sq e i) x

theorem sectorParitySignProjections_commute (i j : SectorSignIndex N) :
    Commute (sectorParitySignSpace S a b σ e i).starProjection
      (sectorParitySignSpace S a b σ e j).starProjection :=
  involutionSignProjections_commute _ _ (sectorParityBandNormalizer_selfAdjoint S a b σ i)
    (sectorParityBandNormalizer_selfAdjoint S a b σ j) (sectorParityBandNormalizers_commute S a b σ i j) _ _

theorem totalNewBand_sectorSign_commute (i : SectorSignIndex N) :
    Commute (totalNewBand N hN S a b σ).starProjection
      (sectorParitySignSpace S a b σ e i).starProjection :=
  subspace_involutionSign_commute _ _ (sectorParityBandNormalizer_selfAdjoint S a b σ i)
    (invariantSpace_projection_commute _ _ (sectorParityBandNormalizer_selfAdjoint S a b σ i)
      (sectorParityBandNormalizer_new S a b σ i)) _

def sectorParityBandSpace : Submodule ℂ (S.parityBand a b σ) :=
  inter (totalNewBand N hN S a b σ)
    (jointListSpace (sectorParitySignSpace S a b σ e) (Finset.univ : Finset (SectorSignIndex N)).toList)

theorem sectorParityBandSpace_mem (x : S.parityBand a b σ) :
    x∈sectorParityBandSpace S a b σ e ↔
      inclusion S a b σ x∈completedCountingSectorSpace N hN e := by
  have hm : x∈sectorParityBandSpace S a b σ e ↔ x∈totalNewBand N hN S a b σ ∧
      ∀ i : SectorSignIndex N,sectorParityBandNormalizer S a b σ i x=(sectorNormalizerSign e i:ℂ) • x := by
    rw [sectorParityBandSpace,inter_mem,jointListSpace_mem]
    simp only [Finset.mem_toList,Finset.mem_univ,forall_true_left,sectorParitySignSpace,
      involutionSignSpace,LinearMap.mem_ker,ContinuousLinearMap.toLinearMap_sub,
      ContinuousLinearMap.toLinearMap_smul,ContinuousLinearMap.toLinearMap_one,
      LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,sub_eq_zero]
    rfl
  rw [hm,completedCountingSectorSpace_mem]
  constructor
  · intro hx
    refine ⟨⟨x.val.val.property,hx.1⟩,?_⟩
    intro i
    have hh := congrArg (inclusion S a b σ) (hx.2 i)
    simpa only [sectorParityBandNormalizer_apply,map_smul] using hh
  · intro hx
    refine ⟨hx.1.2,?_⟩
    intro i
    apply parityBand_inclusion_injective S a b σ
    simpa only [sectorParityBandNormalizer_apply,map_smul] using hx.2 i

/-- This is the original canonical generator sector restricted to the
actual fixed-parity spectral band. -/
theorem sectorParityBandSpace_eq_canonical (hAd : GridAdmissibleGap.Admissible N) :
    sectorParityBandSpace S a b σ e=
      (completedNewSignSpace N hN (sectorCharacter N hN e)).comap (inclusion S a b σ) := by
  ext x
  change x∈sectorParityBandSpace S a b σ e ↔ inclusion S a b σ x∈completedNewSignSpace N hN (sectorCharacter N hN e)
  rw [sectorParityBandSpace_mem,completedCountingSectorSpace_eq_newSign N hAd e]

def sectorParitySignProduct : S.parityBand a b σ →L[ℂ] S.parityBand a b σ :=
  ((Finset.univ : Finset (SectorSignIndex N)).toList.map fun i =>
    (sectorParitySignSpace S a b σ e i).starProjection).prod

theorem sectorParitySignProduct_norm : ‖sectorParitySignProduct S a b σ e‖≤1 := by
  apply contraction_list_prod
  intro i
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using (sectorParitySignSpace S a b σ e i).norm_starProjection_apply_le x

/-- Exact finite sign product after the actual total-new projection. -/
theorem sectorParityBandSpace_projection :
    (sectorParityBandSpace S a b σ e).starProjection=
      (totalNewBand N hN S a b σ).starProjection*sectorParitySignProduct S a b σ e := by
  have hc : Commute (totalNewBand N hN S a b σ).starProjection
      (jointListSpace (sectorParitySignSpace S a b σ e)
        (Finset.univ : Finset (SectorSignIndex N)).toList).starProjection := by
    rw [jointListSpace_projection _ (sectorParitySignProjections_commute S a b σ e)]
    apply Commute.list_prod_right
    intro U hU
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hU
    exact totalNewBand_sectorSign_commute S a b σ e i
  calc
    _ = (inter (totalNewBand N hN S a b σ)
        (jointListSpace (sectorParitySignSpace S a b σ e)
          (Finset.univ : Finset (SectorSignIndex N)).toList)).starProjection := rfl
    _ = (totalNewBand N hN S a b σ).starProjection.comp
        (jointListSpace (sectorParitySignSpace S a b σ e)
          (Finset.univ : Finset (SectorSignIndex N)).toList).starProjection :=
      inter_projection_of_commute _ _ hc
    _ = _ := congrArg (fun U : S.parityBand a b σ →L[ℂ] S.parityBand a b σ =>
      (totalNewBand N hN S a b σ).starProjection.comp U)
      (jointListSpace_projection _ (sectorParitySignProjections_commute S a b σ e) _)

#print axioms sectorParitySignProjection_apply
#print axioms sectorParitySignProjections_commute
#print axioms totalNewBand_sectorSign_commute
#print axioms sectorParityBandSpace_mem
#print axioms sectorParityBandSpace_eq_canonical
#print axioms sectorParitySignProduct_norm
#print axioms sectorParityBandSpace_projection
end QuantitativeMaass
