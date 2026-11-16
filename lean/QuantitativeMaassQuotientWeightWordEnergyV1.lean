module

public import QuantitativeMaassQuotientWeightBandPathsV1
public import QuantitativeMaassRecursiveLeakageEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeNinaMaass

namespace QuantitativeMaass
open Weighted (cutoffWordRadius cutoffWordBand)

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

theorem quotientWeightBandPath_defect_energy {ι : Type*} [Fintype ι]
    {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (t L : ℝ) (hL : 0<L)
    (v : OrthonormalBasis ι ℂ (cutoffWordBand S t L 0)) (n : ℕ)
    (ht : cutoffWordRadius L n+L+2≤t) :
    finiteSourceEnergy v ((normalizedCuspidalQuotientWeight N hN hδ hν).comp
      (quotientWeightBandPathAmbient S hδ hν t L n)-quotientWeightBandPathAmbient S hδ hν t L (n+1))≤
      16*(4*quotientWeightBound δ*(2*ν:ℝ))^2*
        (Module.finrank ℂ (cutoffWordBand S t L n):ℝ)/L^2 := by
  let : FiniteDimensional ℂ (cutoffWordBand S t L 0) := S.band_finiteDimensional _ _
  have hh := quotientWeightBandStep_defect_energy S hδ hν v t (cutoffWordRadius L n)
    L hL ht (quotientWeightBandPath S hδ hν t L n)
  have hn : ‖quotientWeightBandPath S hδ hν t L n‖^2≤1 := by
    nlinarith [quotientWeightBandPath_norm S hδ hν t L n,norm_nonneg (quotientWeightBandPath S hδ hν t L n)]
  have he := hh.trans (mul_le_mul_of_nonneg_right hn (by positivity))
  simp only [one_mul] at he
  exact he

/-- The actual normalized Gram word is close to its successive spectral
compressions, with an explicit sum of defects and no invariant-band premise. -/
theorem quotientWeight_word_energy {ι : Type*} [Fintype ι]
    {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (t L : ℝ) (hL : 0<L)
    (v : OrthonormalBasis ι ℂ (cutoffWordBand S t L 0)) (n : ℕ)
    (ht : ∀ j<n,cutoffWordRadius L j+L+2≤t) :
    finiteSourceEnergy v (quotientWeightAmbientPath S hδ hν t L n-
      quotientWeightBandPathAmbient S hδ hν t L n)≤
      (2:ℝ)^n*∑ j∈Finset.range n,
        16*(4*quotientWeightBound δ*(2*ν:ℝ))^2*
          (Module.finrank ℂ (cutoffWordBand S t L j):ℝ)/L^2 := by
  have hh := recursive_leakage_energy v (fun _ => normalizedCuspidalQuotientWeight N hN hδ hν)
    (quotientWeightAmbientPath S hδ hν t L) (quotientWeightBandPathAmbient S hδ hν t L)
    (fun _ => normalizedCuspidalQuotientWeight_norm N hN hδ hν)
    (by ext; rfl) (fun _ => rfl) n
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j hj
  exact quotientWeightBandPath_defect_energy S hδ hν t L hL v j (ht j (Finset.mem_range.mp hj))

#print axioms quotientWeightBandPath_defect_energy
#print axioms quotientWeight_word_energy

end QuantitativeMaass
