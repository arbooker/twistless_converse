module

public import QuantitativeMaassCutoffBandPathsV1
public import QuantitativeMaassRecursiveLeakageEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeNinaMaass

namespace QuantitativeMaass.Weighted

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

theorem cutoffBandPath_defect_energy {ι : Type*} [Fintype ι]
    {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (b : ℕ → Cutoff N) (hb : ∀ j,(b j).bound≤1) (t L : ℝ) (hL : 0<L)
    (v : OrthonormalBasis ι ℂ (cutoffWordBand S t L 0)) (n : ℕ)
    (ht : cutoffWordRadius L n+L+2≤t) :
    finiteSourceEnergy v ((cuspidalCutoffEndomorphism N hN (b n)).comp
      (cutoffBandPathAmbient S b t L n)-cutoffBandPathAmbient S b t L (n+1))≤
      16*(b n).gradientBound^2*(Module.finrank ℂ (cutoffWordBand S t L n):ℝ)/L^2 := by
  let : FiniteDimensional ℂ (cutoffWordBand S t L 0) := S.band_finiteDimensional _ _
  have hh := nestedBandRemainder_precompose_energy S (b n) v t (cutoffWordRadius L n)
    L hL ht (cutoffBandPath S b t L n)
  have hn : ‖cutoffBandPath S b t L n‖^2≤1 := by
    nlinarith [cutoffBandPath_norm_le S b hb t L n,norm_nonneg (cutoffBandPath S b t L n)]
  have he := hh.trans (mul_le_mul_of_nonneg_right hn (by positivity))
  simp only [one_mul] at he
  unfold finiteSourceEnergy
  simp only [sub_apply,ContinuousLinearMap.comp_apply,cutoffBandPath_defect]
  exact he

/-- Quantitative comparison of an actual cutoff word with its successive
spectral-band compressions. Every factor may fail to preserve every band. -/
theorem cutoff_word_energy {ι : Type*} [Fintype ι]
    {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (b : ℕ → Cutoff N) (hb : ∀ j,(b j).bound≤1) (t L : ℝ) (hL : 0<L)
    (v : OrthonormalBasis ι ℂ (cutoffWordBand S t L 0)) (n : ℕ)
    (ht : ∀ j<n,cutoffWordRadius L j+L+2≤t) :
    finiteSourceEnergy v (cutoffAmbientPath S b t L n-cutoffBandPathAmbient S b t L n)≤
      (2:ℝ)^n*∑ j∈Finset.range n,
        16*(b j).gradientBound^2*(Module.finrank ℂ (cutoffWordBand S t L j):ℝ)/L^2 := by
  have hh := recursive_leakage_energy v (fun j => cuspidalCutoffEndomorphism N hN (b j))
    (cutoffAmbientPath S b t L) (cutoffBandPathAmbient S b t L)
    (fun j => (cuspidalCutoffEndomorphism_norm_le N hN (b j)).trans (hb j))
    (by ext; rfl) (fun _ => rfl) n
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j hj
  exact cutoffBandPath_defect_energy S b hb t L hL v j (ht j (Finset.mem_range.mp hj))

#print axioms cutoffBandPath_defect_energy
#print axioms cutoff_word_energy

end QuantitativeMaass.Weighted
