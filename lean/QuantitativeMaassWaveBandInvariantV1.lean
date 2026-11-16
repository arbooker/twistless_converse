module

public import QuantitativeNinaMaassOldBandsV1
public import QuantitativeMaassWaveSeparationV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set QuantitativeNinaMaass
open scoped InnerProductSpace

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

/-- Actual wave commutation and cusp preservation suffice to preserve every
principal spectral band, without an extra graph-domain hypothesis. -/
theorem wave_commuting_cusp_band {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (U : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hc : ∀ x,x∈localCuspidalSpace N hN → U x∈localCuspidalSpace N hN)
    (hU : ∀ t,Commute U (Wave.shiftedQuotientWave N t))
    (a b : ℝ) (x : localCuspidalSpace N hN) (hx : x∈S.band a b) :
    U.toLinearMap.restrict hc x∈S.band a b := by
  let L := U.toLinearMap.restrict hc
  have ho := S.basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  have hfin := principalWindowIndices_finite N hN _ ho (fun j => (S.basis j).property)
    S.energy S.energy_nonneg S.graph a b
  have hgen (j : principalWindowIndices S.energy a b) : L (S.basis j.val)∈S.band a b := by
    apply hilbertBasis_mem_finite_span S.basis _ hfin
    intro i hi
    rw [S.basis.repr_apply_apply]
    change inner ℂ (S.basis i:AutomorphicSpace N) (U (S.basis j.val:AutomorphicSpace N))=0
    apply wave_commuting_energy_coefficient_zero N U hU _ _ _ _
      (S.energy_nonneg i) (S.energy_nonneg j.val) (S.graph i) (S.graph j.val)
    intro heq
    apply hi
    change 1/4≤S.energy i ∧ Real.sqrt (S.energy i-1/4)∈Icc a b
    rw [heq]
    exact j.property
  change L x∈S.band a b
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j,rfl⟩ := hy
    exact hgen j
  | zero => simpa only [map_zero] using (S.band a b).zero_mem
  | add y z _ _ hy hz => simpa only [map_add] using (S.band a b).add_mem hy hz
  | smul c y _ hy => simpa only [map_smul] using (S.band a b).smul_mem c hy

#print axioms wave_commuting_cusp_band

end QuantitativeMaass
