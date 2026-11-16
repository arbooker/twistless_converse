module

public import QuantitativeMaassCuspidalCutoffTailV1
public import QuantitativeNinaMaassOldBandsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set QuantitativeNinaMaass

namespace QuantitativeMaass.Weighted

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

/-- The literal part of a cuspidally projected cutoff outside the indicated
principal band. Its domain is the full automorphic Hilbert space. -/
def cuspidalWideRemainder {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (b : Cutoff N) (t L : ℝ) : AutomorphicSpace N →L[ℂ] localCuspidalSpace N hN :=
  let W := S.band (t-(L+3)) (t+(L+3))
  let : FiniteDimensional ℂ W := S.band_finiteDimensional _ _
  (1-W.starProjection).comp (cuspidalCutoff N hN b)

theorem cuspidalWideRemainder_energy {ι : Type*} [Fintype ι]
    {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (b : Cutoff N)
    (f : ι → AutomorphicSpace N) (r : ι → ℝ) (hf : Orthonormal ℂ f)
    (hgraph : ∀ i,FriedrichsGraph N (f i) (((1/4+(r i)^2:ℝ):ℂ) • f i))
    (t L : ℝ) (hL : 0<L) (ht : L+3≤t)
    (hr : ∀ i,r i∈Icc (t-1/2) (t+1/2)) :
    (∑ i,‖cuspidalWideRemainder S b t L (f i)‖^2)≤
      16*b.gradientBound^2*(Fintype.card ι:ℝ)/L^2 := by
  have hin (i : ι) : |Real.sqrt ((1/4+(r i)^2)-1/4)-t|≤1 := by
    have hri : 0≤r i := by have hi := (hr i).1; linarith
    rw [add_sub_cancel_left,Real.sqrt_sq hri]
    exact abs_le.mpr ⟨by have hh := (hr i).1; linarith,
      by have hh := (hr i).2; linarith⟩
  have h := cuspidalCutoff_wide_tail N hN b S.basis S.energy S.energy_nonneg S.graph
    f (fun i => 1/4+(r i)^2) hf (fun _ => by positivity) hgraph t L hL ht hin
  simpa only [cuspidalWideRemainder,ContinuousLinearMap.comp_apply,
    sub_apply,one_apply_eq_self] using h

#print axioms cuspidalWideRemainder_energy

end QuantitativeMaass.Weighted
