module

public import QuantitativeMaassPrincipalEnergySeparationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeMaass.Weighted

/-- Actual cutoff coefficients outside a wide principal band. Exceptional
eigenvalues are included through their nonnegative energy, without an
assumption that multiplication preserves the cuspidal subspace or a band. -/
theorem smooth_cutoff_outside_wide_band {ι κ : Type*} [Fintype κ]
    (N : ℕ) (b : Cutoff N) (r : ι → ℝ) (μ : κ → ℝ)
    (f : ι → AutomorphicSpace N) (g : κ → AutomorphicSpace N)
    (hf : Orthonormal ℂ f) (hg : Orthonormal ℂ g)
    (hr : ∀ i,0≤r i) (hμ : ∀ j,0≤μ j)
    (hfgraph : ∀ i,FriedrichsGraph N (f i) ((r i:ℂ) • f i))
    (hggraph : ∀ j,FriedrichsGraph N (g j) ((μ j:ℂ) • g j))
    (t L : ℝ) (hL : 0<L)
    (hin : ∀ j,|Real.sqrt (μ j-1/4)-t|≤1)
    (hout : ∀ i,L+3≤|Real.sqrt (r i-1/4)-t|) :
    (∑ j,∑' i,‖inner ℂ (f i).val (multiplier N b (g j).val)‖^2)≤
      16*b.gradientBound^2*(Fintype.card κ:ℝ)/L^2 := by
  apply smooth_cutoff_separated_family_energy N b r μ f g hf hg hr hμ
    hfgraph hggraph L hL
  intro i j
  exact outside_wide_band_energy_separation (r i) (μ j) t L
    (hr i) (hμ j) (hin j) (hout i)

#print axioms smooth_cutoff_outside_wide_band

end QuantitativeMaass.Weighted
