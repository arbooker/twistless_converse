module

public import SmallLevelContinuedFiniteShiftSourceV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelFiniteShift
open Complex Filter
open scoped Topology

/-- A vanishing analytic coefficient cancels any pole of order at most one.
The conclusion concerns germs, so it does not require a particular value
assigned to a removable singularity. -/
theorem simple_pole_cancellation (c g : ℂ → ℂ) (x : ℂ)
    (hc : AnalyticAt ℂ c x) (hc0 : c x=0) (hg : MeromorphicAt g x)
    (horder : (-1:WithTop ℤ)≤meromorphicOrderAt g x) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r x ∧ (fun z => c z*g z)=ᶠ[𝓝[≠] x] r := by
  have hpos : 0<meromorphicOrderAt c x :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hc.meromorphicAt).mp
      (by simpa only [hc0] using hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hc1 : (1:WithTop ℤ)≤meromorphicOrderAt c x := by
    cases he : meromorphicOrderAt c x with
    | top => simp
    | coe n =>
      rw [he] at hpos
      have hn : (0:ℤ)<n := by exact_mod_cast hpos
      exact_mod_cast (show (1:ℤ)≤n by omega)
  have hprod : 0≤meromorphicOrderAt (c*g) x := by
    rw [meromorphicOrderAt_mul hc.meromorphicAt hg]
    have hh := add_le_add hc1 horder
    norm_num at hh
    exact hh
  exact ((hc.meromorphicAt.mul hg).meromorphicOrderAt_nonneg_iff).mp hprod

#print axioms simple_pole_cancellation
end SmallLevelFiniteShift
