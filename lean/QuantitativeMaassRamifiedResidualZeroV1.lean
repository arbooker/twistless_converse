module

public import AsymptoticRamifiedObservationV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass
open MeasureTheory UpperHalfPlane Set Filter
open AsymptoticHyperbolicSlash AsymptoticCompactBranch AsymptoticWeightedBranches
open AsymptoticRamifiedObservation

/-- A literal weight-zero ramified averaging law annihilates its compact
Hilbert-space residual, including all strip/cap identifications. -/
theorem ramified_residual_weightZero_eq_zero (p : ℕ) (hp : 0<p)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (δ : ℂ)
    (F : ℂ→ℂ) (hper : ∀ z,F (z+1)=F z)
    (hrow : ∀ z : ℂ,0<z.im → (∑ a∈Finset.range p,F ((z+(a:ℂ))/p))=δ*F z)
    (u : Space) (hu : u=ᵐ[volume] stripSection ε t 0 F) :
    residual p hp hs hε t 0 δ u=0 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (average p hp hs hε t 0 u)
      (δ • compactOperator 1 hs hε t 0 u),
    Lp.coeFn_smul δ (compactOperator 1 hs hε t 0 u),
    average_on_section p hp hs hε t 0 F hper u hu,
    identity_on_section hs hε t 0 F hper u hu,
    Lp.coeFn_zero ℂ 2 (volume : Measure ℍ)] with z hsub hsm hav hid hzero
  change (average p hp hs hε t 0 u-δ • compactOperator 1 hs hε t 0 u:Space) z=(0:Space) z
  rw [hsub,hzero]
  change average p hp hs hε t 0 u z-(δ • compactOperator 1 hs hε t 0 u:Space) z=0
  rw [hsm]
  change average p hp hs hε t 0 u z-δ*compactOperator 1 hs hε t 0 u z=0
  rw [hav,hid]
  classical
  by_cases hz : z∈s
  · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz,hrow z z.im_pos]
    simp only [pow_zero,mul_one,div_one]
    ring
  · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem hz,mul_zero,sub_zero]

#print axioms ramified_residual_weightZero_eq_zero
end QuantitativeMaass
