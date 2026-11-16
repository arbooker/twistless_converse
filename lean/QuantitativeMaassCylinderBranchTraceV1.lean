module

public import QuantitativeMaassColumnPairTraceV1
public import QuantitativeMaassCylinderSquareKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [InnerProductSpace ℂ H] in
/-- Continuous Hilbert columns are square integrable on compact sets in
the actual hyperbolic measure. -/
theorem compact_column_memLp (c : ℍ→H) (hc : Continuous c) (S : Set ℍ) (hS : IsCompact S) :
    MemLp c 2 (volume.restrict S) :=
  (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    ((hc.norm.pow 2).continuousOn.integrableOn_compact hS)

/-- A bounded measurable coefficient and a continuous branch preserve
square-integrable columns on every compact cell. -/
theorem compact_branch_column_memLp (c : ℍ→H) (hc : Continuous c)
    (S : Set ℍ) (hS : IsCompact S) (u : ℍ→ℍ) (hu : Continuous u)
    (a : ℍ→ℂ) (ha : AEStronglyMeasurable a (volume.restrict S)) (C : ℝ)
    (hb : ∀ᵐ x ∂volume.restrict S,‖a x‖≤C) :
    MemLp (fun x => star (a x) • c (u x)) 2 (volume.restrict S) := by
  have hd := compact_column_memLp (fun x => c (u x)) (hc.comp hu) S hS
  have hw : AEStronglyMeasurable (fun x => star (a x) • c (u x)) (volume.restrict S) :=
    ha.star.smul hd.aestronglyMeasurable
  apply hd.of_le_mul hw
  change ∀ᵐ x ∂volume.restrict S,‖star (a x) • c (u x)‖≤C*‖c (u x)‖
  filter_upwards [hb] with x hx
  rw [norm_smul,norm_star]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
  (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)

/-- The actual cylinder packet restricted to a compact output cell. -/
def cylinderCompactColumnPacket (S : Set ℍ) (hS : IsCompact S) :=
  finiteEnergyColumnOperator (volume.restrict S) (cylinderTimeColumn f hc he R hR hs)
    (compact_column_memLp _ (cylinderAbelColumn_continuous _ _ R hR _) S hS)

/-- Actual finite-branch output on a compact cell. Its coefficient is
measurable and bounded, without a smoothness requirement. -/
def cylinderBranchColumnPacket (S : Set ℍ) (hS : IsCompact S) (u : ℍ→ℍ) (hu : Continuous u)
    (a : ℍ→ℂ) (ha : AEStronglyMeasurable a (volume.restrict S)) (C : ℝ)
    (hb : ∀ᵐ x ∂volume.restrict S,‖a x‖≤C) :=
  finiteEnergyColumnOperator (volume.restrict S)
    (fun x => star (a x) • cylinderTimeColumn f hc he R hR hs (u x))
    (compact_branch_column_memLp _ (cylinderAbelColumn_continuous _ _ R hR _)
      S hS u hu a ha C hb)

include hr in
/-- Exact trace of an actual compact branch, expressed through the
convolution-square cylinder kernel. -/
theorem cylinder_compact_branch_trace {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (S : Set ℍ) (hS : IsCompact S) (u : ℍ→ℍ) (hu : Continuous u)
    (a : ℍ→ℂ) (ha : AEStronglyMeasurable a (volume.restrict S)) (C : ℝ)
    (hb : ∀ᵐ x ∂volume.restrict S,‖a x‖≤C) :
    (∑' i,(inner ℂ (cylinderCompactColumnPacket f hc he R hR hs S hS (basis i))
      (cylinderBranchColumnPacket f hc he R hR hs S hS u hu a ha C hb (basis i))).re)=
      ∫ x in S,(a x*radialPoincareKernel 0
        (abelProfile (evenCoshLift (timeConvolution f f))) x (u x)).re := by
  rw [cylinderCompactColumnPacket,cylinderBranchColumnPacket,finiteEnergyColumn_pair_trace]
  apply integral_congr_ae
  filter_upwards with x
  have hsym : (inner ℂ (cylinderTimeColumn f hc he R hR hs x)
      (star (a x) • cylinderTimeColumn f hc he R hR hs (u x))).re=
      (inner ℂ (star (a x) • cylinderTimeColumn f hc he R hR hs (u x))
        (cylinderTimeColumn f hc he R hR hs x)).re := inner_re_symm (𝕜 := ℂ) _ _
  rw [hsym]
  simp only [inner_smul_left,starRingEnd_apply,star_star,cylinderTimeSquare_kernel_cross f hc he hr R hR hs]

#print axioms compact_column_memLp
#print axioms compact_branch_column_memLp
#print axioms cylinder_compact_branch_trace

end QuantitativeMaass
