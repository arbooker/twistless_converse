module

public import QuantitativeMaassPoincareGraphV1

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology

namespace QuantitativeMaass

/-- Compact overlap turns a bounded compact seed into a globally bounded
Poincare representative; the bound is uniform over the entire quotient. -/
theorem compact_poincare_bounded {G A : Type*} [Group G] [TopologicalSpace A]
    [LocallyCompactSpace A] [MulAction G A] [ProperlyDiscontinuousSMul G A]
    (f : A → ℂ) (hf : HasCompactSupport f) (hc : Continuous f) :
    ∃ B : ℝ,0≤B ∧ ∀ x,‖poincareSum (G:=G) f x‖≤B := by
  classical
  obtain ⟨M,hM⟩ := compact_seed_overlap (G:=G) f hf
  obtain ⟨C,hC⟩ := hf.exists_bound_of_continuous hc
  let D := max C 0
  have hD : 0≤D := le_max_right _ _
  refine ⟨M*D,mul_nonneg (Nat.cast_nonneg _) hD,?_⟩
  intro x
  let hS := compact_seed_point_support (G:=G) f hf x
  let S := hS.toFinset
  have hout (γ : G) (hγ : γ∉S) : f (γ•x)=0 := by
    by_contra hn
    exact hγ (hS.mem_toFinset.mpr hn)
  have hcard : S.card≤M := hM x S (fun γ hγ => hS.mem_toFinset.mp hγ)
  change ‖∑' γ : G,f (γ•x)‖≤_
  rw [tsum_eq_sum hout]
  calc
    _ ≤ ∑ γ∈S,‖f (γ•x)‖ := norm_sum_le _ _
    _ ≤ ∑ _γ∈S,D := Finset.sum_le_sum (fun γ _ => (hC (γ•x)).trans (le_max_left _ _))
    _ = (S.card:ℝ)*D := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hD

/-- The previously proved dense family has continuous bounded invariant
representatives, as needed for dominated convergence on the finite quotient. -/
theorem poincareSeed_representative_bounded (N : ℕ) (u : SmoothUpperSeed) :
    ∃ B : ℝ,0≤B ∧ ∀ x,‖poincareSum (G:=gamma N) (upperFunction u.toFun) x‖≤B :=
  compact_poincare_bounded _ u.compact (upperFunction_continuous u.smooth)

#print axioms compact_poincare_bounded
#print axioms poincareSeed_representative_bounded

end QuantitativeMaass
