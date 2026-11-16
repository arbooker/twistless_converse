module

public import QuantitativeMaassCuspChartCovarianceV1
public import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter Matrix UpperHalfPlane
open scoped Topology MatrixGroups

namespace QuantitativeMaass

/-- Proper discontinuity for the literal integral matrix group, including
its finite central stabilizer, inherited through its injective real image. -/
instance integral_action_proper : ProperlyDiscontinuousSMul SL(2,ℤ) ℍ := by
  constructor
  intro K L hK hL
  let i : SL(2,ℤ) → (SpecialLinearGroup.mapGL (R := ℤ) (n := Fin 2) ℝ).range :=
    fun s => ⟨SpecialLinearGroup.mapGL ℝ s,⟨s,rfl⟩⟩
  have hi : Function.Injective i := by
    intro s t h
    exact SpecialLinearGroup.mapGL_injective (R := ℤ) (S := ℝ) (congrArg Subtype.val h)
  have hf := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
    (Γ := (SpecialLinearGroup.mapGL (R := ℤ) (n := Fin 2) ℝ).range) hK hL
  exact (hf.preimage hi.injOn).subset (fun _ h => h)

section General
variable {G A : Type*} [Group G] [TopologicalSpace A] [LocallyCompactSpace A]
  [MulAction G A] [ProperlyDiscontinuousSMul G A]

/-- A compactly supported Poincaré seed has only finitely many nonzero
translates throughout a neighborhood of each point, not merely pointwise. -/
theorem compact_seed_locally_finite (f : A → ℂ) (hf : HasCompactSupport f) (x : A) :
    ∃ S : Finset G, ∃ U ∈ 𝓝 x, ∀ y∈U, ∀ g∉S, f (g • y)=0 := by
  classical
  obtain ⟨K,hK,hKx⟩ := exists_compact_mem_nhds x
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
    (Γ := G) hK hf
  refine ⟨hfin.toFinset,K,hKx,?_⟩
  intro y hy g hg
  by_contra hne
  apply hg
  apply hfin.mem_toFinset.mpr
  exact ⟨g•y,⟨y,hy,rfl⟩,subset_closure hne⟩

/-- The literal automorphic Poincaré sum. Its local finiteness is proved
from compact support and proper discontinuity below. -/
def poincareSum (f : A → ℂ) (x : A) : ℂ := ∑' g : G, f (g • x)

theorem poincareSum_eventually_finite (f : A → ℂ) (hf : HasCompactSupport f) (x : A) :
    ∃ S : Finset G, poincareSum (G := G) f =ᶠ[𝓝 x] fun y => ∑ g∈S, f (g • y) := by
  obtain ⟨S,U,hU,hS⟩ := compact_seed_locally_finite (G := G) f hf x
  refine ⟨S,Filter.eventually_of_mem hU ?_⟩
  intro y hy
  exact tsum_eq_sum (hS y hy)

omit [TopologicalSpace A] [LocallyCompactSpace A] [ProperlyDiscontinuousSMul G A] in
theorem poincareSum_invariant (f : A → ℂ) (g : G) (x : A) :
    poincareSum (G := G) f (g • x)=poincareSum (G := G) f x := by
  unfold poincareSum
  simp only [← mul_smul]
  exact (Equiv.mulRight g).tsum_eq (fun h => f (h • x))

theorem poincareSum_continuous [ContinuousConstSMul G A]
    (f : A → ℂ) (hf : HasCompactSupport f) (hc : Continuous f) :
    Continuous (poincareSum (G := G) f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨S,hS⟩ := poincareSum_eventually_finite (G := G) f hf x
  apply ContinuousAt.congr_of_eventuallyEq _ hS
  exact (continuous_finsetSum S fun g _ => hc.comp (continuous_const_smul g)).continuousAt

end General

#print axioms integral_action_proper
#print axioms compact_seed_locally_finite
#print axioms poincareSum_invariant
#print axioms poincareSum_continuous

end QuantitativeMaass
