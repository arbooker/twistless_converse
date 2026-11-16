module

public import QuantitativeMaassPoincareLocalV1
public import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace QuantitativeMaass

variable {G A : Type*} [Group G] [TopologicalSpace A] [LocallyCompactSpace A]
  [MulAction G A] [ProperlyDiscontinuousSMul G A]

omit [LocallyCompactSpace A] in
/-- Proper discontinuity gives a uniform bound on simultaneous nonzero
translates of one compact seed, independent of the evaluation point. -/
theorem compact_seed_overlap (f : A → ℂ) (hf : HasCompactSupport f) :
    ∃ M : ℕ, ∀ x : A, ∀ S : Finset G,
      (∀ g∈S, f (g • x)≠0) → S.card≤M := by
  classical
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G) hf hf
  refine ⟨hfin.toFinset.card,?_⟩
  intro x S hS
  by_cases hne : S.Nonempty
  · obtain ⟨g₀,hg₀⟩ := hne
    apply Finset.card_le_card_of_injOn (fun g => g*g₀⁻¹)
    · intro g hg
      apply hfin.mem_toFinset.mpr
      refine ⟨g•x,⟨g₀•x,subset_closure (hS g₀ hg₀),?_⟩,
        subset_closure (hS g hg)⟩
      simp only [mul_smul,inv_smul_smul]
    · exact (Equiv.mulRight g₀⁻¹).injective.injOn
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.zero_le]

/-- Every pointwise Poincaré sum is a finite sum over precisely its nonzero
terms. This also justifies summability of its squared-norm series. -/
theorem compact_seed_point_support (f : A → ℂ) (hf : HasCompactSupport f) (x : A) :
    (Function.support (fun g : G => f (g • x))).Finite := by
  classical
  obtain ⟨S,U,hU,hS⟩ := compact_seed_locally_finite (G := G) f hf x
  exact S.finite_toSet.subset (fun g hg => by
    by_contra hn
    exact hg (hS x (mem_of_mem_nhds hU) g hn))

/-- The exact pointwise estimate used to put the constructed Poincaré
series into quotient L². The constant comes from proved compact overlap. -/
theorem compact_seed_poincare_square_bound (f : A → ℂ) (hf : HasCompactSupport f) :
    ∃ M : ℕ, ∀ x : A, ‖poincareSum (G := G) f x‖^2≤
      (M:ℝ)*∑' g : G, ‖f (g • x)‖^2 := by
  classical
  obtain ⟨M,hM⟩ := compact_seed_overlap (G := G) f hf
  refine ⟨M,?_⟩
  intro x
  let hS := compact_seed_point_support (G := G) f hf x
  let S := hS.toFinset
  have hout (g : G) (hg : g∉S) : f (g•x)=0 := by
    by_contra hne
    exact hg (hS.mem_toFinset.mpr hne)
  have hcard : S.card≤M := hM x S (fun g hg => hS.mem_toFinset.mp hg)
  have hp : poincareSum (G := G) f x=∑ g∈S, f (g•x) := tsum_eq_sum hout
  have hq : (∑' g : G, ‖f (g•x)‖^2)=∑ g∈S, ‖f (g•x)‖^2 :=
    tsum_eq_sum (fun g hg => by simp [hout g hg])
  rw [hp,hq]
  calc
    ‖∑ g∈S, f (g•x)‖^2 ≤ (∑ g∈S, ‖f (g•x)‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (S.card:ℝ)*∑ g∈S, ‖f (g•x)‖^2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

#print axioms compact_seed_overlap
#print axioms compact_seed_poincare_square_bound

end QuantitativeMaass
