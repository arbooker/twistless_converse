module

public import QuantitativeNewGapTreeHeckeMomentsV1
public import QuantitativeNewGapTreeMomentNormV1
public import QuantitativeNewGapTreeNormV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open QuantitativeMaass AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticNestedQuotients AsymptoticRegularTrace
open scoped BigOperators lp InnerProductSpace

def primeTreeAverage (p : ℕ) [Fact p.Prime] :
    ℓ²(TreeWord (Option (ZMod p)),ℂ) →L[ℂ] ℓ²(TreeWord (Option (ZMod p)),ℂ) :=
  ((p:ℝ)+1)⁻¹ • treeAdjacency

theorem primeTreeAverage_complex (p : ℕ) [Fact p.Prime] :
    primeTreeAverage p = (((p+1:ℕ):ℂ)⁻¹) • treeAdjacency := by
  ext f v
  simp only [primeTreeAverage,smul_apply,lp.coeFn_smul,Pi.smul_apply,
    Complex.real_smul,smul_eq_mul,Complex.ofReal_inv,Complex.ofReal_add,
    Complex.ofReal_natCast,Complex.ofReal_one,Nat.cast_add,Nat.cast_one]

theorem primeTreeAverage_selfAdjoint (p : ℕ) [Fact p.Prime] :
    IsSelfAdjoint (primeTreeAverage p) := by
  rw [primeTreeAverage_complex]
  exact (show IsSelfAdjoint (((p+1:ℕ):ℂ)⁻¹) by simp [IsSelfAdjoint]).smul
    treeAdjacency_selfAdjoint

theorem primeTreeAverage_power_root (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ((primeTreeAverage p)^n) treeRootVector TreeWord.root =
      (((p+1:ℕ):ℂ)⁻¹)^n*(treeWalkCount (p+1) n 0:ℂ) := by
  rw [primeTreeAverage_complex,smul_pow]
  change (((p+1:ℕ):ℂ)⁻¹)^n *
    ((treeAdjacency (α:=Option (ZMod p)))^n) treeRootVector TreeWord.root = _
  rw [treeAdjacency_power_root]
  simp [TreeWord.root]

/-- Sharp norm bound for the literal rational arithmetic Hecke operator.
The proof identifies all rooted moments and then uses equivariance of
continuous functional calculus and faithful quotient columns to control
the entire operator. No spectral support assumption is supplied. -/
theorem regularHecke_sharp_norm_le (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hpM : ¬p ∣ M) : ‖regularHecke M p‖ ≤ 2*Real.sqrt p/((p:ℝ)+1) := by
  have hp : 1<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hc : (Fintype.card (Option (ZMod p)):ℝ)=(p:ℝ)+1 := by simp
  apply equivariant_norm_le_of_moments (gamma M) (regularHecke M p)
    (regularHecke_selfAdjoint M p hpM) (regularHecke_equivariant M p hpM)
    (primeTreeAverage p) (primeTreeAverage_selfAdjoint p) treeRootVector
  · intro n
    rw [delta_inner,regularHecke_power_root M p hpM]
    have ht : ⟪treeRootVector,((primeTreeAverage p)^n) treeRootVector⟫_ℂ =
        ((primeTreeAverage p)^n) treeRootVector TreeWord.root := by
      rw [treeRootVector,lp.inner_single_left]
      simp [RCLike.inner_apply]
    rw [ht,primeTreeAverage_power_root]
  · positivity
  · exact (tree_neighbor_average_norm_lt_one hp hc).1

/-- The two actual arithmetic old embeddings at an unramified prime
have a strictly positive regular-representation angle gap. This statement
does not assert the separate physical cuspidal Satake bound. -/
theorem arithmetic_old_cross_gram_sharp (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hpM : ¬p ∣ M) :
    ‖(isometry (gamma_le_of_dvd (Nat.dvd_mul_left M p))).toContinuousLinearMap.adjoint.comp
      (isometry (gamma_le_degeneracyGroup M p (Nat.pos_of_ne_zero (NeZero.ne M))
        (Fact.out : p.Prime).pos)).toContinuousLinearMap‖ ≤ 2*Real.sqrt p/((p:ℝ)+1) ∧
      2*Real.sqrt p/((p:ℝ)+1)<1 := by
  constructor
  · rw [← regularHecke_norm_eq_cross_gram]
    exact regularHecke_sharp_norm_le M p hpM
  · have hp : 1<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact (tree_neighbor_average_norm_lt_one (α:=Option (ZMod p)) hp (by simp)).2

#print axioms regularHecke_sharp_norm_le
#print axioms arithmetic_old_cross_gram_sharp

end QuantitativeNewGap
