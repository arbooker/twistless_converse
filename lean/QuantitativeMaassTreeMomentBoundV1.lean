module

public import QuantitativeNewGapTreeNormV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open scoped BigOperators lp

namespace QuantitativeMaass

/-- The returning-word count is bounded by the sharp norm of the actual
regular-tree adjacency on its full counting Hilbert space. -/
theorem treeWalkCount_root_sharp_bound (p n : ℕ) (hp : 1<p) :
    (treeWalkCount (p+1) n 0:ℝ)≤(2*Real.sqrt (p:ℝ))^n := by
  let T := treeAdjacency (α := Fin (p+1))
  let v := treeRootVector (α := Fin (p+1))
  have hT : ‖T‖≤2*Real.sqrt (p:ℝ) :=
    QuantitativeNewGap.treeAdjacency_sharp_norm_le (by exact_mod_cast hp)
      (by simp)
  have hpow (k : ℕ) : ‖(T^k) v‖≤(2*Real.sqrt (p:ℝ))^k := by
    induction k with
    | zero => simpa only [pow_zero,one_apply_eq_self] using (treeRootVector_norm (α := Fin (p+1))).le
    | succ k ih =>
      rw [pow_succ']
      change ‖T ((T^k) v)‖≤_
      calc
        _ ≤ ‖T‖*‖(T^k) v‖ := T.le_opNorm _
        _ ≤ (2*Real.sqrt (p:ℝ))*(2*Real.sqrt (p:ℝ))^k :=
          mul_le_mul hT ih (norm_nonneg _) (by positivity)
        _ = _ := (pow_succ' _ _).symm
  calc
    _ = ‖((T^n) v) TreeWord.root‖ := by
      dsimp only [T,v]
      rw [treeAdjacency_power_root]
      simp only [Fintype.card_fin,TreeWord.root,List.length_nil,Complex.norm_natCast]
    _ ≤ ‖(T^n) v‖ := lp.norm_apply_le_norm (by norm_num) _ _
    _ ≤ _ := hpow n

/-- In the classical p^(-1/2) Hecke normalization, the tree moment grows
at most like 2^n. This is a moment bound, not a physical spectral gap. -/
theorem normalized_treeWalkCount_bound (p n : ℕ) (hp : 1<p) :
    (Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)≤(2:ℝ)^n := by
  have hs : 0<Real.sqrt (p:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (lt_trans Nat.zero_lt_one hp))
  calc
    _ ≤ (Real.sqrt (p:ℝ))⁻¹^n*(2*Real.sqrt (p:ℝ))^n :=
      mul_le_mul_of_nonneg_left (treeWalkCount_root_sharp_bound p n hp) (by positivity)
    _ = _ := by
      rw [←mul_pow]
      congr 1
      field_simp

#print axioms treeWalkCount_root_sharp_bound
#print axioms normalized_treeWalkCount_bound

end QuantitativeMaass
