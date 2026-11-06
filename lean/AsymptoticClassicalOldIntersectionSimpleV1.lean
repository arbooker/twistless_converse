module

public import AsymptoticClassicalOldIntersectionSimpleGroupV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Filter Topology
open scoped ModularForm

/-- At a simply ramified prime, simultaneous membership in both old images
 forces zero: the generated group has arbitrarily small lower periods. -/
theorem simple_old_intersection_eq_bot (M p : ℕ) (hM : 0 < M) (hp : p.Prime)
    (hc : p.Coprime M) (k : ℤ) :
    LinearMap.range (restrict k (level_antitone (Nat.dvd_mul_left M p))) ⊓
      LinearMap.range (restrict k (level_le_dilation_conjugate M p hp.pos)) = ⊥ := by
  let : NeZero M := ⟨hM.ne'⟩
  let : NeZero (p * M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
  apply le_antisymm _ bot_le
  intro f hf
  have hi : level M ⊔ dilationLevel M p hp.pos ≤ slashStabilizer k f :=
    (mem_restrict_intersection_iff (G := level (p * M)) (H := level M)
      (L := dilationLevel M p hp.pos) k _ _ f).mp hf
  change f = 0
  let q : ℝ := 1 / (p : ℝ)^2
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hqpos : 0 < q := one_div_pos.mpr (sq_pos_of_pos (by linarith))
  have hqlt : q < 1 := by
    apply (div_lt_one (sq_pos_of_pos (by linarith : (0 : ℝ) < p))).mpr
    nlinarith
  apply cusp_zero_of_small_lower_symmetries k f (fun n => (M : ℝ) * q^n)
  · simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hqpos.le hqlt))
  · intro n
    exact mul_ne_zero (by exact_mod_cast hM.ne') (pow_ne_zero n hqpos.ne')
  · intro n
    exact hi (small_lower_mem_join M p hp.pos hc n)

#print axioms simple_old_intersection_eq_bot

end AsymptoticClassicalCusp
