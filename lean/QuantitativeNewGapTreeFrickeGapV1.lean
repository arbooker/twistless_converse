module

public import QuantitativeNewGapTreeWeightedGapV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticCongruenceStrip UpperHalfPlane
open scoped lp

/-- The explicit unramified-prime gap with the original lower-level and
Fricke old groups, expressed using the actual weighted new projector. -/
theorem simple_weighted_fricke_gap (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hpM : ¬p∣M)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (w : ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hw : w∈AsymptoticCongruenceQuotient.quotientSpace (p*M) hε ht z) :
    letI : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
    (1-2*Real.sqrt p/((p:ℝ)+1))*
      ‖w-(AsymptoticCongruenceOldSpace.newSpace (p*M) (gamma M)
        (frickeOldGroup (p*M) M (Nat.mul_pos hp.pos hM))
        (gamma_le_of_dvd (Nat.dvd_mul_left M p))
        (gamma_le_frickeOldGroup (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p))
        hε ht z).starProjection w‖^2≤
      ‖(AsymptoticCongruenceOldSpace.lowerSpace (Nat.dvd_mul_left M p) hε ht z).starProjection w‖^2+
      ‖(AsymptoticCongruenceOldSpace.frickeSpace (Nat.mul_pos hp.pos hM)
        (Nat.dvd_mul_left M p) hε ht z).starProjection w‖^2 := by
  let : NeZero M := ⟨hM.ne'⟩
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
  simpa only [AsymptoticCongruenceOldSpace.lowerSpace,
    AsymptoticCongruenceOldSpace.frickeSpace,frickeOldGroup_eq_degeneracy M p hM hp.pos] using
    simple_weighted_old_gap M p hpM hε ht z w hw

theorem simple_gap_pos (p : ℕ) (hp : p.Prime) :
    0<1-2*Real.sqrt p/((p:ℝ)+1) := by
  let : Fact p.Prime := ⟨hp⟩
  have hpr : 1<(p:ℝ) := by exact_mod_cast hp.one_lt
  exact sub_pos.mpr (tree_neighbor_average_norm_lt_one (α:=Option (ZMod p)) hpr (by simp)).2

#print axioms simple_weighted_fricke_gap
#print axioms simple_gap_pos

end QuantitativeNewGap
