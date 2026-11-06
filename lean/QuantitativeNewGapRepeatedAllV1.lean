module

public import QuantitativeNewGapTreeFrickeGapV1
public import AsymptoticRepeatedJoinIndexV1
public import AsymptoticTotalNewCornerV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticCongruenceStrip AsymptoticNestedQuotients AsymptoticQuotientOperators
open QuantitativeEulerOldProjectionBlock
open scoped lp

/-- Every repeated prime has a finite containing old block. An exact
description of the generated join is unnecessary for this finiteness. -/
theorem repeated_containing_finite (L p : ℕ) (hL : 0<L) (hp : p.Prime) :
    ((gamma (p*(p*L))).subgroupOf (degeneracyGroup L p hp.pos)).FiniteIndex := by
  let : NeZero (p*L) := ⟨(Nat.mul_pos hp.pos hL).ne'⟩
  refine ⟨?_⟩
  change (gamma (p*(p*L))).relIndex (degeneracyGroup L p hp.pos)≠0
  rw [double_degeneracy_index L p hL hp.pos]
  exact mul_ne_zero hp.ne_zero (Subgroup.index_ne_zero_of_finite
    (H := (gamma (p*L)).subgroupOf (gamma L)))

/-- Uniform infinite-coset gap for every repeated prime, obtained from
the existing finite-block transport and a proved actual containing group. -/
theorem repeated_coset_old_gap_all (L p : ℕ) (hL : 0<L) (hp : p.Prime) :
    letI : NeZero (p*(p*L)) := ⟨(Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)).ne'⟩
    ∃ γ : ℝ, 0<γ ∧ ∀ w : ℓ²(Classes (gamma (p*(p*L))),ℂ),
      γ*‖w-(newSpace (gamma_le_of_dvd (Nat.dvd_mul_left (p*L) p))
        (gamma_le_frickeOldGroup (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL))
          (Nat.dvd_mul_left (p*L) p))).starProjection w‖^2≤
      ‖(space (gamma_le_of_dvd (Nat.dvd_mul_left (p*L) p))).starProjection w‖^2+
      ‖(space (gamma_le_frickeOldGroup (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL))
        (Nat.dvd_mul_left (p*L) p))).starProjection w‖^2 := by
  let : NeZero (p*L) := ⟨(Nat.mul_pos hp.pos hL).ne'⟩
  let : NeZero (p*(p*L)) := ⟨(Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)).ne'⟩
  let : ((gamma (p*(p*L))).subgroupOf (degeneracyGroup L p hp.pos)).FiniteIndex :=
    repeated_containing_finite L p hL hp
  have hg := ambient_old_gap
    (gamma_le_of_dvd (Nat.dvd_mul_left (p*L) p))
    (gamma_le_degeneracyGroup (p*L) p (Nat.mul_pos hp.pos hL) hp.pos)
    (gamma_le_degeneracyGroup L p hL hp.pos)
    (degeneracyGroup_mono hp.pos (Nat.dvd_mul_left L p))
  simpa only [frickeOldGroup_eq_degeneracy (p*L) p (Nat.mul_pos hp.pos hL) hp.pos] using hg

/-- A positive actual local old gap at every prime divisor, covering
both simple and arbitrary repeated ramification. -/
theorem prime_coset_old_gap (M p : ℕ) (hM : 0<M) (hp : p.Prime) :
    letI : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
    ∃ γ : ℝ, 0<γ ∧ ∀ w : ℓ²(Classes (gamma (p*M)),ℂ),
      γ*‖w-(newSpace (gamma_le_of_dvd (Nat.dvd_mul_left M p))
        (gamma_le_frickeOldGroup (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p))).starProjection w‖^2≤
      ‖(space (gamma_le_of_dvd (Nat.dvd_mul_left M p))).starProjection w‖^2+
      ‖(space (gamma_le_frickeOldGroup (Nat.mul_pos hp.pos hM)
        (Nat.dvd_mul_left M p))).starProjection w‖^2 := by
  let : NeZero M := ⟨hM.ne'⟩
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
  by_cases hpM : p∣M
  · obtain ⟨L,rfl⟩ := hpM
    have hL : 0<L := by nlinarith
    exact repeated_coset_old_gap_all L p hL hp
  · refine ⟨1-2*Real.sqrt p/((p:ℝ)+1),simple_gap_pos p hp,?_⟩
    intro w
    simpa only [frickeOldGroup_eq_degeneracy M p hM hp.pos] using
      simple_coset_old_gap M p hpM w

#print axioms repeated_containing_finite
#print axioms repeated_coset_old_gap_all
#print axioms prime_coset_old_gap

end QuantitativeNewGap
