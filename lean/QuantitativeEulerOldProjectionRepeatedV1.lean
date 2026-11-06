module

public import QuantitativeEulerOldProjectionGapV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionBlock

open AsymptoticNestedQuotients AsymptoticQuotientOperators AsymptoticCongruenceStrip
open QuantitativeNewGap
open scoped lp

/-- Finite index in the join implies finiteness of each ambient old fiber;
this is a proved algebraic consequence, not an additional hypothesis. -/
theorem ambient_old_finite {G : Type*} [Group G] {H J S : Subgroup G}
    (hJS : J ≤ S) [(H.subgroupOf S).FiniteIndex] : Finite (J ⧸ H.subgroupOf J) := by
  have hi : ((H.subgroupOf S).subgroupOf (J.subgroupOf S)).index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hj : (H.subgroupOf J).index ≠ 0 := by
    rw [← inside_index hJS]
    exact hi
  let : (H.subgroupOf J).FiniteIndex := ⟨hj⟩
  infer_instance

theorem repeatedAmbient_le_old₀ (L : ℕ) : gamma (2*(2*L)) ≤ gamma (2*L) :=
  gamma_le_of_dvd (Nat.dvd_mul_left (2*L) 2)

theorem repeatedAmbient_le_old₁ (L : ℕ) (hL : 0 < L) :
    gamma (2*(2*L)) ≤ degeneracyGroup (2*L) 2 Nat.zero_lt_two :=
  gamma_le_degeneracyGroup (2*L) 2 (by omega) Nat.zero_lt_two

theorem repeatedOld_le_join₀ (L : ℕ) : gamma (2*L) ≤ repeatedJoin L := le_sup_left

theorem repeatedOld_le_join₁ (L : ℕ) :
    degeneracyGroup (2*L) 2 Nat.zero_lt_two ≤ repeatedJoin L := le_sup_right

/-- The requested repeated-prime finite root gap now holds uniformly on
all ambient regular cosets, including both actual index-six and index-four
joins. There is only the positivity assumption on L; no ambient gap premise. -/
theorem repeated_ambient_old_gap (L : ℕ) (hL : 0 < L) :
    let : ((gamma (2*(2*L))).subgroupOf (repeatedJoin L)).FiniteIndex := by
      change (repeatedBase L).FiniteIndex
      exact repeatedBaseFiniteIndex L hL
    let : Finite (gamma (2*L) ⧸ (gamma (2*(2*L))).subgroupOf (gamma (2*L))) :=
      ambient_old_finite (repeatedOld_le_join₀ L)
    let : Finite (degeneracyGroup (2*L) 2 Nat.zero_lt_two ⧸
        (gamma (2*(2*L))).subgroupOf (degeneracyGroup (2*L) 2 Nat.zero_lt_two)) :=
      ambient_old_finite (repeatedOld_le_join₁ L)
    ∃ γ : ℝ, 0 < γ ∧ ∀ v : ℓ²(Classes (gamma (2*(2*L))),ℂ),
      γ * ‖v - (newSpace (repeatedAmbient_le_old₀ L)
        (repeatedAmbient_le_old₁ L hL)).starProjection v‖^2 ≤
      ‖(space (repeatedAmbient_le_old₀ L)).starProjection v‖^2 +
      ‖(space (repeatedAmbient_le_old₁ L hL)).starProjection v‖^2 := by
  let : ((gamma (2*(2*L))).subgroupOf (repeatedJoin L)).FiniteIndex := by
    change (repeatedBase L).FiniteIndex
    exact repeatedBaseFiniteIndex L hL
  let : Finite (gamma (2*L) ⧸ (gamma (2*(2*L))).subgroupOf (gamma (2*L))) :=
    ambient_old_finite (repeatedOld_le_join₀ L)
  let : Finite (degeneracyGroup (2*L) 2 Nat.zero_lt_two ⧸
      (gamma (2*(2*L))).subgroupOf (degeneracyGroup (2*L) 2 Nat.zero_lt_two)) :=
    ambient_old_finite (repeatedOld_le_join₁ L)
  exact ambient_old_gap (repeatedAmbient_le_old₀ L) (repeatedAmbient_le_old₁ L hL)
    (repeatedOld_le_join₀ L) (repeatedOld_le_join₁ L)

#print axioms ambient_old_finite
#print axioms repeated_ambient_old_gap
end QuantitativeEulerOldProjectionBlock
