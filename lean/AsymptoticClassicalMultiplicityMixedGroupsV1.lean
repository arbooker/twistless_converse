module

public import AsymptoticClassicalMultiplicityOrdinaryV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix ConjAct AsymptoticCongruenceLabels
open scoped ModularForm Pointwise MatrixGroups

/-- Among integral matrices, belonging to a dilated group is exactly the
 stronger divisibility condition on the lower-left entry. -/
theorem integral_mem_dilationLevel_iff (M q : ℕ) (hq : 0 < q) (A : SL(2, ℤ)) :
    SpecialLinearGroup.mapGL ℝ A ∈ dilationLevel M q hq ↔
      A ∈ CongruenceSubgroup.Gamma0 (q * M) := by
  constructor
  · rintro ⟨_, ⟨B, hB, rfl⟩, he⟩
    have hh : dilationReal q hq * SpecialLinearGroup.mapGL ℝ A =
        SpecialLinearGroup.mapGL ℝ B * dilationReal q hq := by
      rw [← he]
      change dilationReal q hq * ((dilationReal q hq)⁻¹ * SpecialLinearGroup.mapGL ℝ B *
        ((dilationReal q hq)⁻¹)⁻¹) = _
      group
    have hc := congrArg (fun g : GL (Fin 2) ℝ => g.val 1 0) hh
    change ((dilationReal q hq).val * A.val.map (fun a : ℤ => (a : ℝ))) 1 0 =
      (B.val.map (fun a : ℤ => (a : ℝ)) * (dilationReal q hq).val) 1 0 at hc
    simp [dilationReal, dilationGL, GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two] at hc
    have hc' : A 1 0 = B 1 0 * (q : ℤ) := by exact_mod_cast hc
    obtain ⟨c, hcB⟩ := (gamma0_mem_dvd M B).mp hB
    rw [gamma0_mem_dvd]
    refine ⟨c, ?_⟩
    rw [hc', hcB, Nat.cast_mul]
    ring
  · intro hA
    exact level_le_dilation_conjugate M q hq ⟨A, hA, rfl⟩

/-- An integral level meets a dilated level in an explicit integral level. -/
theorem level_inf_dilationLevel (A B q : ℕ) (hq : 0 < q) :
    level A ⊓ dilationLevel B q hq = level (Nat.lcm A (q * B)) := by
  rw [← level_inf]
  ext g
  constructor
  · rintro ⟨⟨C, hC, rfl⟩, hg⟩
    exact ⟨⟨C, hC, rfl⟩, ⟨C, (integral_mem_dilationLevel_iff B q hq C).mp hg, rfl⟩⟩
  · rintro ⟨hA, hB⟩
    exact ⟨hA, level_le_dilation_conjugate B q hq hB⟩

/-- The mixed ordinary/dilated old groups have the required exact intersection. -/
theorem mixed_level_inf (M p q : ℕ) (hq : 0 < q) :
    level (q * M) ⊓ dilationLevel (p * M) q hq = level (p * (q * M)) := by
  rw [level_inf_dilationLevel, Nat.lcm_eq_right
    (Nat.mul_dvd_mul_left q (Nat.dvd_mul_left M p))]
  congr 1
  ring

/-- Dilation and ordinary old directions have the same relative index. -/
theorem dilationLevel_over_index (M q : ℕ) (hM : 0 < M) (hq : 0 < q) :
    (level (q * M)).relIndex (dilationLevel M q hq) =
      (level (q * M)).relIndex (level M) := by
  rw [← frickeOldLevel_eq_dilationLevel M q hM hq, frickeOldLevel_relIndex]

/-- The two sides of the mixed cross-prime diamond have equal indices. -/
theorem mixed_level_index (M p q : ℕ) (hM : 0 < M) (hp : 0 < p)
    (hq : q.Prime) (hc : p.Coprime q) :
    (level (p * (q * M))).relIndex (dilationLevel (p * M) q hq.pos) =
      (level (q * M)).relIndex (dilationLevel M q hq.pos) := by
  rw [show p * (q * M) = q * (p * M) by ring,
    dilationLevel_over_index (p * M) q (Nat.mul_pos hp hM) hq.pos,
    dilationLevel_over_index M q hM hq.pos,
    show q * (p * M) = p * (q * M) by ring]
  exact coprime_level_index M p q hM hp hq hc

#print axioms integral_mem_dilationLevel_iff
#print axioms level_inf_dilationLevel
#print axioms mixed_level_inf
#print axioms dilationLevel_over_index
#print axioms mixed_level_index

end AsymptoticClassicalCusp
