module

public import AsymptoticClassicalOldLevelsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm

variable (N : ℕ) (hN : 0 < N) (k : ℤ)
  (p : {p : ℕ // p.Prime ∧ p ∣ N})

/-- Membership in the concrete new subspace gives the two literal cusp-form
 trace equations. -/
theorem prime_trace_eq_zero (f : CuspForm (level N) k)
    (hf : f ∈ newSpace N hN k) :
    letI : NeZero N := ⟨hN.ne'⟩
    letI : NeZero (N / p.val) := ⟨(Nat.div_pos (Nat.le_of_dvd hN p.property.2)
      p.property.1.pos).ne'⟩
    arithmeticTrace (level N) (level (N / p.val)) k f = 0 ∧
      arithmeticTrace (level N) (frickeOldLevel N (N / p.val) hN) k f = 0 := by
  exact (mem_newSpace N hN k f).mp hf p

/-- A form coming from either of the two old levels and satisfying all
 new trace equations must be zero. -/
theorem new_disjoint_first_old :
    Disjoint (newSpace N hN k)
      (LinearMap.range (restrict k (level_antitone (Nat.div_dvd_of_dvd p.property.2)))) := by
  let : NeZero N := ⟨hN.ne'⟩
  let : NeZero (N / p.val) := ⟨(Nat.div_pos (Nat.le_of_dvd hN p.property.2)
    p.property.1.pos).ne'⟩
  let : (level N).IsFiniteRelIndex (level (N / p.val)) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level (N / p.val))).symm).1
  apply Disjoint.mono_left _ (old_trace_kernel_disjoint k
    (level_antitone (Nat.div_dvd_of_dvd p.property.2))).symm
  intro f hf
  exact (prime_trace_eq_zero N hN k p f hf).1

theorem new_disjoint_second_old :
    Disjoint (newSpace N hN k)
      (LinearMap.range (restrict k
        (level_le_frickeOldLevel hN (Nat.div_dvd_of_dvd p.property.2)))) := by
  let : NeZero N := ⟨hN.ne'⟩
  let : NeZero (N / p.val) := ⟨(Nat.div_pos (Nat.le_of_dvd hN p.property.2)
    p.property.1.pos).ne'⟩
  let : (level N).IsFiniteRelIndex (frickeOldLevel N (N / p.val) hN) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).trans
      (Subgroup.IsArithmetic.is_commensurable
        (𝒢 := frickeOldLevel N (N / p.val) hN)).symm).1
  apply Disjoint.mono_left _ (old_trace_kernel_disjoint k
    (level_le_frickeOldLevel hN (Nat.div_dvd_of_dvd p.property.2))).symm
  intro f hf
  exact (prime_trace_eq_zero N hN k p f hf).2

#print axioms prime_trace_eq_zero
#print axioms new_disjoint_first_old
#print axioms new_disjoint_second_old

end AsymptoticClassicalCusp
