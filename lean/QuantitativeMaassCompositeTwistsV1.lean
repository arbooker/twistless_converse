module

public import QuantitativeMaassPrimitiveCRTV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

theorem analytic_twist_units (F : ℂ → ℂ) (q : ℕ) [NeZero q] (z : ℂ) :
    FinitenessAnalyticReconstruction.twist F q z=
      ∑ u : (ZMod q)ˣ,F (z+((u:ZMod q).val:ℂ)/q) := by
  classical
  unfold FinitenessAnalyticReconstruction.twist
  rw [←Finset.sum_coe_sort]
  exact (Equiv.sum_comp (primitiveResidueUnitsEquiv q)
    (fun a : FinitenessRamanujanSum.residues q => F (z+(a.val:ℂ)/q))).symm

/-- Primitive twists multiply at coprime moduli for every periodic function. -/
theorem analytic_twist_coprime_mul (F : ℂ → ℂ) (hF : Function.Periodic F 1)
    (m n : ℕ) (hm : 0<m) (hn : 0<n) (hc : m.Coprime n) (z : ℂ) :
    FinitenessAnalyticReconstruction.twist F (m*n) z=
      FinitenessAnalyticReconstruction.twist
        (FinitenessAnalyticReconstruction.twist F n) m z := by
  classical
  let : NeZero m := ⟨hm.ne'⟩
  let : NeZero n := ⟨hn.ne'⟩
  let : NeZero (m*n) := ⟨(Nat.mul_pos hm hn).ne'⟩
  have hterm (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
      F (z+((primitiveTranslationCRT m n hc (a,b):ZMod (m*n)).val:ℂ)/(m*n))=
        F (z+((a:ZMod m).val:ℂ)/m+((b:ZMod n).val:ℂ)/n) := by
    have hh := periodic_fraction_congr F hF (m*n) (Nat.mul_pos hm hn)
      ((primitiveTranslationCRT m n hc (a,b):ZMod (m*n)).val:ℤ)
      ((n:ℤ)*(a:ZMod m).val+(m:ℤ)*(b:ZMod n).val)
      (by simpa using primitiveTranslationCRT_value m n hc a b) z
    push_cast at hh
    rw [hh]
    congr 1
    have hmC : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
    have hnC : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
    field_simp
    ring
  rw [analytic_twist_units,analytic_twist_units]
  simp_rw [analytic_twist_units]
  simp only [Nat.cast_mul]
  calc
    _ = ∑ ab : (ZMod m)ˣ × (ZMod n)ˣ,
        F (z+((primitiveTranslationCRT m n hc ab:ZMod (m*n)).val:ℂ)/(m*n)) :=
      (Equiv.sum_comp (primitiveTranslationCRT m n hc)
        (fun u : (ZMod (m*n))ˣ => F (z+((u:ZMod (m*n)).val:ℂ)/(m*n)))).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_congr rfl (fun b _ => hterm a b)

#print axioms analytic_twist_units
#print axioms analytic_twist_coprime_mul

end QuantitativeMaass
