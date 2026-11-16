module

public import QuantitativeMaassFiniteSourceEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeMaass

/-- Successive band insertions are controlled by their actual leakage
defects. No common invariant band or commutation of the factors is needed. -/
theorem recursive_leakage_energy {E H ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (A : ℕ → H →L[ℂ] H)
    (u v : ℕ → E →L[ℂ] H) (hA : ∀ n,‖A n‖≤1)
    (h0 : u 0=v 0) (hu : ∀ n,u (n+1)=(A n).comp (u n)) (n : ℕ) :
    finiteSourceEnergy b (u n-v n)≤
      (2:ℝ)^n*∑ j∈Finset.range n,finiteSourceEnergy b ((A j).comp (v j)-v (j+1)) := by
  have hnon (j : ℕ) : 0≤finiteSourceEnergy b ((A j).comp (v j)-v (j+1)) :=
    finiteSourceEnergy_nonneg b _
  induction n with
  | zero => simp [h0,finiteSourceEnergy]
  | succ n ih =>
    have hid : u (n+1)-v (n+1)=
        (A n).comp (u n-v n)+((A n).comp (v n)-v (n+1)) := by
      rw [hu]
      ext x
      simp only [sub_apply,add_apply,ContinuousLinearMap.comp_apply,map_sub]
      abel
    have hn : ‖A n‖^2≤1 := by nlinarith [hA n,norm_nonneg (A n)]
    have hl := (finiteSourceEnergy_left b (A n) (u n-v n)).trans
      (mul_le_mul_of_nonneg_right hn (finiteSourceEnergy_nonneg b _))
    simp only [one_mul] at hl
    rw [hid]
    apply (finiteSourceEnergy_add b _ _).trans
    have he := add_le_add
      (mul_le_mul_of_nonneg_left (hl.trans ih) (by norm_num : (0:ℝ)≤2))
      (le_refl (2*finiteSourceEnergy b ((A n).comp (v n)-v (n+1))))
    apply he.trans
    rw [Finset.sum_range_succ,pow_succ]
    have hp : 1≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hp) (hnon n)]

#print axioms recursive_leakage_energy

end QuantitativeMaass
