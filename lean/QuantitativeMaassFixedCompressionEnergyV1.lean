module

public import QuantitativeMaassRecursiveLeakageEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeMaass

/-- A single contractive outer projection can replace successive inner
compressions. Its only geometric input is that it fixes those intermediate
ranges; it need not commute with the operator. -/
theorem fixed_compression_energy {E H ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (A : ℕ → H →L[ℂ] H) (P : H →L[ℂ] H)
    (u v z : ℕ → E →L[ℂ] H) (hA : ∀ j,‖A j‖≤1) (hP : ‖P‖≤1)
    (hu0 : u 0=v 0) (hz0 : z 0=v 0)
    (hu : ∀ j,u (j+1)=(A j).comp (u j))
    (hz : ∀ j,z (j+1)=(P.comp (A j)).comp (z j))
    (n : ℕ) (hfix : ∀ j≤n,P.comp (v j)=v j) :
    finiteSourceEnergy b (u n-z n)≤
      4*(2:ℝ)^n*∑ j∈Finset.range n,finiteSourceEnergy b ((A j).comp (v j)-v (j+1)) := by
  have hp2 : ‖P‖^2≤1 := by nlinarith [norm_nonneg P]
  have hPA (j : ℕ) : ‖P.comp (A j)‖≤1 := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    nlinarith [norm_nonneg P,norm_nonneg (A j),hA j]
  have heu := recursive_leakage_energy b A u v hA hu0 hu n
  have hez := recursive_leakage_energy b (fun j => P.comp (A j)) z v hPA hz0 hz n
  have hterm (j : ℕ) (hj : j∈Finset.range n) :
      finiteSourceEnergy b ((P.comp (A j)).comp (v j)-v (j+1))≤
        finiteSourceEnergy b ((A j).comp (v j)-v (j+1)) := by
    have heq : (P.comp (A j)).comp (v j)-v (j+1)=
        P.comp ((A j).comp (v j)-v (j+1)) := by
      ext x
      have hf := congrArg (fun T : E →L[ℂ] H => T x)
        (hfix (j+1) (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))
      change P ((A j) (v j x))-v (j+1) x=P ((A j) (v j x)-v (j+1) x)
      rw [map_sub]
      exact congrArg (fun y => P ((A j) (v j x))-y) hf.symm
    rw [heq]
    exact (finiteSourceEnergy_left b P _).trans
      ((mul_le_mul_of_nonneg_right hp2 (finiteSourceEnergy_nonneg b _)).trans_eq (one_mul _))
  have hez' := hez.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity))
  have hneg : finiteSourceEnergy b (v n-z n)=finiteSourceEnergy b (z n-v n) := by
    unfold finiteSourceEnergy
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun r : ℝ => r^2) (norm_sub_rev _ _)
  have heq : u n-z n=(u n-v n)+(v n-z n) := by ext x; simp only [sub_apply,add_apply]; abel
  rw [heq]
  have he := finiteSourceEnergy_add b (u n-v n) (v n-z n)
  rw [hneg] at he
  nlinarith only [he,heu,hez']

#print axioms fixed_compression_energy

end QuantitativeMaass
