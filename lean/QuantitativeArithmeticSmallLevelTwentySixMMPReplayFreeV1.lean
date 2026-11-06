module
public import SmallLevelTwentySixUnitMMPFreeKernelTheoryV4
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPReplay
open SmallLevelTwentySixUnitMMP

/-- The Taylor replay uses coordinate300 in place of520. The triangular
source relation changes between them by the nonzero factor Y²/Z. -/
theorem source_zero_of_replay_free (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h300 : v 300=0) (h540 : v 540=0) : ∀ j : Fin 320,v (support j)=0 := by
  have h := pivot_150 X Y Z W a b hX hY hZ hW v hv
  simp only [h300,mul_zero,zero_add,one_mul] at h
  have h520 := (mul_eq_zero.mp h).resolve_left (div_ne_zero (pow_ne_zero 2 hY) hZ)
  exact FreeKernel.source_zero_of_free X Y Z W a b hX hY hZ hW v hv h520 h540

#print axioms source_zero_of_replay_free
end QuantitativeArithmeticSmallLevelTwentySixMMPReplay
