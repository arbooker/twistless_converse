module
public import SmallLevelTwentySixWeightAbelMMPDataV1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixWeightAbelMMP.MM
open SmallLevelIntegerPowerAbel SmallLevelFourPrimePowerSum
def data : List Datum := signedData (-1) (-1) (1) terms
theorem bounds : boundsGood 105741618458486400 data=true := by decide +kernel
theorem prefixes : prefixesGood 1 0 data=true := by decide +kernel
theorem strict_total : 0<total 1 0 data := by decide +kernel
theorem finite_nonzero : ∀ n : Fin 1,1≤n.val → total n.val 0 data≠0 := by decide +kernel

theorem power_sum_nonzero (n : ℕ) (hn : 1≤n) : powerSum n data≠0 := by
  by_cases hm : 1≤n
  · exact ne_of_gt (positive_from_threshold 1 n 105741618458486400 data hm
      (by norm_num) bounds prefixes strict_total)
  · apply powerSum_ne_zero_of_total
    exact finite_nonzero ⟨n,by omega⟩ hn

#print axioms power_sum_nonzero
end SmallLevelTwentySixWeightAbelMMP.MM
