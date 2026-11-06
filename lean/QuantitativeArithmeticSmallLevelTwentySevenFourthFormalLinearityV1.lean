module
public import QuantitativeArithmeticSmallLevelTwentySevenFourthNormalizedShiftV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily

private theorem eval_scalar (x y z w a b c t : ℂ) (v : ℕ → ℂ)
    (p : QuantitativeArithmeticSevenLaurentRows.Poly) :
    QuantitativeArithmeticSevenLaurentRows.eval x y z w a b c (fun j => t*v j) p=
      t*QuantitativeArithmeticSevenLaurentRows.eval x y z w a b c v p := by
  induction p with
  | nil => simp
  | cons e p ih => simp only [QuantitativeArithmeticSevenLaurentRows.eval_cons,ih]; ring

theorem formalRow_scalar (r : Source) (ε : ℚ) (x y z w a b c t : ℂ) (v : ℕ → ℂ) :
    formalRow r ε x y z w a b c (fun j => t*v j)=t*formalRow r ε x y z w a b c v := by
  cases r with
  | old u => exact eval_scalar x y z w a b c t v _
  | matrix u hu obs ho => simp only [formalRow,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading]; ring
  | ramanujan u hu obs ho =>
    simp only [formalRow,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,sampleEval_scalar]
    ring
  | hecke u hu =>
    simp only [formalRow,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,← Finset.mul_sum]
    split_ifs <;> ring
  | entire p hp => exact eval_scalar x y z w a b c t v p

theorem matrixHigher_scalar (r : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec) (x y z w t : ℂ) (n : ℕ) (v : ℕ → ℂ) :
    matrixHigher r x y z w n (fun j => t*v j)=t*matrixHigher r x y z w n v := by
  unfold matrixHigher
  ring

theorem ramanujanHigher_scalar (r : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec) (ε : ℚ) (x y z w t : ℂ) (n : ℕ) (v : ℕ → ℂ) :
    ramanujanHigher r ε x y z w n (fun j => t*v j)=t*ramanujanHigher r ε x y z w n v := by
  unfold ramanujanHigher
  rw [sampleEval_scalar]
  ring

theorem formalHigher_scalar (r : Source) (ε : ℚ) (x y z w t : ℂ) (n : ℕ) (v : ℕ → ℂ) :
    formalHigher r ε x y z w n (fun j => t*v j)=t*formalHigher r ε x y z w n v := by
  cases r with
  | old u =>
    cases u with
    | matrix j => exact matrixHigher_scalar _ x y z w t n v
    | ramanujan j => exact ramanujanHigher_scalar _ ε x y z w t n v
    | hecke j hj => simp only [formalHigher,mul_zero]
    | entire j => simp only [formalHigher,mul_zero]
  | matrix u hu obs ho => exact matrixHigher_scalar u x y z w t n v
  | ramanujan u hu obs ho => exact ramanujanHigher_scalar u ε x y z w t n v
  | hecke u hu => simp only [formalHigher,mul_zero]
  | entire p hp => simp only [formalHigher,mul_zero]
#print axioms formalRow_scalar
#print axioms formalHigher_scalar
end QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
