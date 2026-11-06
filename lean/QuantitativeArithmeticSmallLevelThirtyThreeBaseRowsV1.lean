module
public import QuantitativeArithmeticSmallLevelThirtyThreeLaurentDataV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeLaurent
open QuantitativeArithmeticSevenLaurentRows

def baseRows (σ : ℚ) (j : ℕ) : Poly :=
  if h : j<775 then normalizeLaurent (specializeSigns σ (sourceRows ⟨j,h⟩)) else []

theorem baseRows_eval (x y z a : ℂ) (σ : ℚ) (v : ℕ→ℂ) (i : Fin 775) :
    eval x y z 1 a 1 1 v (baseRows σ i)=eval x y z σ a 1 1 v (sourceRows i) := by
  rw [baseRows,dite_eq_left i.isLt,eval_normalizeLaurent,eval_specializeSigns]

#print axioms baseRows_eval
end QuantitativeArithmeticSmallLevelThirtyThreeLaurent
