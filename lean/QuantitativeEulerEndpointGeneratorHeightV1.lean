module

public import QuantitativeEulerEndpointRightStackV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix QuantitativeArithmetic QuantitativeHolomorphic QuantitativeEulerDensityGenerators
open scoped Classical MatrixGroups

def generatorHeight (N : ℕ) [NeZero N] : ℝ :=
  1+∑ γ : Generator N, fixedMatrixHeight γ.val.val

theorem generatorHeight_one_le (N : ℕ) [NeZero N] : 1≤generatorHeight N := by
  have h := Finset.sum_nonneg (fun γ (_ : γ∈(Finset.univ : Finset (Generator N))) =>
    fixedMatrixHeight_nonneg γ.val.val)
  unfold generatorHeight
  linarith

theorem generatorHeight_bound (N : ℕ) [NeZero N] (γ : Generator N) :
    MatrixEntryBound γ.val.val (generatorHeight N) := by
  apply entry_bound_mono (fixedMatrixHeight_bounds _)
  have h := Finset.single_le_sum (fun δ _ => fixedMatrixHeight_nonneg δ.val.val)
    (Finset.mem_univ γ)
  exact h.trans (by unfold generatorHeight; linarith)

theorem generatorHeight_identity (N : ℕ) [NeZero N] :
    MatrixEntryBound (1 : SL(2,ℤ)).val (generatorHeight N) := by
  have h : MatrixEntryBound (1 : IntegerMatrix2) 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  exact entry_bound_mono h (generatorHeight_one_le N)

/-- One fixed coefficient controls both the unmultiplied family residual
and every generator-multiplied family residual. -/
def generatorTransportConstant {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold) : ℝ :=
  2*transportConstant P*generatorHeight N

theorem generatorTransportConstant_pos {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold) :
    0<generatorTransportConstant P :=
  mul_pos (mul_pos (by norm_num) (transportConstant_pos P))
    (lt_of_lt_of_le zero_lt_one (generatorHeight_one_le N))

theorem generator_transport_height {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) (q : ℕ) :
    2*(localTransportConstant P a i*(q : ℝ)^4)*generatorHeight N≤
      generatorTransportConstant P*(q : ℝ)^4 := by
  calc
    _ ≤ 2*(transportConstant P*(q : ℝ)^4)*generatorHeight N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (localTransportConstant_le P a i) (by positivity))
        (by norm_num)) ((by norm_num : (0 : ℝ)≤1).trans (generatorHeight_one_le N))
    _ = _ := by unfold generatorTransportConstant; ring

#print axioms generatorHeight_bound
#print axioms generatorTransportConstant_pos
#print axioms generator_transport_height
end QuantitativeEulerEndpointPrepared
