module

public import AsymptoticClassicalMellinSplitV1
public import AsymptoticClassicalAxisDecayV1
public import AsymptoticClassicalLSeriesV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalLSeries

open UpperHalfPlane Complex ConjAct AsymptoticClassicalCusp
open scoped Pointwise

/-- The classical cusp Mellin transform has finite order, as follows
 from exponential decay of the two tails in its functional-equation pair. -/
theorem lambda_finiteOrder {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} (hk : 0 < k) (f : CuspForm Γ k) :
    FinitenessFiniteOrder.Bound (ModularForm.Λ hk f) := by
  let ΓS := toConjAct (ModularGroup.S : GL (Fin 2) ℝ)⁻¹ • Γ
  let : ΓS.IsArithmetic := by
    convert Subgroup.IsArithmetic.conj Γ ↑(ModularGroup.S⁻¹)
    simp only [ModularGroup.S_inv, ← map_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.S]
  let g : CuspForm ΓS k := CuspForm.translate f (ModularGroup.S : GL (Fin 2) ℝ)
  obtain ⟨Cf, cf, hCf, hcf, hf⟩ := cusp_axis_exponential_bound f
  obtain ⟨Cg, cg, hCg, hcg, hg⟩ := cusp_axis_exponential_bound g
  exact strongPair_finiteOrder (ModularForm.weakFEPair hk f) (CuspForm.isStrongFEPair hk f)
    hCf hCg hcf hcg hf hg

theorem conductor_finiteOrder (N : ℕ) (hN : 0 < N) :
    FinitenessFiniteOrder.Bound (fun s : ℂ => (N : ℂ) ^ ((s - 1 / 2) / 2)) := by
  have hnC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hb := FinitenessInputBounds.bound_shift
    (FinitenessFiniteOrder.exp_linear (Real.log (N : ℝ) / 2)) (-(1 / 2 : ℂ))
  convert hb using 1
  funext s
  rw [Complex.cpow_def_of_ne_zero hnC]
  have hl : Complex.log (N : ℂ) = (Real.log (N : ℝ) : ℂ) := by simp
  rw [hl]
  congr 1
  push_cast
  ring

/-- The actual normalized entire continuation meets the finite-order
 condition in the paper's complex Euler-product definition. -/
theorem entireCompletion_finiteOrder (N k : ℕ) [NeZero N] (hk : 0 < k)
    (f : CuspForm (level N) (k : ℤ)) :
    FinitenessOriginalInput.FiniteOrder (entireCompletion N k hk f) := by
  apply FinitenessInputBounds.bound_finiteOrder
  have hΛ := FinitenessInputBounds.bound_shift
    (lambda_finiteOrder (by exact_mod_cast hk : (0 : ℤ) < k) f) (((k : ℂ) - 1) / 2)
  exact FinitenessFiniteOrder.mul
    (FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const 2)
      (conductor_finiteOrder N (Nat.pos_of_ne_zero (NeZero.ne N)))) hΛ

#print axioms lambda_finiteOrder
#print axioms conductor_finiteOrder
#print axioms entireCompletion_finiteOrder

end AsymptoticClassicalLSeries
