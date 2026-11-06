module
public import QuantitativeArithmeticSmallLevelTwentySevenShiftSourceMatrixTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenShiftSourceRamanujanTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenShiftSource
open _root_.Matrix QuantitativeArithmeticRationalRows
open QuantitativeArithmeticSmallLevelTwentySevenObservation
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)

def basisValues (v : ℕ → ℂ) : Fin 321 → ℂ := fun i => eval v (basis i.val)

theorem observation_basis (v : ℕ → ℂ) (i : Fin 553) :
    eval v (observation i)=(factorMatrix *ᵥ basisValues v) i := by
  have hh := observation_factorization v i
  have hb : ∀ t∈factor i, t.2<321 := by
    intro t ht
    exact of_decide_eq_true (List.all_eq_true.mp (factor_indices i) t ht)
  rw [eval_bounded_eq_sum _ _ hb] at hh
  exact hh

namespace Ramanujan

def coefficient (i : Fin 192) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  SmallLevelTaylor.taylorRowScalar (2*m) (Nat.lcm 27 ((selected i).q^2))
    (((selected i).t:ℝ)/(selected i).Q) η (n+1) s

theorem shift_factor (i : Fin 192) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (v : ℕ → ℂ) :
    QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.shift (selected i) m η n s v=
      coefficient i m η n s*(factorMatrix *ᵥ basisValues v) (obs i) := by
  unfold QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.shift
  rw [← all_observed v i,observation_basis]
  rfl

theorem coefficient_analytic (i : Fin 192) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (coefficient i m η n) s := by
  have hv : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point (selected i) :=
    QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.selected_valid _
  apply SmallLevelTaylor.taylorRowScalar_analytic
  · exact_mod_cast Nat.lcm_pos (by decide : 0<27) (pow_pos hv.2.1 2)
  · exact div_ne_zero (by exact_mod_cast hv.2.2.2.1) (by exact_mod_cast hv.1.ne')
end Ramanujan

namespace Matrix

def coefficient (i : Fin 119) (m n : ℕ) (s : ℂ) : ℂ :=
  (primeRate 2 m s^(selected i).e₂*primeRate 3 m s^(selected i).e₃*
    primeRate 5 m s^(selected i).e₅*primeRate 7 m s^(selected i).e₇)*
    (Complex.I*((QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry (selected i).word 1 0:ℂ)*
      (QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.denominator point (selected i):ℂ)))^(n+1)*
    Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1)

theorem shift_factor (i : Fin 119) (m n : ℕ) (s : ℂ) (v : ℕ → ℂ) :
    QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.shift point (selected i) m n s v=
      coefficient i m n s*(factorMatrix *ᵥ basisValues v) (obs i) := by
  unfold QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.shift
  rw [← all_observed v i,observation_basis]
  rfl

theorem coefficient_analytic (i : Fin 119) (m n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (coefficient i m n) s := by
  have h2 := (primeRate_analytic 2 m s).zpow (primeRate_nonzero 2 m s) (n := (selected i).e₂)
  have h3 := (primeRate_analytic 3 m s).zpow (primeRate_nonzero 3 m s) (n := (selected i).e₃)
  have h5 := (primeRate_analytic 5 m s).zpow (primeRate_nonzero 5 m s) (n := (selected i).e₅)
  have h7 := (primeRate_analytic 7 m s).zpow (primeRate_nonzero 7 m s) (n := (selected i).e₇)
  exact ((((h2.mul h3).mul h5).mul h7).mul analyticAt_const).mul
    (SmallLevelTaylor.binomial_shift_analytic (2*m) (n+1) s)
end Matrix
#print axioms observation_basis
#print axioms Ramanujan.shift_factor
#print axioms Ramanujan.coefficient_analytic
#print axioms Matrix.shift_factor
#print axioms Matrix.coefficient_analytic
end QuantitativeArithmeticSmallLevelTwentySevenShiftSource
