module
public import QuantitativeArithmeticSmallLevelTwentySevenSourceDispatchV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
open Matrix
open QuantitativeArithmeticSmallLevelTwentySevenObservation
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
open QuantitativeArithmeticSmallLevelTwentySevenShiftSource (basisValues)

def kindCoefficient (r : Kind) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (j : Fin 321) : ℂ :=
  match r with
  | .hecke _ _ => 0
  | .ramanujan i => QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.coefficient i m η n s*factorMatrix (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.obs i) j
  | .matrix i => QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix.coefficient i m n s*factorMatrix (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix.obs i) j
  | .entire _ => 0

def coefficient (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin 550) (Fin 321) ℂ :=
  fun i => kindCoefficient (kind i) m η n s

def kindShift (r : Kind) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (v : ℕ → ℂ) : ℂ :=
  match r with
  | .hecke _ _ => 0
  | .ramanujan i => QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.shift (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected i) m η n s v
  | .matrix i => QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.shift point (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix.selected i) m n s v
  | .entire _ => 0

theorem kindCoefficient_analytic (r : Kind) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (j : Fin 321) :
    AnalyticAt ℂ (fun z => kindCoefficient r m η n z j) s := by
  cases r with
  | hecke i h => exact analyticAt_const
  | ramanujan i => exact (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.coefficient_analytic i m η n s).mul analyticAt_const
  | matrix i => exact (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix.coefficient_analytic i m n s).mul analyticAt_const
  | entire i => exact analyticAt_const

theorem coefficient_analytic (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (i : Fin 550) (j : Fin 321) :
    AnalyticAt ℂ (fun z => coefficient m η n z i j) s :=
  kindCoefficient_analytic (kind i) m η n s j

theorem weighted_factor (c : ℂ) (i : Fin 553) (v : Fin 321 → ℂ) :
    (∑ j : Fin 321, (c*factorMatrix i j)*v j)=c*(factorMatrix *ᵥ v) i := by
  change _=c*∑ j : Fin 321, factorMatrix i j*v j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem kindShift_action (r : Kind) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (v : ℕ → ℂ) :
    (∑ j : Fin 321, kindCoefficient r m η n s j*basisValues v j)=kindShift r m η n s v := by
  cases r with
  | hecke i h => simp [kindCoefficient,kindShift]
  | ramanujan i =>
    change (∑ j : Fin 321, (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.coefficient i m η n s*factorMatrix (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.obs i) j)*basisValues v j)=_
    rw [weighted_factor]
    exact (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.shift_factor i m η n s v).symm
  | matrix i =>
    change (∑ j : Fin 321, (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix.coefficient i m n s*factorMatrix (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix.obs i) j)*basisValues v j)=_
    rw [weighted_factor]
    exact (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix.shift_factor i m n s v).symm
  | entire i => simp [kindCoefficient,kindShift]

theorem shift_action (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (v : ℕ → ℂ) (i : Fin 550) :
    (coefficient m η n s *ᵥ basisValues v) i=kindShift (kind i) m η n s v :=
  kindShift_action (kind i) m η n s v
#print axioms coefficient_analytic
#print axioms shift_action
end QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
