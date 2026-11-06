module
public import QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamilyModelV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages (primeRate)

def formalRow (r : Source) (ε : ℚ) (x y z w a b c : ℂ) (v : ℕ → ℂ) : ℂ :=
  match r with
  | .old t => eval x y z w a b c v (QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.signedPoly ε t)
  | .matrix t _ _ _ => QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading t x y z w v
  | .ramanujan t _ _ _ => QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading t x y z w (ε:ℂ) v
  | .hecke t _ => QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading t x y z w a b c v
  | .entire p _ => eval x y z w a b c v p

theorem formalRow_physical (r : Source) (ε : ℚ) (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) (s : ℂ) :
    formalRow r ε (primeRate 2 m s) (primeRate 3 m s) (primeRate 5 m s) (primeRate 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 5:ℂ)*f 5) ((Real.sqrt 7:ℂ)*f 7)
      (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)=row r m f (ε:ℂ) s := by
  cases r with
  | old t => exact QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physical_signed ε t m f s
  | matrix t ht obs ho => rfl
  | ramanujan t ht obs ho => exact (QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.physical_leading point t ht m (ε:ℂ) s _).symm
  | hecke t ht =>
    have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
    simpa only [formalRow,row] using QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal t ht.2.2.2.1 m f h3 s
      (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)
  | entire p hp => rfl

#print axioms formalRow_physical
end QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
