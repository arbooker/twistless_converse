module
public import QuantitativeArithmeticSmallLevelTwentySevenSourceDispatchV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenOriginalSystemV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages (inputs primeRate primeRate_nonzero)
open QuantitativeArithmeticSmallLevelTwentySevenObservation (observation)
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point physicalRow)

theorem eval_lift (x y z w a b c : ℂ) (v : ℕ → ℂ) (p : QuantitativeArithmeticRationalRows.Row) :
    eval x y z w a b c v (liftRationalRow p)=QuantitativeArithmeticRationalRows.eval v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [liftRationalRow,List.map_cons,eval_cons,QuantitativeArithmeticRationalRows.eval_cons] at *
    rw [ih]
    simp [monomial]

def signedPoly (ε : ℚ) (r : Kind) : Poly :=
  if ε=1 then inputs (source r) else
    match r with
    | .ramanujan j => mergeFuel 20000 (inputs (source r))
        (shift (1-ε) ((QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected j).e₂,(QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected j).e₃,(QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected j).e₅,(QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected j).e₇,0,0,0)
          (liftRationalRow (observation (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.obs j))))
    | _ => inputs (source r)

def physicalEval (p : Poly) (m : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  eval (primeRate 2 m s) (primeRate 3 m s) (primeRate 5 m s) (primeRate 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 5:ℂ)*f 5) ((Real.sqrt 7:ℂ)*f 7)
    (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s) p

theorem physical_signed (ε : ℚ) (r : Kind) (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    physicalEval (signedPoly ε r) m f s=row r m f (ε:ℂ) s := by
  by_cases he : ε=1
  · subst ε
    simp only [signedPoly,ite_true,Rat.cast_one]
    exact (row_one r m f s).symm
  · cases r with
    | hecke j hj => simp only [signedPoly,ite_eq_right he,physicalEval,physicalRow,row,source]
    | entire j => simp only [signedPoly,ite_eq_right he,physicalEval,physicalRow,row,source]
    | matrix j => simpa only [signedPoly,ite_eq_right he,physicalEval,physicalRow,row,source] using (row_one (.matrix j) m f s).symm
    | ramanujan j =>
      unfold physicalEval
      rw [signedPoly,ite_eq_right he]
      rw [eval_mergeFuel,eval_shift _ _ _ _ _ _ _ _
        (primeRate_nonzero 2 m s) (primeRate_nonzero 3 m s)
        (primeRate_nonzero 5 m s) (primeRate_nonzero 7 m s),eval_lift]
      have hp := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.selected_physical (ramanujanIndex j) m f s
      change physicalRow point (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected j).source m f s=
        QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.leading (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected j) m 1 s (fun n => SmallLevelAdditive.original (2*m) f (point n:ℝ) s) at hp
      change physicalRow point (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected j).source m f s+_=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.leading (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected j) m ε s _
      rw [hp,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.all_observed]
      rw [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.physical_leading point (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected j) (QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.selected_valid (ramanujanIndex j)) m 1 s,
        QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.physical_leading point (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected j) (QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.selected_valid (ramanujanIndex j)) m ε s]
      simp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,monomial,pow_zero,mul_one,Rat.cast_sub,Rat.cast_one]
      ring

theorem physical_zero_signed (ε : ℚ) (r : Kind) (m : ℕ) (f : ℕ → ℂ) (hf2 : f 2=0) (s : ℂ) :
    physicalEval (zeroA (signedPoly ε r)) m f s=row r m f (ε:ℂ) s := by
  unfold physicalEval
  rw [eval_zeroA]
  have h := physical_signed ε r m f s
  simpa only [physicalEval,hf2,mul_zero] using h
#print axioms physical_signed
#print axioms physical_zero_signed
end QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
