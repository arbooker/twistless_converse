module
public import QuantitativeArithmeticSmallLevelTwentySevenPoleSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenSourceShiftMatrixV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
open Matrix
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
open QuantitativeArithmeticSmallLevelTwentySevenShiftSource (basisValues observation_basis)
open QuantitativeArithmeticSmallLevelTwentySevenObservation (factorMatrix observation)
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages (primeRate primeRate_analytic primeRate_nonzero)

/-- Source specifications contain rational geometric checks, together with an
explicit expression of the shifted sample in the already continued observations. -/
inductive Source where
  | old (r : QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.Kind)
  | matrix (r : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec) (valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point r)
      (obs : Fin 553) (observed : ∀ v : ℕ → ℂ,
        QuantitativeArithmeticRationalRows.eval v (observation obs)=v r.right)
  | ramanujan (r : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec) (valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point r)
      (obs : Fin 553) (observed : ∀ v : ℕ → ℂ,
        QuantitativeArithmeticRationalRows.eval v (observation obs)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval r.q r.right v)
  | hecke (r : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec) (valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point r)
  | entire (p : QuantitativeArithmeticSevenLaurentRows.Poly)
      (original : ∀ (m : ℕ), 0<m → ∀ {f : ℕ → ℂ},
        FinitenessOriginalInput.IsSolution 27 (2*m) f →
        ∃ (B : ℝ) (E : ℂ → ℂ), Differentiable ℂ E ∧
          ∀ s : ℂ, B<s.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval p m f s=E s)

def matrixCoefficient (r : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec) (m n : ℕ) (s : ℂ) : ℂ :=
  (primeRate 2 m s^r.e₂*primeRate 3 m s^r.e₃*
    primeRate 5 m s^r.e₅*primeRate 7 m s^r.e₇)*
    (Complex.I*((QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry r.word 1 0:ℂ)*(QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.denominator point r:ℂ)))^(n+1)*
    Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1)

def ramanujanCoefficient (r : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  SmallLevelTaylor.taylorRowScalar (2*m) (Nat.lcm 27 (r.q^2))
    ((r.t:ℝ)/r.Q) η (n+1) s

def row (r : Source) (m : ℕ) (f : ℕ → ℂ) (η s : ℂ) : ℂ :=
  match r with
  | .old t => QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.row t m f η s
  | .matrix t _ _ _ => QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.leading t m s
      (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)
  | .ramanujan t _ _ _ => QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.leading t m η s
      (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)
  | .hecke t _ => QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.leading t m f s
      (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)
  | .entire p _ => QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval p m f s

def shift (r : Source) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (v : ℕ → ℂ) : ℂ :=
  match r with
  | .old t => QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.kindShift t m η n s v
  | .matrix t _ _ _ => QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.shift point t m n s v
  | .ramanujan t _ _ _ => QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.shift t m η n s v
  | .hecke _ _ => 0
  | .entire _ _ => 0

def coefficient (r : Source) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (j : Fin 321) : ℂ :=
  match r with
  | .old t => QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.kindCoefficient t m η n s j
  | .matrix t _ obs _ => matrixCoefficient t m n s*factorMatrix obs j
  | .ramanujan t _ obs _ => ramanujanCoefficient t m η n s*factorMatrix obs j
  | .hecke _ _ => 0
  | .entire _ _ => 0

theorem shift_action (r : Source) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (v : ℕ → ℂ) :
    (∑ j : Fin 321, coefficient r m η n s j*basisValues v j)=shift r m η n s v := by
  cases r with
  | old t => exact QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.kindShift_action t m η n s v
  | matrix t ht obs ho =>
    change (∑ j : Fin 321, (matrixCoefficient t m n s*factorMatrix obs j)*basisValues v j)=_
    rw [QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.weighted_factor,← observation_basis,ho]
    rfl
  | ramanujan t ht obs ho =>
    change (∑ j : Fin 321, (ramanujanCoefficient t m η n s*factorMatrix obs j)*basisValues v j)=_
    rw [QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.weighted_factor,← observation_basis,ho]
    rfl
  | hecke t ht => simp [coefficient,shift]
  | entire p hp => simp [coefficient,shift]

theorem coefficient_analytic (r : Source) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (j : Fin 321) :
    AnalyticAt ℂ (fun z => coefficient r m η n z j) s := by
  cases r with
  | old t => exact QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.kindCoefficient_analytic t m η n s j
  | matrix t ht obs ho =>
    have h2 := (primeRate_analytic 2 m s).zpow (primeRate_nonzero 2 m s) (n := t.e₂)
    have h3 := (primeRate_analytic 3 m s).zpow (primeRate_nonzero 3 m s) (n := t.e₃)
    have h5 := (primeRate_analytic 5 m s).zpow (primeRate_nonzero 5 m s) (n := t.e₅)
    have h7 := (primeRate_analytic 7 m s).zpow (primeRate_nonzero 7 m s) (n := t.e₇)
    exact (((((h2.mul h3).mul h5).mul h7).mul analyticAt_const).mul
      (SmallLevelTaylor.binomial_shift_analytic (2*m) (n+1) s)).mul analyticAt_const
  | ramanujan t ht obs ho =>
    apply AnalyticAt.mul _ analyticAt_const
    apply SmallLevelTaylor.taylorRowScalar_analytic
    · exact_mod_cast Nat.lcm_pos (by decide : 0<27) (pow_pos ht.2.1 2)
    · exact div_ne_zero (by exact_mod_cast ht.2.2.2.1) (by exact_mod_cast ht.1.ne')
  | hecke t ht => exact analyticAt_const
  | entire p hp => exact analyticAt_const
#print axioms shift_action
#print axioms coefficient_analytic
end QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
