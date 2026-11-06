module
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxSymbolicRowsV1
public import FinitenessOriginalTwistLocalV1
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData

private theorem parameter_nonzero (p m : ℕ) (hp : p≠0) (s : ℂ) : primeParameter p m s≠0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))

private theorem parameter_inverse (p m : ℕ) (s : ℂ) :
    (p:ℂ)^((m:ℂ)-s)=(primeParameter p m s)⁻¹ := by
  unfold primeParameter
  rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]

private theorem grid_prime {p : ℕ} (hp : p.Prime) (hpQ : p∣1050) :
    p=2 ∨ p=3 ∨ p=5 ∨ p=7 := by
  have h := hp.mem_primeFactors hpQ (by decide : 1050≠0)
  have he : Nat.primeFactors 1050={2,3,5,7} := by decide +kernel
  simpa only [he,Finset.mem_insert,Finset.mem_singleton] using h

/-- The sparse source polynomials are the genuine leading Fricke/Hecke rows.
In particular the ramified Hecke coefficient is derived from the original
Euler product, rather than stipulated in the polynomial model. -/
theorem eval_rawSourcePoly (r : SourceRow) {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε s : ℂ) (χ : ℚ) (hχ : ε*I^(2*m)=(χ:ℂ)) (v : Fin 1050 → ℂ) :
    eval (primeParameter 2 m s) (primeParameter 3 m s)
      (primeParameter 5 m s) (primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 7:ℂ)*f 7)
      (periodicVector v) (rawSourcePoly χ r)=sourceLeading r m f ε s v := by
  have hx := parameter_nonzero 2 m (by decide) s
  have hy := parameter_nonzero 3 m (by decide) s
  have hz := parameter_nonzero 5 m (by decide) s
  have hw := parameter_nonzero 7 m (by decide) s
  have h5 : f 5=0 := FinitenessOriginalTwistLocal.bad_parameter_zero
    hf.toEulerData (by decide : Nat.Prime 5) (by decide)
  cases r with
  | old j =>
    rw [rawSourcePoly,eval_unitPoly]
    simp only [sourceLeading,periodicVector,Nat.mod_eq_of_lt (show 7*j.val<1050 by omega)]
  | physical r =>
    cases r with
    | word r =>
      simp only [rawSourcePoly,eval_append,eval_shift _ _ _ _ _ _ _ _ hx hy hz hw,
        eval_gridPoly,sourceLeading,leading,coefficient_leading,hχ,
        Rat.cast_neg,Rat.cast_pow,monomial,primeExponent,pow_zero,mul_one,fourPrimeMonomial]
      ring
    | taylor r =>
      simp only [rawSourcePoly,eval_append,eval_shift _ _ _ _ _ _ _ _ hx hy hz hw,
        eval_samplePoly,sourceLeading,leading,taylor_certificate_leading,
        QuantitativeArithmeticSmallLevelTwentyFive.GridSystem.phaseRoot,hχ,
        Rat.cast_neg,monomial,primeExponent,pow_zero,mul_one,fourPrimeMonomial]
      ring
    | entire q hq hd => exact eval_samplePoly _ _ _ _ _ _ _ v q 0
    | infinity w j hc hd => exact eval_gridPoly _ _ _ _ _ _ _ v j
    | hecke p hp hd j =>
      rcases grid_prime hp hd with rfl|rfl|rfl|rfl
      all_goals
        simp only [rawSourcePoly,heckePoly,sourceLeading,leading,fullHeckeRow,
          eval_append,eval_completePoly,eval_shift _ _ _ _ _ _ _ _ hx hy hz hw,
          eval_gridPoly,parameter_inverse,monomial,h5]
        norm_num only [eval_append,eval_shift _ _ _ _ _ _ _ _ hx hy hz hw,
          eval_gridPoly,monomial,ite_true,ite_false,show ¬(2:ℕ)=3 by decide,
          show ¬(2:ℕ)=7 by decide,show ¬(3:ℕ)=2 by decide,show ¬(3:ℕ)=7 by decide,
          show ¬(5:ℕ)=2 by decide,show ¬(5:ℕ)=3 by decide,show ¬(5:ℕ)=7 by decide,
          show ¬(7:ℕ)=2 by decide,show ¬(7:ℕ)=3 by decide,
          show ¬(2:ℕ)∣25 by decide,show ¬(3:ℕ)∣25 by decide,show (5:ℕ)∣25 by decide,
          show ¬(7:ℕ)∣25 by decide,pow_zero,pow_one,zpow_zero,zpow_neg_one,
          zpow_neg,zpow_ofNat,Rat.cast_one,Rat.cast_neg,eval_nil]
        ring

def sourceTailFactor (r : SourceRow) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  match r with
  | .physical (.word r) => coefficient r m (ε*I^(2*m)) (n+1) s
  | .physical (.taylor r) => taylorCoefficient 1050 (2*m) f ε r.q r.source (n+1) s
  | _ => 0

/-- All higher Taylor terms have the same source-free row support, evaluated
at the shifted argument. The scalar Taylor coefficient need not be divided out. -/
theorem eval_rawTailPoly (r : SourceRow) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (n : ℕ) (s x y z w a b c : ℂ) (v : Fin 1050 → ℂ) :
    sourceShifted r m f ε n s v=sourceTailFactor r m f ε n s*
      eval x y z w a b c (periodicVector v) (rawTailPoly r) := by
  cases r with
  | old j => simp [sourceShifted,sourceTailFactor]
  | physical r =>
    cases r <;> simp only [sourceShifted,shifted,sourceTailFactor,rawTailPoly,
      eval_gridPoly,eval_samplePoly,zero_mul]

#print axioms eval_rawSourcePoly
#print axioms eval_rawTailPoly
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
