module

public import QuantitativeArithmeticSparsePolynomialCertificateTheoryV4
public import SmallLevelIntegerPowerAbelTheoryV4

/-! Consolidated chapter: SmallLevelFourPrimePowerSum. Original declarations and local scopes are retained. -/

/-! ## SmallLevelFourPrimePowerSumV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelFourPrimePowerSum
open QuantitativeArithmeticSparsePolynomialCertificate SmallLevelIntegerPowerAbel

/-- Integer bases for the physical tuple (2^n,9^n,13^n,25^n).
The fifth polynomial exponent is reserved for an auxiliary variable. -/
def primeBase (e : Exponent) : ℕ :=
  2^e.1*9^e.2.1*13^e.2.2.1*25^e.2.2.2.1

def signedData (sx sz orientation : ℤ) (p : Poly) : List Datum :=
  p.map fun t => (primeBase t.2,orientation*t.1*sx^t.2.1*sz^t.2.2.2.1)

end SmallLevelFourPrimePowerSum
end
end

/-! ## SmallLevelFourPrimePowerSumPhysicalV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelFourPrimePowerSum
open Complex QuantitativeArithmeticSparsePolynomialCertificate SmallLevelIntegerPowerAbel

lemma pow_exchange (z : ℂ) (n j : ℕ) : (z^n)^j=(z^j)^n := by
  rw [←pow_mul,←pow_mul,Nat.mul_comm]

theorem monomial_physical (sx sz : ℤ) (n : ℕ) (e : Exponent) :
    monomial ((sx:ℂ)*(2:ℂ)^n) ((9:ℂ)^n) ((sz:ℂ)*(13:ℂ)^n) ((25:ℂ)^n) 1 e=
      (sx:ℂ)^e.1*(sz:ℂ)^e.2.2.1*(primeBase e:ℂ)^n := by
  simp only [monomial,primeBase,mul_pow,one_pow,mul_one,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [pow_exchange 2 n e.1,pow_exchange 9 n e.2.1,
    pow_exchange 13 n e.2.2.1,pow_exchange 25 n e.2.2.2.1]
  ring

/-- The exact integer power sum is the signed physical evaluation of the
same polynomial. This supplies the semantic link for the Abel certificates. -/
theorem signed_powerSum (sx sz orientation : ℤ) (n : ℕ) (p : Poly) :
    ((powerSum n (signedData sx sz orientation p):ℝ):ℂ)=
      (orientation:ℂ)*eval ((sx:ℂ)*(2:ℂ)^n) ((9:ℂ)^n)
        ((sz:ℂ)*(13:ℂ)^n) ((25:ℂ)^n) 1 p := by
  induction p with
  | nil => simp [signedData,powerSum]
  | cons t p ih =>
    rcases t with ⟨c,e⟩
    simp only [signedData,List.map_cons,powerSum,Complex.ofReal_add,Complex.ofReal_mul,
      Complex.ofReal_intCast,Complex.ofReal_pow,Complex.ofReal_natCast] at *
    rw [ih,eval_cons,monomial_physical]
    push_cast
    ring

theorem physical_eval_ne_zero (sx sz orientation : ℤ) (n : ℕ) (p : Poly)
    (h : powerSum n (signedData sx sz orientation p)≠0) :
    eval ((sx:ℂ)*(2:ℂ)^n) ((9:ℂ)^n) ((sz:ℂ)*(13:ℂ)^n) ((25:ℂ)^n) 1 p≠0 := by
  intro hz
  have he:=signed_powerSum sx sz orientation n p
  rw [hz,mul_zero] at he
  exact h (Complex.ofReal_eq_zero.mp he)

#print axioms signed_powerSum
#print axioms physical_eval_ne_zero
end SmallLevelFourPrimePowerSum
end
end
