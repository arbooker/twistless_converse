module

public import FinitenessRamanujanDivisorV1
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

@[expose] public section

set_option autoImplicit false

namespace FinitenessRamanujanArithmetic

open Complex Finset ArithmeticFunction FinitenessRamanujanSum FinitenessRamanujanDivisor
local notation "ζ" => (ArithmeticFunction.zeta : ArithmeticFunction ℂ)
local notation "μ" => (ArithmeticFunction.moebius : ArithmeticFunction ℂ)

noncomputable def asFunction (n : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun q => complexSum q n,by simp [complexSum,residues]⟩

noncomputable def indicator (n : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun q => if q ∣ n then (q:ℂ) else 0,by split_ifs <;> simp⟩

theorem zeta_product (n : ℕ) : asFunction n*ζ=indicator n := by
  ext q
  rw [coe_mul_zeta_apply]
  change (∑ d ∈ q.divisors, complexSum d n)=if q ∣ n then (q:ℂ) else 0
  by_cases hq : q=0
  · simp [hq]
  exact sum_divisors (Nat.pos_of_ne_zero hq) n

theorem moebius_product (n : ℕ) : asFunction n=indicator n*μ := by
  calc
    asFunction n=(asFunction n*ζ)*μ := by rw [mul_assoc,coe_zeta_mul_coe_moebius,mul_one]
    _ = indicator n*μ := by rw [zeta_product]

theorem indicator_multiplicative (n : ℕ) : (indicator n).IsMultiplicative := by
  constructor
  · simp [indicator]
  · intro a b hc
    change (if a*b ∣ n then ((a*b:ℕ):ℂ) else 0)=
      (if a ∣ n then (a:ℂ) else 0)*(if b ∣ n then (b:ℂ) else 0)
    by_cases ha : a ∣ n
    · by_cases hb : b ∣ n
      · simp [ha,hb,hc.mul_dvd_of_dvd_of_dvd ha hb]
      · have hab : ¬a*b ∣ n := fun h => hb (dvd_trans (dvd_mul_left b a) h)
        simp [hb,hab]
    · have hab : ¬a*b ∣ n := fun h => ha (dvd_trans (dvd_mul_right a b) h)
      simp [ha,hab]

theorem isMultiplicative (n : ℕ) : (asFunction n).IsMultiplicative := by
  rw [moebius_product]
  exact (indicator_multiplicative n).mul isMultiplicative_moebius.intCast

theorem multiplicative {q r : ℕ} (hc : q.Coprime r) (n : ℕ) :
    complexSum (q*r) n=complexSum q n*complexSum r n :=
  (isMultiplicative n).2 hc

theorem divisor_formula (q n : ℕ) :
    complexSum q n=∑ d ∈ q.divisors,
      ((ArithmeticFunction.moebius (q/d):ℤ):ℂ)*(if d ∣ n then (d:ℂ) else 0) := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f q) (moebius_product n)
  rw [mul_apply] at h
  change complexSum q n=∑ x ∈ q.divisorsAntidiagonal,
    (indicator n) x.1*((ArithmeticFunction.moebius x.2:ℤ):ℂ) at h
  rw [Nat.sum_divisorsAntidiagonal (fun x y => (indicator n) x*
    ((ArithmeticFunction.moebius y:ℤ):ℂ))] at h
  rw [h]
  apply sum_congr rfl
  intro d _
  change (if d ∣ n then (d:ℂ) else 0)*((ArithmeticFunction.moebius (q/d):ℤ):ℂ)=_
  ring

/-- Exact prime-power formula obtained by subtracting two adjacent
divisor sums. Valid also at n=0 and j=0. -/
theorem prime_power {p : ℕ} (hp : p.Prime) (j n : ℕ) :
    complexSum (p^(j+1)) n=
      (if p^(j+1) ∣ n then ((p^(j+1):ℕ):ℂ) else 0)-
      (if p^j ∣ n then ((p^j:ℕ):ℂ) else 0) := by
  have h0 := sum_divisors (pow_pos hp.pos j) n
  have h1 := sum_divisors (pow_pos hp.pos (j+1)) n
  rw [Nat.sum_divisors_prime_pow hp] at h0 h1
  rw [sum_range_succ] at h1
  linear_combination h1-h0

theorem unit_invariance {q m : ℕ} (hc : q.Coprime m) (n : ℕ) :
    complexSum q (n*m)=complexSum q n := by
  rw [divisor_formula,divisor_formula]
  apply sum_congr rfl
  intro d hd
  have hdm : d.Coprime m := hc.of_dvd_left (Nat.dvd_of_mem_divisors hd)
  simp only [hdm.dvd_mul_right]

theorem at_valuation {p n : ℕ} (hp : p.Prime) (hn : n≠0) (k : ℕ) :
    complexSum (p^k) n=complexSum (p^k) (p^(n.factorization p)) := by
  calc
    complexSum (p^k) n=complexSum (p^k) ((p^(n.factorization p))*(n/(p^(n.factorization p)))) := by
      rw [Nat.ordProj_mul_ordCompl_eq_self]
    _ = _ := unit_invariance ((Nat.coprime_ordCompl hp hn).pow_left k) _

theorem factorization {q : ℕ} (hq : q≠0) (n : ℕ) :
    complexSum q n=q.factorization.prod (fun p j => complexSum (p^j) n) :=
  (isMultiplicative n).multiplicative_factorization (asFunction n) hq

#print axioms multiplicative
#print axioms divisor_formula
#print axioms prime_power
#print axioms unit_invariance

end FinitenessRamanujanArithmetic
