module
public import QuantitativeArithmeticPrimePowerTorsionV1
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
set_option autoImplicit false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticPrimePowerTorsion
open Complex
open scoped ComplexConjugate

private theorem nat_cpow_conjugate {p : ℕ} (hp : p≠0) (u : ℂ) :
    (p:ℂ)^(conj u)=conj ((p:ℂ)^u) := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp
  have hl : Complex.log (p:ℂ)=(Real.log (p:ℝ):ℂ) := by simp
  simp only [Complex.cpow_def_of_ne_zero hp0,hl,← Complex.exp_conj,map_mul,
    Complex.conj_ofReal]

/-- Real values at two distinct positive primes force a real exponent. -/
theorem distinct_primes_cpow_real {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (u : ℂ) (hpu : ((p:ℂ)^u).im=0)
    (hqu : ((q:ℂ)^u).im=0) : u.im=0 := by
  have one_relation (r : ℕ) (hr : r≠0) (hru : ((r:ℂ)^u).im=0) :
      (r:ℂ)^(u-conj u)=1 := by
    have hr0 : (r:ℂ)≠0 := by exact_mod_cast hr
    have hc : (r:ℂ)^(conj u)=(r:ℂ)^u := by
      rw [nat_cpow_conjugate hr]
      apply Complex.ext <;> simp [hru]
    rw [Complex.cpow_sub _ _ hr0,hc,
      div_self (Complex.cpow_ne_zero_iff.mpr (Or.inl hr0))]
  have h := distinct_primes_cpow_one hp hq hpq (u-conj u)
    (one_relation p hp.ne_zero hpu) (one_relation q hq.ne_zero hqu)
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im,Complex.conj_im,Complex.zero_im] at hi
  linarith

/-- In fact both real prime-power values must be positive. -/
theorem distinct_primes_cpow_positive {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (u : ℂ) (hpu : ((p:ℂ)^u).im=0)
    (hqu : ((q:ℂ)^u).im=0) : 0<((p:ℂ)^u).re := by
  have hu := distinct_primes_cpow_real hp hq hpq u hpu hqu
  have he : (u.re:ℂ)=u := by apply Complex.ext <;> simp [hu]
  have hpow := congrArg Complex.re (Complex.ofReal_cpow (Nat.cast_nonneg p) u.re)
  have hpEq : ((p:ℂ)^u).re=(p:ℝ)^u.re := by
    simpa [he] using hpow.symm
  rw [hpEq]
  exact Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _

/-- A negative real value at one prime excludes a real value at another. -/
theorem negative_prime_cpow_excludes_real {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (u : ℂ) (r : ℝ) (hr : r<0) (hpu : (p:ℂ)^u=(r:ℂ))
    (hqu : ((q:ℂ)^u).im=0) : False := by
  have hi : ((p:ℂ)^u).im=0 := by rw [hpu]; rfl
  have hpos := distinct_primes_cpow_positive hp hq hpq u hi hqu
  rw [hpu] at hpos
  simp only [Complex.ofReal_re] at hpos
  linarith

#print axioms distinct_primes_cpow_real
#print axioms distinct_primes_cpow_positive
#print axioms negative_prime_cpow_excludes_real
end QuantitativeArithmeticPrimePowerTorsion
