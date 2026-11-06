module

public import QuantitativeNewGapNormalizerV1
public import QuantitativeArithmeticAtkinSignsCompleteV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticSectorSigns AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open AsymptoticAtkinLehner AsymptoticNestedQuotients QuantitativeArithmeticAtkinSigns
open scoped lp

abbrev SimplePrime (N : ℕ) := {p : ℕ // p∈simplePrimes N}

theorem simplePrime_prime {N : ℕ} (p : SimplePrime N) : p.val.Prime :=
  (mem_simplePrimes.mp p.property).1

theorem simplePrime_dvd {N : ℕ} (p : SimplePrime N) : p.val∣N :=
  (mem_simplePrimes.mp p.property).2.1

theorem simplePrime_colevel_pos (N : ℕ) (hN : 0<N) (p : SimplePrime N) : 0<N/p.val :=
  Nat.div_pos (Nat.le_of_dvd hN (simplePrime_dvd p)) (simplePrime_prime p).pos

theorem simplePrime_coprime (N : ℕ) (p : SimplePrime N) : p.val.Coprime (N/p.val) := by
  apply (simplePrime_prime p).coprime_iff_not_dvd.mpr
  intro hd
  have hh := Nat.mul_dvd_mul_left p.val hd
  rw [Nat.mul_div_cancel' (simplePrime_dvd p),← pow_two] at hh
  exact (mem_simplePrimes.mp p.property).2.2 hh

theorem simplePrime_bezout (N : ℕ) (p : SimplePrime N) :
    (p.val:ℤ)*Nat.gcdA p.val (N/p.val)+((N/p.val:ℕ):ℤ)*Nat.gcdB p.val (N/p.val)=1 := by
  have hh := Nat.gcd_eq_gcd_ab p.val (N/p.val)
  rw [(simplePrime_coprime N p).gcd_eq_one,Nat.cast_one] at hh
  exact hh.symm

def localAtkinLabel (N : ℕ) (hN : 0<N) (p : SimplePrime N) : AsymptoticRationalGroup.Group :=
  localAtkin (N/p.val) p.val (simplePrime_colevel_pos N hN p) (simplePrime_prime p).pos
    (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p)

theorem localAtkinLabel_conj (N : ℕ) (hN : 0<N) (p : SimplePrime N)
    (g : AsymptoticRationalGroup.Group) (hg : g∈gamma N) :
    localAtkinLabel N hN p*g*(localAtkinLabel N hN p)⁻¹∈gamma N := by
  have hg' : g∈gamma (p.val*(N/p.val)) := by
    simpa only [Nat.mul_div_cancel' (simplePrime_dvd p)] using hg
  simpa only [localAtkinLabel,Nat.mul_div_cancel' (simplePrime_dvd p)] using
    local_conj_mem (N/p.val) p.val (simplePrime_colevel_pos N hN p) (simplePrime_prime p).pos
      (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p) hg'

theorem localAtkinLabel_inv_conj (N : ℕ) (hN : 0<N) (p : SimplePrime N)
    (g : AsymptoticRationalGroup.Group) (hg : g∈gamma N) :
    (localAtkinLabel N hN p)⁻¹*g*localAtkinLabel N hN p∈gamma N := by
  have hg' : g∈gamma (p.val*(N/p.val)) := by
    simpa only [Nat.mul_div_cancel' (simplePrime_dvd p)] using hg
  simpa only [localAtkinLabel,Nat.mul_div_cancel' (simplePrime_dvd p)] using
    local_inv_conj_mem (N/p.val) p.val (simplePrime_colevel_pos N hN p) (simplePrime_prime p).pos
      (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p) hg'

theorem localAtkinLabel_square (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    localAtkinLabel N hN p*localAtkinLabel N hN p∈gamma N := by
  simpa only [localAtkinLabel,Nat.mul_div_cancel' (simplePrime_dvd p)] using
    localAtkin_square_mem (N/p.val) p.val (simplePrime_colevel_pos N hN p) (simplePrime_prime p).pos
      (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p)

def localAtkinEquiv (N : ℕ) (hN : 0<N) (p : SimplePrime N) : Classes (gamma N) ≃ Classes (gamma N) :=
  leftMulEquiv (gamma N) (localAtkinLabel N hN p)
    (localAtkinLabel_conj N hN p) (localAtkinLabel_inv_conj N hN p)

theorem localAtkinEquiv_involutive (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    Function.Involutive (localAtkinEquiv N hN p) :=
  normalizerEquiv_involutive _ _ _ _ (localAtkinLabel_square N hN p)

theorem localAtkin_globalFricke_commute (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    Function.Commute (localAtkinEquiv N hN p) (globalFrickeEquiv N hN) := by
  apply normalizerEquivs_commute
  exact localAtkin_fricke_commutator_mem_level N p.val hN (simplePrime_prime p)
    (simplePrime_dvd p) (simplePrime_colevel_pos N hN p)
    (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p)

theorem localAtkinEquivs_commute (N : ℕ) (hN : 0<N) (p q : SimplePrime N) :
    Function.Commute (localAtkinEquiv N hN p) (localAtkinEquiv N hN q) := by
  by_cases hpq : p=q
  · subst q
    intro x
    rfl
  apply normalizerEquivs_commute
  have hpq' : p.val≠q.val := fun hh => hpq (Subtype.ext hh)
  exact localAtkin_pair_commutator_mem_level N p.val q.val hN
    (simplePrime_prime p) (simplePrime_prime q) (simplePrime_dvd p) (simplePrime_dvd q) hpq'
    (simplePrime_colevel_pos N hN p) (simplePrime_colevel_pos N hN q)
    (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val))
    (Nat.gcdA q.val (N/q.val)) (Nat.gcdB q.val (N/q.val))
    (simplePrime_bezout N p) (simplePrime_bezout N q)

#print axioms localAtkinLabel_square
#print axioms localAtkin_globalFricke_commute
#print axioms localAtkinEquivs_commute

end QuantitativeNewGap
