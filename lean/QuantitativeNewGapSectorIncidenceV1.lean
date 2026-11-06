module

public import QuantitativeNewGapSectorSpaceV1
public import QuantitativeNewGapRamifiedIdentificationV1
public import AsymptoticCosetSectorOrthogonalityV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticNestedQuotients AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open AsymptoticSectorSigns AsymptoticAtkinLehner AsymptoticOrbitDecode AsymptoticFreshMatrices
open AsymptoticQuotientOperators UpperHalfPlane
open scoped lp

theorem countingSector_fricke (N : ℕ) (hN : 0<N) (e : Sector N)
    (f : ℓ²(Classes (gamma N),ℂ)) (hf : f∈countingSectorSpace N hN e)
    (g : AsymptoticRationalGroup.Group) :
    sign e.1*f (classOf (gamma N) (frickeLabel N hN*g))=f (classOf (gamma N) g) := by
  have hh := congrArg (fun v : ℓ²(Classes (gamma N),ℂ) => v (classOf (gamma N) g))
    (((countingSectorSpace_mem N hN e f).mp hf).2 none)
  change f (classOf (gamma N) (frickeLabel N hN*g))=(signReal e.1:ℂ)*f (classOf (gamma N) g) at hh
  rw [signReal_coe] at hh
  rw [hh,← mul_assoc,← pow_two,sign_sq,one_mul]

theorem countingSector_simple_local (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hpM : ¬p∣M)
    (e : Sector (p*M)) (f : ℓ²(Classes (gamma (p*M)),ℂ))
    (hf : f∈countingSectorSpace (p*M) (Nat.mul_pos hp.pos hM) e)
    (hAB : (p:ℤ)*Nat.gcdA p M+(M:ℤ)*Nat.gcdB p M=1)
    (g : AsymptoticRationalGroup.Group) :
    f (classOf (gamma (p*M)) (localAtkin M p hM hp.pos (Nat.gcdA p M) (Nat.gcdB p M) hAB*g))=
      -delta e p*f (classOf (gamma (p*M)) g) := by
  classical
  have hs : ¬p^2∣p*M := by
    rw [pow_two,Nat.mul_dvd_mul_iff_left hp.pos]
    exact hpM
  have hps : p∈simplePrimes (p*M) := mem_simplePrimes.mpr ⟨hp,Nat.dvd_mul_right p M,hs⟩
  let q : SimplePrime (p*M) := ⟨p,hps⟩
  have hh := congrArg (fun v : ℓ²(Classes (gamma (p*M)),ℂ) => v (classOf (gamma (p*M)) g))
    (((countingSectorSpace_mem _ _ e f).mp hf).2 (some q))
  change f (classOf (gamma (p*M)) (localAtkinLabel (p*M) (Nat.mul_pos hp.pos hM) q*g))=
    ((-signReal (e.2 q):ℝ):ℂ)*f (classOf (gamma (p*M)) g) at hh
  simpa only [localAtkinLabel,q,Nat.mul_div_cancel_left M hp.pos,Complex.ofReal_neg,
    signReal_coe,delta,dite_eq_left hps] using hh

/-- The finite new/sign intersection satisfies every original weighted
Fricke and ramified incidence equation, including repeated primes. -/
theorem countingSector_induction_mem_incidence (N : ℕ) (hN : 0<N) (e : Sector N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (f : ℓ²(Classes (gamma N),ℂ)) (hf : f∈countingSectorSpace N hN e) :
    AsymptoticCongruenceQuotient.induction N hε ht z f∈
      AsymptoticQuotientIncidence.space N hN hε ht e z := by
  apply (AsymptoticQuotientIncidence.induction_mem_space N hN hε ht e z f).mpr
  refine ⟨countingSector_fricke N hN e f hf,?_⟩
  rintro ⟨p,hp,hpN⟩ g
  obtain ⟨M,rfl⟩ := hpN
  have hM : 0<M := by nlinarith
  let : NeZero (p*M) := ⟨hN.ne'⟩
  let : Fact p.Prime := ⟨hp⟩
  have hn := AsymptoticTotalNewCorner.space_le_local (p*M) hN p
    (((countingSectorSpace_mem _ _ e f).mp hf).1)
  rw [AsymptoticTotalNewCorner.localSpace_mul_eq M p hM hp] at hn
  have hz := (newSpace_mem _ _ f).mp hn
  by_cases hpM : p∣M
  · have hs : p^2∣p*M := by rw [pow_two]; exact Nat.mul_dvd_mul_left p hpM
    simp only [AsymptoticCylinderRamified.eigenvalue,ite_eq_left hs,zero_mul]
    exact fricke_zero_ramified_zero M p hM hp.pos hpM f hz.2 g
  · have hs : ¬p^2∣p*M := by rw [pow_two,Nat.mul_dvd_mul_iff_left hp.pos]; exact hpM
    have hAB : (p:ℤ)*Nat.gcdA p M+(M:ℤ)*Nat.gcdB p M=1 := by
      have hh := Nat.gcd_eq_gcd_ab p M
      rw [(hp.coprime_iff_not_dvd.mpr hpM).gcd_eq_one,Nat.cast_one] at hh
      exact hh.symm
    have hW := countingSector_simple_local M p hM hp hpM e f hf hAB
    have he := lower_zero_local_sign_ramified M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M)
      hAB f (-delta e p) (by simpa only [neg_sq] using delta_sq e p) hz.1 hW g
    simpa only [AsymptoticCylinderRamified.eigenvalue,ite_eq_right hs,neg_neg,
      AsymptoticCongruenceQuotient.classOf,AsymptoticNestedQuotients.classOf] using he

#print axioms countingSector_fricke
#print axioms countingSector_simple_local
#print axioms countingSector_induction_mem_incidence

/-- Conversely, the original incidence equations imply every canonical
local sign and all new constraints. -/
theorem incidence_induction_mem_countingSector (N : ℕ) (hN : 0<N) (e : Sector N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (f : ℓ²(Classes (gamma N),ℂ))
    (hf : AsymptoticCongruenceQuotient.induction N hε ht z f∈
      AsymptoticQuotientIncidence.space N hN hε ht e z) :
    f∈countingSectorSpace N hN e := by
  apply (countingSectorSpace_mem N hN e f).mpr
  refine ⟨AsymptoticTotalNewCorner.incidence_induction_mem N hN hε ht e z f hf,?_⟩
  have hi := (AsymptoticQuotientIncidence.induction_mem_space N hN hε ht e z f).mp hf
  intro i
  cases i with
  | none =>
    apply lp.ext
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      change f (classOf (gamma N) (frickeLabel N hN*g))=(signReal e.1:ℂ)*f (classOf (gamma N) g)
      rw [signReal_coe]
      exact sign_reverse e.1 (hi.1 g)
  | some p =>
    let : Fact p.val.Prime := ⟨simplePrime_prime p⟩
    have hpM : ¬p.val∣N/p.val :=
      (simplePrime_prime p).coprime_iff_not_dvd.mp (simplePrime_coprime N p)
    have hF : ∀ a : gamma (p.val*(N/p.val)),∀ g,
        f (classOf (gamma N) (a.val*g))=f (classOf (gamma N) g) := by
      intro a g
      have ha : a.val∈gamma N := by
        simpa only [Nat.mul_div_cancel' (simplePrime_dvd p)] using a.property
      exact congrArg f (classOf_mul (gamma N) ⟨a.val,ha⟩ g)
    have hW : ∀ g,sign e.1*f (classOf (gamma N)
        (frickeLabel (p.val*(N/p.val))
          (Nat.mul_pos (simplePrime_prime p).pos (simplePrime_colevel_pos N hN p))*g))=
        f (classOf (gamma N) g) := by
      intro g
      simpa only [Nat.mul_div_cancel' (simplePrime_dvd p),AsymptoticCongruenceQuotient.classOf,
        AsymptoticNestedQuotients.classOf] using hi.1 g
    have hU : ∀ g,∑ a : Fin p.val,f (classOf (gamma N)
        (ramifiedLabel p.val (simplePrime_prime p).pos a*g))=delta e p.val*f (classOf (gamma N) g) := by
      intro g
      have hh := hi.2 ⟨p.val,simplePrime_prime p,simplePrime_dvd p⟩ g
      simpa only [AsymptoticCylinderRamified.eigenvalue,
        ite_eq_right (mem_simplePrimes.mp p.property).2.2,AsymptoticCongruenceQuotient.classOf,
        AsymptoticNestedQuotients.classOf] using hh
    apply lp.ext
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      change f (classOf (gamma N) (localAtkinLabel N hN p*g))=
        ((-signReal (e.2 p):ℝ):ℂ)*f (classOf (gamma N) g)
      have hh := local_eigen (N/p.val) p.val (simplePrime_colevel_pos N hN p) hpM
        (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p)
        (fun g => f (classOf (gamma N) g)) hF (sign e.1) (delta e p.val) (delta_sq e p.val) hW hU g
      simpa only [localAtkinLabel,Complex.ofReal_neg,signReal_coe,delta,dite_eq_left p.property] using hh

theorem countingSector_induction_iff_incidence (N : ℕ) (hN : 0<N) (e : Sector N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (f : ℓ²(Classes (gamma N),ℂ)) :
    f∈countingSectorSpace N hN e ↔ AsymptoticCongruenceQuotient.induction N hε ht z f∈
      AsymptoticQuotientIncidence.space N hN hε ht e z :=
  ⟨countingSector_induction_mem_incidence N hN e hε ht z f,
    incidence_induction_mem_countingSector N hN e hε ht z f⟩

#print axioms countingSector_induction_iff_incidence

end QuantitativeNewGap
