module

public import AsymptoticNewSpaceCompressionV1
public import AsymptoticLocalOldGroupsV1
public import AsymptoticPrimeNewCornerV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticQuotientOperators

open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticLocalCongruence
open AsymptoticNestedQuotients AsymptoticSectorSigns
open scoped lp

/-- The actual pair of old groups gives a prime-supported exact new
projection, including at repeated primes. -/
theorem prime_new_supported (M p : ℕ) (hM : 0<M) (hp : p.Prime) :
    letI : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
    Supported (gamma_le_projectiveOutside (p*M) (Nat.mul_pos hp.pos hM) {p})
      (newSpace (gamma_le_of_dvd (Nat.dvd_mul_left M p))
        (gamma_le_frickeOldGroup (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p))).starProjection := by
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
  apply newSpace_supported
  · exact gamma_lower_le_projectiveOutside M p hM hp
  · rw [frickeOldGroup_eq_degeneracy M p hM hp.pos]
    exact degeneracy_le_projectiveOutside M p hM hp

/-- Every actual incidence sector pulls back into the same fixed local
new corner. The corner is independent of the sector and the strip point. -/
theorem incidence_induction_mem_prime_new (M p : ℕ) (hM : 0<M) (hp : p.Prime)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (e : Sector (p*M)) (x : ℍ)
    (f : ℓ²(Classes (gamma (p*M)),ℂ))
    (hf : AsymptoticCongruenceQuotient.induction (p*M) hε ht x f∈
      AsymptoticQuotientIncidence.space (p*M) (Nat.mul_pos hp.pos hM) hε ht e x) :
    letI : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
    f∈newSpace (gamma_le_of_dvd (Nat.dvd_mul_left M p))
      (gamma_le_frickeOldGroup (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p)) := by
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
  exact (AsymptoticCongruenceOldSpace.newSpace_induction_iff (p*M) _ _ _ _ hε ht x f).mp
    (AsymptoticCongruenceOldSpace.prime_incidence_le_newSpace M p hM hp hε ht e x hf)

#print axioms prime_new_supported
#print axioms incidence_induction_mem_prime_new

end AsymptoticQuotientOperators
