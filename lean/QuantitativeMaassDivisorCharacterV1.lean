module

public import QuantitativeMaassExactDivisorArithmeticV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson

namespace QuantitativeMaass

theorem exact_divisor_bezout (Q D : ℕ) (h : Nat.Coprime Q D) :
    (Q:ℤ)*Nat.gcdA Q D+(D:ℤ)*Nat.gcdB Q D=1 := by
  have hh := Nat.gcd_eq_gcd_ab Q D
  rw [h.gcd_eq_one,Nat.cast_one] at hh
  exact hh.symm

def exactDivisorGeneratorIndex (N : ℕ) (hN : 0<N) (Q D : ℕ)
    (hQ : 0<Q) (hcop : Nat.Coprime Q D) (hQD : Q*D=N) :
    admissibleGeneratorIndex N hN :=
  ⟨exactAtkinLabel D Q hQ (Nat.gcdA Q D) (Nat.gcdB Q D) (exact_divisor_bezout Q D hcop),
    admissibleNormalizerGenerator.atkin D Q hQ (Nat.gcdA Q D) (Nat.gcdB Q D)
      (exact_divisor_bezout Q D hcop) hQD⟩

def divisorCharacter (N : ℕ) (hN : 0<N) (χ : admissibleGeneratorIndex N hN → ℂ)
    (Q : ℕ) : ℂ := by
  classical
  exact if h : ∃ i,generatorAtDivisor N hN Q i then χ (Classical.choose h) else 1

theorem divisorCharacter_eq (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (x : AutomorphicSpace N)
    (hx : x∈completedGeneratorSpace N hN χ) (hx0 : x≠0)
    (Q : ℕ) (i : admissibleGeneratorIndex N hN) (hi : generatorAtDivisor N hN Q i) :
    divisorCharacter N hN χ Q=χ i := by
  have hex : ∃ j,generatorAtDivisor N hN Q j := ⟨i,hi⟩
  rw [divisorCharacter,dite_eq_left hex]
  have he := DFunLike.congr_fun (generatorAtDivisor_action_eq N hN Q
    (Classical.choose hex) i (Classical.choose_spec hex) hi) x
  rw [hx,hx] at he
  exact smul_left_injective ℂ hx0 he

theorem divisorCharacter_one (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (x : AutomorphicSpace N)
    (hx : x∈completedGeneratorSpace N hN χ) (hx0 : x≠0) :
    divisorCharacter N hN χ 1=1 := by
  let i := exactDivisorGeneratorIndex N hN 1 N (by decide) (Nat.coprime_one_left N) (one_mul N)
  rw [divisorCharacter_eq N hN χ x hx hx0 1 i
    ⟨N,by decide,_,_,_,one_mul N,rfl⟩]
  exact generator_character_atkin_one N hN χ x hx hx0 _ _ _ i rfl

theorem divisorCharacter_full (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (x : AutomorphicSpace N)
    (hx : x∈completedGeneratorSpace N hN χ) (hx0 : x≠0) :
    divisorCharacter N hN χ N=χ (frickeGeneratorIndex N hN) := by
  let i := exactDivisorGeneratorIndex N hN N 1 hN (Nat.coprime_one_right N) (mul_one N)
  rw [divisorCharacter_eq N hN χ x hx hx0 N i
    ⟨1,hN,_,_,_,mul_one N,rfl⟩]
  exact generator_character_atkin_full N hN χ x hx hx0 _ _ _ i rfl

/-- Multiplicativity uses the actual congruence-coset product identity. -/
theorem divisorCharacter_mul (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (x : AutomorphicSpace N)
    (hx : x∈completedGeneratorSpace N hN χ) (hx0 : x≠0)
    (P Q D : ℕ) (hP : 0<P) (hQ : 0<Q) (hPQ : Nat.Coprime P Q)
    (hcop : Nat.Coprime (P*Q) D) (hND : (P*Q)*D=N) :
    divisorCharacter N hN χ P*divisorCharacter N hN χ Q=divisorCharacter N hN χ (P*Q) := by
  subst N
  have hp := hPQ.mul_right (hcop.of_dvd_left (dvd_mul_right P Q))
  have hq := hPQ.symm.mul_right (hcop.of_dvd_left (dvd_mul_left Q P))
  let i := exactDivisorGeneratorIndex _ hN P (Q*D) hP hp (by ring)
  let j := exactDivisorGeneratorIndex _ hN Q (P*D) hQ hq (by ring)
  let k := exactDivisorGeneratorIndex _ hN (P*Q) D (Nat.mul_pos hP hQ) hcop rfl
  rw [divisorCharacter_eq _ hN χ x hx hx0 P i ⟨Q*D,hP,_,_,_,by ring,rfl⟩,
    divisorCharacter_eq _ hN χ x hx hx0 Q j ⟨P*D,hQ,_,_,_,by ring,rfl⟩,
    divisorCharacter_eq _ hN χ x hx hx0 (P*Q) k ⟨D,Nat.mul_pos hP hQ,_,_,_,rfl,rfl⟩]
  exact generator_character_atkin_product D P Q hP hQ hN χ x hx hx0
    _ _ _ _ _ _ _ _ _ i j k rfl rfl rfl

#print axioms exact_divisor_bezout
#print axioms divisorCharacter_eq
#print axioms divisorCharacter_one
#print axioms divisorCharacter_full
#print axioms divisorCharacter_mul

end QuantitativeMaass
