module

public import QuantitativeMaassFiniteGeneratorSignsV1
public import QuantitativeMaassExactAtkinEndpointsV1
public import QuantitativeMaassCompletedSectorSignsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson

namespace QuantitativeMaass

theorem generator_character_atkin_one (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (x : AutomorphicSpace N)
    (hx : x∈completedGeneratorSpace N hN χ) (hx0 : x≠0)
    (A B : ℤ) (hAB : (1:ℤ)*A+(N:ℤ)*B=1)
    (i : admissibleGeneratorIndex N hN) (hi : i.val=exactAtkinLabel N 1 (by decide) A B hAB) :
    χ i=1 := by
  have hg : (admissibleGeneratorLift N hN i).val∈AsymptoticCongruenceStrip.gamma N := by
    change i.val∈_
    rw [hi]
    exact exactAtkin_one_mem N A B hAB
  have he := quotientNormalizerPullback_gamma N (admissibleGeneratorLift N hN i) hg x
  rw [hx i] at he
  exact smul_left_injective ℂ hx0 (he.trans (one_smul ℂ x).symm)

theorem generator_character_atkin_full (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (x : AutomorphicSpace N)
    (hx : x∈completedGeneratorSpace N hN χ) (hx0 : x≠0)
    (A B : ℤ) (hAB : (N:ℤ)*A+(1:ℤ)*B=1)
    (i : admissibleGeneratorIndex N hN) (hi : i.val=exactAtkinLabel 1 N hN A B hAB) :
    χ i=χ (frickeGeneratorIndex N hN) := by
  obtain ⟨a,ha⟩ := exactAtkin_full_fricke N hN A B hAB
  have he := quotientNormalizerPullback_left_gamma N (admissibleGeneratorLift N hN i)
    (admissibleGeneratorLift N hN (frickeGeneratorIndex N hN)) a (by
      change i.val=a.val*AsymptoticFreshMatrices.frickeLabel N hN
      rw [hi]
      exact ha) x
  rw [hx i,hx] at he
  exact smul_left_injective ℂ hx0 he

/-- Exact multiplicativity of the signs at disjoint exact divisors,
derived from their actual completed quotient actions. -/
theorem generator_character_atkin_product (D P Q : ℕ) (hP : 0<P) (hQ : 0<Q)
    (hN : 0<(P*Q)*D) (χ : admissibleGeneratorIndex ((P*Q)*D) hN → ℂ)
    (x : AutomorphicSpace ((P*Q)*D))
    (hx : x∈completedGeneratorSpace ((P*Q)*D) hN χ) (hx0 : x≠0)
    (A B C E U V : ℤ)
    (hAB : (P:ℤ)*A+((Q*D:ℕ):ℤ)*B=1)
    (hCE : (Q:ℤ)*C+((P*D:ℕ):ℤ)*E=1)
    (hUV : ((P*Q:ℕ):ℤ)*U+(D:ℤ)*V=1)
    (i j k : admissibleGeneratorIndex ((P*Q)*D) hN)
    (hi : i.val=exactAtkinLabel (Q*D) P hP A B hAB)
    (hj : j.val=exactAtkinLabel (P*D) Q hQ C E hCE)
    (hk : k.val=exactAtkinLabel D (P*Q) (Nat.mul_pos hP hQ) U V hUV) :
    χ i*χ j=χ k := by
  obtain ⟨a,ha⟩ := exactAtkin_product_mod_gamma D P Q hP hQ A B C E U V hAB hCE hUV
  have he := quotientNormalizerPullback_left_gamma ((P*Q)*D)
    (admissibleGeneratorLift _ hN i*admissibleGeneratorLift _ hN j)
    (admissibleGeneratorLift _ hN k) a (by
      change i.val*j.val=a.val*k.val
      rw [hi,hj,hk]
      exact ha) x
  rw [quotientNormalizerPullback_mul,hx i,map_smul,hx j,hx k,smul_smul] at he
  exact smul_left_injective ℂ hx0 he

#print axioms generator_character_atkin_one
#print axioms generator_character_atkin_full
#print axioms generator_character_atkin_product

end QuantitativeMaass
