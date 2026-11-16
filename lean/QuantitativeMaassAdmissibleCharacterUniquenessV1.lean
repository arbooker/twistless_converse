module

public import QuantitativeMaassDivisorCharacterV1
public import QuantitativeMaassExactCharacterArithmeticV1
public import QuantitativeMaassCompletedHalfSignV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNewGap

namespace QuantitativeMaass

theorem divisorCharacter_simple (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (x : AutomorphicSpace N)
    (hx : x∈completedGeneratorSpace N hN χ) (hx0 : x≠0) (p : SimplePrime N) :
    divisorCharacter N hN χ p.val=χ (simpleAtkinGeneratorIndex N hN p) := by
  apply divisorCharacter_eq N hN χ x hx hx0
  exact ⟨N/p.val,(simplePrime_prime p).pos,_,_,simplePrime_bezout N p,
    Nat.mul_div_cancel' (simplePrime_dvd p),rfl⟩

theorem divisorCharacter_ne_zero (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (x : AutomorphicSpace N)
    (hx : x∈completedGeneratorSpace N hN χ) (hx0 : x≠0)
    (Q D : ℕ) (hQD : Q*D=N) (hcop : Nat.Coprime Q D) :
    divisorCharacter N hN χ Q≠0 := by
  have hQ : 0<Q := by nlinarith
  let i := exactDivisorGeneratorIndex N hN Q D hQ hcop hQD
  rw [divisorCharacter_eq N hN χ x hx hx0 Q i ⟨D,hQ,_,_,_,hQD,rfl⟩]
  rcases completedGeneratorSpace_eigenvalue_sign N hN χ x hx hx0 i with h|h <;> rw [h] <;> norm_num

/-- On a nonzero completed new/sign sector at an admissible level,
Fricke and simple-prime signs determine the entire generator character. -/
theorem admissible_new_character_unique (N : ℕ) (hN : GridAdmissibleGap.Admissible N) [NeZero N]
    (χ ψ : admissibleGeneratorIndex N hN.1 → ℂ) (x y : AutomorphicSpace N)
    (hx : x∈completedNewSignSpace N hN.1 χ) (hy : y∈completedNewSignSpace N hN.1 ψ)
    (hx0 : x≠0) (hy0 : y≠0)
    (hW : χ (frickeGeneratorIndex N hN.1)=ψ (frickeGeneratorIndex N hN.1))
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN.1 p)=
      ψ (simpleAtkinGeneratorIndex N hN.1 p)) : χ=ψ := by
  have hdiv : ∀ Q D : ℕ,Q*D=N→Nat.Coprime Q D→
      divisorCharacter N hN.1 χ Q=divisorCharacter N hN.1 ψ Q := by
    apply admissible_exact_character_eq N hN
    · rw [divisorCharacter_one N hN.1 χ x hx.2.2 hx0,
        divisorCharacter_one N hN.1 ψ y hy.2.2 hy0]
    · rw [divisorCharacter_full N hN.1 χ x hx.2.2 hx0,
        divisorCharacter_full N hN.1 ψ y hy.2.2 hy0,hW]
    · exact divisorCharacter_mul N hN.1 χ x hx.2.2 hx0
    · exact divisorCharacter_mul N hN.1 ψ y hy.2.2 hy0
    · intro p hp
      rw [divisorCharacter_simple N hN.1 χ x hx.2.2 hx0 ⟨p,hp⟩,
        divisorCharacter_simple N hN.1 ψ y hy.2.2 hy0 ⟨p,hp⟩,hS]
    · exact divisorCharacter_ne_zero N hN.1 χ x hx.2.2 hx0
  funext i
  obtain ⟨g,hg⟩ := i
  cases hg with
  | fricke => exact hW
  | half h4 =>
    exact (completedNewSign_half_character N hN.1 h4 χ x hx hx0).trans
      (completedNewSign_half_character N hN.1 h4 ψ y hy hy0).symm
  | atkin D Q hQ A B hAB hQD =>
    let i : admissibleGeneratorIndex N hN.1 :=
      ⟨exactAtkinLabel D Q hQ A B hAB,admissibleNormalizerGenerator.atkin D Q hQ A B hAB hQD⟩
    have hi : generatorAtDivisor N hN.1 Q i := ⟨D,hQ,A,B,hAB,hQD,rfl⟩
    have hc : Nat.Coprime Q D := Nat.isCoprime_iff_coprime.mp ⟨A,B,by nlinarith [hAB]⟩
    change χ i=ψ i
    rw [←divisorCharacter_eq N hN.1 χ x hx.2.2 hx0 Q i hi,
      ←divisorCharacter_eq N hN.1 ψ y hy.2.2 hy0 Q i hi]
    exact hdiv Q D hQD hc

#print axioms divisorCharacter_simple
#print axioms divisorCharacter_ne_zero
#print axioms admissible_new_character_unique

end QuantitativeMaass
