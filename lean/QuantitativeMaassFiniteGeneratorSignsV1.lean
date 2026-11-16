module

public import QuantitativeMaassFiniteGeneratorFamilyV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set AsymptoticClassicalPetersson

namespace QuantitativeMaass

def generatorRepresentativeIndex (N : ℕ) (hN : 0<N) (i : admissibleGeneratorIndex N hN) :
    Option (Option (Fin (N+1))) := Classical.choose (finiteGeneratorFamily_covers N hN i)

def finiteGeneratorCharacter (N : ℕ) (hN : 0<N)
    (s : Option (Option (Fin (N+1))) → Bool) (i : admissibleGeneratorIndex N hN) : ℂ :=
  if s (generatorRepresentativeIndex N hN i) then 1 else -1

theorem finiteGeneratorCharacter_norm (N : ℕ) (hN : 0<N)
    (s : Option (Option (Fin (N+1))) → Bool) (i : admissibleGeneratorIndex N hN) :
    ‖finiteGeneratorCharacter N hN s i‖=1 := by
  unfold finiteGeneratorCharacter
  split_ifs <;> simp

/-- A nonzero joint eigenvector determines its entire generator character
from the fixed finite family of actions. -/
theorem generator_character_reduction (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (x : AutomorphicSpace N)
    (hx : x∈completedGeneratorSpace N hN χ) (hx0 : x≠0) (i : admissibleGeneratorIndex N hN) :
    χ i=χ (finiteGeneratorFamily N hN (generatorRepresentativeIndex N hN i)) := by
  have he := congrArg (fun T => T x) (Classical.choose_spec (finiteGeneratorFamily_covers N hN i))
  change quotientNormalizerPullback N (admissibleGeneratorLift N hN i) x=
    quotientNormalizerPullback N (admissibleGeneratorLift N hN
      (finiteGeneratorFamily N hN (generatorRepresentativeIndex N hN i))) x at he
  rw [hx i,hx] at he
  exact smul_left_injective ℂ hx0 he

/-- The possible nonzero simultaneous generator sectors are contained
in an explicitly finite family of sign characters. No diagonalization is assumed. -/
theorem generator_character_finite_encoding (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (x : AutomorphicSpace N)
    (hx : x∈completedGeneratorSpace N hN χ) (hx0 : x≠0) :
    ∃ s : Option (Option (Fin (N+1))) → Bool,χ=finiteGeneratorCharacter N hN s := by
  classical
  let s : Option (Option (Fin (N+1))) → Bool :=
    fun j => decide (χ (finiteGeneratorFamily N hN j)=1)
  refine ⟨s,?_⟩
  funext i
  have he := generator_character_reduction N hN χ x hx hx0 i
  let j := generatorRepresentativeIndex N hN i
  change χ i=(if s j then 1 else -1)
  rw [he]
  change χ (finiteGeneratorFamily N hN j)=(if s j then 1 else -1)
  have hs := completedGeneratorSpace_eigenvalue_sign N hN χ x hx hx0 (finiteGeneratorFamily N hN j)
  rcases hs with hs | hs
  · norm_num [s,hs]
  · norm_num [s,hs]

theorem nonzero_generator_characters_finite (N : ℕ) (hN : 0<N) :
    {χ : admissibleGeneratorIndex N hN → ℂ |
      ∃ x : AutomorphicSpace N,x∈completedGeneratorSpace N hN χ ∧ x≠0}.Finite := by
  apply (Set.finite_range (finiteGeneratorCharacter N hN)).subset
  rintro χ ⟨x,hx,hx0⟩
  obtain ⟨s,hs⟩ := generator_character_finite_encoding N hN χ x hx hx0
  exact ⟨s,hs.symm⟩

#print axioms finiteGeneratorCharacter_norm
#print axioms generator_character_reduction
#print axioms generator_character_finite_encoding
#print axioms nonzero_generator_characters_finite

end QuantitativeMaass
