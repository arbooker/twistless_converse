module

public import QuantitativeMaassAdmissibleCharacterUniquenessV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNewGap

namespace QuantitativeMaass

def realizedNewCharacter (N : ℕ) (hN : 0<N) [NeZero N] :=
  {χ : admissibleGeneratorIndex N hN→ℂ //
    ∃ x : AutomorphicSpace N,x∈completedNewSignSpace N hN χ ∧ x≠0}

def realizedCharacterSector (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : realizedNewCharacter N hN) : Sector N := by
  classical
  exact ⟨decide (χ.val (frickeGeneratorIndex N hN)=1),
    fun p => decide (-χ.val (simpleAtkinGeneratorIndex N hN p)=1)⟩

theorem realizedCharacterSector_coherent (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : realizedNewCharacter N hN) :
    χ.val (frickeGeneratorIndex N hN)=sign (realizedCharacterSector N hN χ).1 ∧
    ∀ p : SimplePrime N,χ.val (simpleAtkinGeneratorIndex N hN p)=
      -delta (realizedCharacterSector N hN χ) p.val := by
  classical
  obtain ⟨x,hx,hx0⟩ := χ.property
  constructor
  · exact (sign_decide (completedGeneratorSpace_eigenvalue_sign N hN χ.val x hx.2.2 hx0 _)).symm
  · intro p
    have hs := completedGeneratorSpace_eigenvalue_sign N hN χ.val x hx.2.2 hx0
      (simpleAtkinGeneratorIndex N hN p)
    have hn : -χ.val (simpleAtkinGeneratorIndex N hN p)=1 ∨
        -χ.val (simpleAtkinGeneratorIndex N hN p)= -1 := by
      rcases hs with hs|hs <;> rw [hs] <;> norm_num
    have he := congrArg Neg.neg (sign_decide hn)
    simpa only [delta,dite_eq_left p.property,realizedCharacterSector,neg_neg] using he.symm

theorem realizedCharacterSector_injective (N : ℕ) (hN : GridAdmissibleGap.Admissible N) [NeZero N] :
    Function.Injective (realizedCharacterSector N hN.1) := by
  intro χ ψ he
  obtain ⟨x,hx,hx0⟩ := χ.property
  obtain ⟨y,hy,hy0⟩ := ψ.property
  apply Subtype.ext
  apply admissible_new_character_unique N hN χ.val ψ.val x y hx hy hx0 hy0
  · rw [(realizedCharacterSector_coherent N hN.1 χ).1,
      (realizedCharacterSector_coherent N hN.1 ψ).1,he]
  · intro p
    rw [(realizedCharacterSector_coherent N hN.1 χ).2 p,
      (realizedCharacterSector_coherent N hN.1 ψ).2 p,he]

theorem realizedNewCharacter_finite (N : ℕ) (hN : GridAdmissibleGap.Admissible N) [NeZero N] :
    Finite (realizedNewCharacter N hN.1) :=
  Finite.of_injective _ (realizedCharacterSector_injective N hN)

theorem realizedNewCharacter_card_le (N : ℕ) (hN : GridAdmissibleGap.Admissible N) [NeZero N] :
    Nat.card (realizedNewCharacter N hN.1)≤2^((simplePrimes N).card+1) := by
  let := realizedNewCharacter_finite N hN
  classical
  let := Fintype.ofFinite (realizedNewCharacter N hN.1)
  rw [Nat.card_eq_fintype_card,←AsymptoticSectorSigns.card N]
  exact Fintype.card_le_of_injective _ (realizedCharacterSector_injective N hN)

#print axioms realizedCharacterSector_coherent
#print axioms realizedCharacterSector_injective
#print axioms realizedNewCharacter_finite
#print axioms realizedNewCharacter_card_le

end QuantitativeMaass
