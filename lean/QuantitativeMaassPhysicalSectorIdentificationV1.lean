module

public import QuantitativeMaassSectorCharacterExtensionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNewGap QuantitativeNinaMaass
namespace QuantitativeMaass

/-- A full generator character on a nonzero vector in a physical sector
has exactly the original finite signs of that sector. -/
theorem countingSector_character_coherent (N : ℕ) [NeZero N] (hN : 0<N)
    (e : Sector N) (χ : admissibleGeneratorIndex N hN → ℂ)
    (x : AutomorphicSpace N) (hx : x∈completedCountingSectorSpace N hN e)
    (hχ : x∈completedNewSignSpace N hN χ) (hx0 : x≠0) :
    χ (frickeGeneratorIndex N hN)=sign e.1 ∧
      ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val := by
  have hs := (completedCountingSectorSpace_mem N hN e x).mp hx
  constructor
  · have ha := hχ.2.2 (frickeGeneratorIndex N hN)
    change frickeIsometry N hN x=χ (frickeGeneratorIndex N hN) • x at ha
    have hb := hs.2 none
    change frickeIsometry N hN x=(signReal e.1:ℂ) • x at hb
    rw [signReal_coe] at hb
    exact smul_left_injective ℂ hx0 (ha.symm.trans hb)
  · intro p
    have ha := hχ.2.2 (simpleAtkinGeneratorIndex N hN p)
    have hi : admissibleGeneratorLift N hN (simpleAtkinGeneratorIndex N hN p)=
        completedLocalAtkinNormalizer N hN p := Subtype.ext (simpleAtkinGeneratorIndex_value N hN p)
    rw [hi] at ha
    have hb := hs.2 (some p)
    change quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p) x=
      ((-signReal (e.2 p):ℝ):ℂ) • x at hb
    have hb' : quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p) x=
        -delta e p.val • x := by
      simpa only [Complex.ofReal_neg,signReal_coe,delta,dite_eq_left p.property] using hb
    exact smul_left_injective ℂ hx0 (ha.symm.trans hb')

theorem sectorCharacter_of_realized (N : ℕ) [NeZero N] (hN : GridAdmissibleGap.Admissible N)
    (χ : realizedNewCharacter N hN.1) :
    sectorCharacter N hN.1 (realizedCharacterSector N hN.1 χ)=χ.val := by
  classical
  have hex : ∃ ψ : realizedNewCharacter N hN.1,
      realizedCharacterSector N hN.1 ψ=realizedCharacterSector N hN.1 χ := ⟨χ,rfl⟩
  rw [sectorCharacter,dite_eq_left hex]
  exact congrArg Subtype.val ((realizedCharacterSector_injective N hN) (Classical.choose_spec hex))

/-- At an admissible level the original finite sign sector is exactly
the canonical all-generator sector. No character-extension premise remains. -/
theorem completedCountingSectorSpace_eq_newSign (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) (e : Sector N) :
    completedCountingSectorSpace N hN.1 e=completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e) := by
  apply le_antisymm
  · intro x hx
    by_cases hx0 : x=0
    · rw [hx0]
      exact Submodule.zero_mem _
    obtain ⟨χ,_hunit,hχ⟩ := countingSector_character_extension N hN e x hx
    let r : realizedNewCharacter N hN.1 := ⟨χ,x,hχ,hx0⟩
    obtain ⟨hW,hS⟩ := countingSector_character_coherent N hN.1 e χ x hx hχ hx0
    have hr := realizedCharacterSector_coherent N hN.1 r
    have he : realizedCharacterSector N hN.1 r=e :=
      coherent_character_sector_unique N hN.1 χ _ e hr.1 hW hr.2 hS
    have hc := sectorCharacter_of_realized N hN r
    rw [he] at hc
    simpa only [hc] using hχ
  · exact completedNewSign_le_countingSector N hN.1 e

/-- The canonical sector projection has the actual finite sign product,
with no additional generator equations left as assumptions. -/
theorem completedNewSign_sector_projection (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) (e : Sector N) :
    (completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e)).starProjection=
      (completedCuspidalNewSpace N hN.1).starProjection.comp
        (((Finset.univ : Finset (SectorSignIndex N)).toList.map fun i =>
          (completedSectorSignConstraint N hN.1 e i).starProjection).prod) := by
  have hs := completedCountingSectorSpace_eq_newSign N hN e
  calc
    _ = (completedCountingSectorSpace N hN.1 e).starProjection :=
      AsymptoticPolarIsometry.starProjection_congr _ _ hs.symm
    _ = _ := completedCountingSectorSpace_projection N hN.1 e


#print axioms countingSector_character_coherent
#print axioms sectorCharacter_of_realized
#print axioms completedCountingSectorSpace_eq_newSign
#print axioms completedNewSign_sector_projection
end QuantitativeMaass
