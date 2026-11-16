module

public import QuantitativeMaassAtkinLabelSeparationV1
public import QuantitativeMaassRealizedCharacterSectorsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNewGap

namespace QuantitativeMaass

/-- A unit-modulus extension exists even for an empty canonical sector. -/
def basicSectorCharacter (N : ℕ) (hN : 0<N) (e : Sector N)
    (i : admissibleGeneratorIndex N hN) : ℂ := by
  classical
  exact if i=frickeGeneratorIndex N hN then sign e.1 else
    if h : ∃ p : SimplePrime N,simpleAtkinGeneratorIndex N hN p=i then
      -delta e (Classical.choose h).val else 1

theorem basicSectorCharacter_norm (N : ℕ) (hN : 0<N) (e : Sector N)
    (i : admissibleGeneratorIndex N hN) : ‖basicSectorCharacter N hN e i‖=1 := by
  classical
  unfold basicSectorCharacter
  split_ifs <;> simp only [sign_norm,norm_neg,delta_norm,norm_one]

theorem basicSectorCharacter_coherent (N : ℕ) (hN : 0<N) (e : Sector N) :
    basicSectorCharacter N hN e (frickeGeneratorIndex N hN)=sign e.1 ∧
    ∀ p : SimplePrime N,basicSectorCharacter N hN e (simpleAtkinGeneratorIndex N hN p)= -delta e p.val := by
  classical
  constructor
  · simp only [basicSectorCharacter,ite_eq_left]
  · intro p
    have hex : ∃ q : SimplePrime N,simpleAtkinGeneratorIndex N hN q=simpleAtkinGeneratorIndex N hN p := ⟨p,rfl⟩
    rw [basicSectorCharacter,ite_eq_right (simpleAtkinGeneratorIndex_ne_fricke N hN p),dite_eq_left hex]
    rw [simpleAtkinGeneratorIndex_injective N hN (Classical.choose_spec hex)]

/-- Prefer the realized canonical character whenever this original sector
occurs; otherwise retain a coherent unit character with an empty target. -/
def sectorCharacter (N : ℕ) (hN : 0<N) [NeZero N] (e : Sector N) :
    admissibleGeneratorIndex N hN→ℂ := by
  classical
  exact if h : ∃ χ : realizedNewCharacter N hN,realizedCharacterSector N hN χ=e then
    (Classical.choose h).val else basicSectorCharacter N hN e

theorem sectorCharacter_norm (N : ℕ) (hN : 0<N) [NeZero N] (e : Sector N)
    (i : admissibleGeneratorIndex N hN) : ‖sectorCharacter N hN e i‖=1 := by
  classical
  unfold sectorCharacter
  split_ifs with h
  · obtain ⟨x,hx,hx0⟩ := (Classical.choose h).property
    rcases completedGeneratorSpace_eigenvalue_sign N hN (Classical.choose h).val x hx.2.2 hx0 i with he|he <;>
      rw [he] <;> norm_num
  · exact basicSectorCharacter_norm N hN e i

theorem sectorCharacter_coherent (N : ℕ) (hN : 0<N) [NeZero N] (e : Sector N) :
    sectorCharacter N hN e (frickeGeneratorIndex N hN)=sign e.1 ∧
    ∀ p : SimplePrime N,sectorCharacter N hN e (simpleAtkinGeneratorIndex N hN p)= -delta e p.val := by
  classical
  unfold sectorCharacter
  split_ifs with h
  · have hh := realizedCharacterSector_coherent N hN (Classical.choose h)
    simpa only [Classical.choose_spec h] using hh
  · exact basicSectorCharacter_coherent N hN e

theorem coherent_character_sector_unique (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) (e d : Sector N)
    (heW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hdW : χ (frickeGeneratorIndex N hN)=sign d.1)
    (heS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    (hdS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta d p.val) : e=d := by
  have hinj : Function.Injective sign := by
    intro a b h
    cases a <;> cases b
    · rfl
    · exfalso; norm_num [sign] at h
    · exfalso; norm_num [sign] at h
    · rfl
  apply Prod.ext
  · exact hinj (heW.symm.trans hdW)
  · funext p
    have he := heS p
    rw [hdS] at he
    have hh := neg_injective he
    apply hinj
    simpa only [delta,dite_eq_left p.property] using hh.symm

theorem sectorCharacter_injective (N : ℕ) (hN : 0<N) [NeZero N] :
    Function.Injective (sectorCharacter N hN) := by
  intro e d he
  obtain ⟨heW,heS⟩ := sectorCharacter_coherent N hN e
  obtain ⟨hdW,hdS⟩ := sectorCharacter_coherent N hN d
  rw [←he] at hdW hdS
  exact coherent_character_sector_unique N hN (sectorCharacter N hN e) e d heW hdW heS hdS

#print axioms basicSectorCharacter_norm
#print axioms basicSectorCharacter_coherent
#print axioms sectorCharacter_norm
#print axioms sectorCharacter_coherent
#print axioms coherent_character_sector_unique
#print axioms sectorCharacter_injective

end QuantitativeMaass
