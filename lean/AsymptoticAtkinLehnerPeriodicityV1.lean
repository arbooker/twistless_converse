module

public import AsymptoticAtkinLehnerComplementV1
public import AsymptoticRamifiedTranslationAverageV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticAtkinLehner

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticFreshMatrices AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticIntegralSubgroup AsymptoticRamifiedTwistedLaw
open scoped MatrixGroups

def translationConjugate (M p : ℕ) (j : ℤ) : SL(2,ℤ) :=
  ⟨!![1-(p:ℤ)*(M:ℤ)*j,(M:ℤ)*j;-(p:ℤ)^2*(M:ℤ)*j,1+(p:ℤ)*(M:ℤ)*j],by
    rw [Matrix.det_fin_two]
    change (1-(p:ℤ)*(M:ℤ)*j)*(1+(p:ℤ)*(M:ℤ)*j)-((M:ℤ)*j)*(-(p:ℤ)^2*(M:ℤ)*j)=1
    ring⟩

theorem translationConjugate_mem (M p : ℕ) (j : ℤ) :
    translationConjugate M p j∈CongruenceSubgroup.Gamma0 (p*M) := by
  rw [gamma0_mem_dvd]
  refine ⟨-(p:ℤ)*j,?_⟩
  change -(p:ℤ)^2*(M:ℤ)*j=((p*M:ℕ):ℤ)*(-(p:ℤ)*j)
  rw [Nat.cast_mul]
  ring

theorem complement_translation (M p : ℕ) (hM : 0<M) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (j : ℤ) :
    complement M p hM A B hAB*translationLabel (j:ℚ)=
      integralLabel (translationConjugate M p j)*complement M p hM A B hAB := by
  have hb : (p:ℚ)*(A:ℚ)+(M:ℚ)*(B:ℚ)=1 := by exact_mod_cast hAB
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (complementGL M p hM A B hAB)*rationalMap (AsymptoticMobiusFold.translation (j:ℚ))=
    rationalMap (rationalGL (translationConjugate M p j))*rationalMap (complementGL M p hM A B hAB)
  rw [← map_mul,← map_mul]
  congr 1
  apply Units.ext
  change (complementGL M p hM A B hAB).val*(AsymptoticMobiusFold.translation (j:ℚ)).val=
    (translationConjugate M p j).val.map (fun z : ℤ => (z:ℚ))*(complementGL M p hM A B hAB).val
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [complementGL,AsymptoticFreshMatrices.representative,entries,translationConjugate,AsymptoticMobiusFold.translation,
      GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two]
  · ring
  · linear_combination -(M:ℚ)*(j:ℚ)*hb
  · ring
  · linear_combination -(p:ℚ)*(M:ℚ)*(j:ℚ)*hb

theorem periodic_complement (M p : ℕ) (hM : 0<M) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (F : AsymptoticRationalGroup.Group → ℂ)
    (hF : ∀ a : gamma (p*M),∀ g,F (a.val*g)=F g) :
    Periodic (fun g => F (complement M p hM A B hAB*g)) := by
  intro j g
  change F (complement M p hM A B hAB*(translationLabel (j:ℚ)*g))=F (complement M p hM A B hAB*g)
  rw [← mul_assoc,complement_translation,mul_assoc]
  exact hF ⟨integralLabel (translationConjugate M p j),
    ⟨translationConjugate M p j,translationConjugate_mem M p j,rfl⟩⟩ _

theorem periodic_of_gamma (N : ℕ) (F : AsymptoticRationalGroup.Group → ℂ)
    (hF : ∀ a : gamma N,∀ g,F (a.val*g)=F g) : Periodic F := by
  intro j g
  exact hF ⟨translationLabel (j:ℚ),translation_mem N j⟩ g

#print axioms translationConjugate_mem
#print axioms complement_translation
#print axioms periodic_complement
#print axioms periodic_of_gamma

end AsymptoticAtkinLehner
