module

public import AsymptoticAtkinLehnerPeriodicityV1
public import AsymptoticRamifiedNonzeroSumV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticAtkinLehner

open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticFreshMatrices
open AsymptoticIntegralSubgroup AsymptoticRamifiedTwistedLaw AsymptoticFreshResidues
open AsymptoticFreshAveraging AsymptoticOrbitDecode

variable (M p : ℕ) [Fact p.Prime] (hM : 0<M) (hpM : ¬p∣M)
variable (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
variable (F : AsymptoticRationalGroup.Group → ℂ)
variable (hF : ∀ a : gamma (p*M),∀ g,F (a.val*g)=F g)

include hpM hF

/-- All reflected nonzero residue branches belong to the same
complementary Atkin--Lehner coset, after the proved residue permutation. -/
theorem defect_complement (i : Fin (p-1)) (g : AsymptoticRationalGroup.Group) :
    F (defectLabel M p hM hpM i*g)=F (complement M p hM A B hAB*g) := by
  rw [defectLabel,label_eq_comparison_complement M p hM (Fact.out : p.Prime).pos A B
    ((permutation p M hpM i).val+1) (i.val+1) (quotient p M hpM i) hAB
    (quotient_relation p M hpM i),mul_assoc]
  exact hF ⟨integralLabel (comparison M p A B ((permutation p M hpM i).val+1)
    (i.val+1) (quotient p M hpM i) hAB (quotient_relation p M hpM i)),
    ⟨_,comparison_mem M p A B _ _ _ hAB (quotient_relation p M hpM i),rfl⟩⟩ _

theorem complementary_sum (g : AsymptoticRationalGroup.Group) :
    puncturedSum p F (frickeLabel (p*(p*M)) (Nat.mul_pos (Fact.out : p.Prime).pos
      (Nat.mul_pos (Fact.out : p.Prime).pos hM))*g)=
      puncturedSum p (fun a => F (complement M p hM A B hAB*a)) g := by
  rw [puncturedSum_eq_primeLabels p (Fact.out : p.Prime).pos,
    puncturedSum_eq_primeLabels p (Fact.out : p.Prime).pos]
  have href (i : Fin (p-1)) : F (primeLabels p i*
      (frickeLabel (p*(p*M)) (Nat.mul_pos (Fact.out : p.Prime).pos
        (Nat.mul_pos (Fact.out : p.Prime).pos hM))*g))=F (reflectedLabel M p hM i*g) := by
    rw [reflectedLabel_eq,mul_assoc]
  simp_rw [href]
  calc
    _ = ∑ i : Fin (p-1),F (reflectedLabel M p hM (permutation p M hpM i)*g) :=
      (Equiv.sum_comp (permutation p M hpM) (fun i => F (reflectedLabel M p hM i*g))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← defectLabel_translation M p hM hpM,mul_assoc,defect_complement M p hM hpM A B hAB F hF]

/-- The local complementary Atkin--Lehner sign is forced by the original
Fricke and ramified incidence equations and literal Γ₀(pM) invariance. -/
theorem complement_eigen (w δ : ℂ) (hδ : δ^2=1)
    (hW : ∀ g,w*F (frickeLabel (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)*g)=F g)
    (hU : ∀ g,∑ a : Fin p,F (ramifiedLabel p (Fact.out : p.Prime).pos a*g)=δ*F g)
    (g : AsymptoticRationalGroup.Group) : F (complement M p hM A B hAB*g)=(-w*δ)*F g := by
  have he : (fun a => F (complement M p hM A B hAB*a))=(fun a => (-w*δ)*F a) := by
    apply puncturedSum_injective p (Fact.out : p.Prime).one_lt
      _ _ (periodic_complement M p hM A B hAB F hF)
      (fun j a => by rw [periodic_of_gamma (p*M) F hF j a])
    intro a
    rw [← complementary_sum M p hM hpM A B hAB F hF,
      punctured_fricke (p*M) p (Nat.mul_pos (Fact.out : p.Prime).pos hM)
        (Fact.out : p.Prime).pos F w δ hδ hW hU,puncturedSum_mul]
  exact congrFun he g

#print axioms defect_complement
#print axioms complementary_sum
#print axioms complement_eigen

end AsymptoticAtkinLehner
