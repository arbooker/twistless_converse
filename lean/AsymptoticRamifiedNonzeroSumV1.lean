module

public import AsymptoticRamifiedTranslationAverageV1
public import AsymptoticFreshAveragingV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRamifiedTwistedLaw

open AsymptoticIntegralSubgroup AsymptoticFreshAveraging
open AsymptoticFreshMatrices AsymptoticRationalGroup AsymptoticRationalBranches
open AsymptoticRationalFreeness AsymptoticReconstructionBranch Matrix

theorem translationLabel_zero : translationLabel (0:ℚ)=1 := by
  apply mul_left_cancel (a:=translationLabel (0:ℚ))
  simpa using translationLabel_mul (0:ℚ) 0

theorem puncturedSum_eq_primeLabels (p : ℕ) (hp : 0<p)
    (F : AsymptoticRationalGroup.Group → ℂ) (g : AsymptoticRationalGroup.Group) :
    puncturedSum p F g=∑ i : Fin (p-1),F (primeLabels p i*g) := by
  cases p with
  | zero => omega
  | succ n =>
    simp [puncturedSum,residueSum,Fin.sum_univ_succ,primeLabels,translationLabel_zero]

theorem puncturedSum_sub (p : ℕ) (F H : AsymptoticRationalGroup.Group → ℂ)
    (g : AsymptoticRationalGroup.Group) :
    puncturedSum p (fun a => F a-H a) g=puncturedSum p F g-puncturedSum p H g := by
  rw [puncturedSum,puncturedSum,puncturedSum,residueSum_sub]
  ring

theorem puncturedSum_mul (p : ℕ) (F : AsymptoticRationalGroup.Group → ℂ) (c : ℂ)
    (g : AsymptoticRationalGroup.Group) :
    puncturedSum p (fun a => c*F a) g=c*puncturedSum p F g := by
  simp only [puncturedSum,residueSum,← Finset.mul_sum]
  ring

theorem puncturedSum_injective (p : ℕ) (hp : 1<p) (F H : AsymptoticRationalGroup.Group → ℂ)
    (hF : Periodic F) (hH : Periodic H) (he : ∀ g,puncturedSum p F g=puncturedSum p H g) : F=H := by
  have hz : (fun g => F g-H g)=0 := puncturedSum_eq_zero p hp _
    (fun j g => by simp only [hF,hH]) (fun g => by rw [puncturedSum_sub,he,sub_self])
  funext g
  exact sub_eq_zero.mp (congrFun hz g)

theorem reflectedLabel_eq (M p : ℕ) [Fact p.Prime] (hM : 0<M) (i : Fin (p-1)) :
    reflectedLabel M p hM i=primeLabels p i*
      frickeLabel (p*(p*M)) (Nat.mul_pos (Fact.out : p.Prime).pos
        (Nat.mul_pos (Fact.out : p.Prime).pos hM)) := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (branch ((M:ℚ)*p^2) 0 (((i.val+1:ℕ):ℚ)/p) _)=
    rationalMap (AsymptoticMobiusFold.translation (((i.val+1:ℕ):ℚ)/p))*
      rationalMap (branch ((p*(p*M):ℕ):ℚ) 0 0 _)
  rw [← map_mul]
  congr 1
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [branch,AsymptoticMobiusFold.translation,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring_nf
  all_goals simp

#print axioms translationLabel_zero
#print axioms puncturedSum_eq_primeLabels
#print axioms puncturedSum_sub
#print axioms puncturedSum_mul
#print axioms puncturedSum_injective
#print axioms reflectedLabel_eq

end AsymptoticRamifiedTwistedLaw
