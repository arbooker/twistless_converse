module

public import AsymptoticRegularFoldedTerminalV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularFoldedLow

open UpperHalfPlane Set AsymptoticRegularTrace

variable {L : ℚ} (hL : 0<L) (b d : ℚ)

theorem operator_zero_off_source (s r : Set ℍ) {cap : ℝ} (hcap : 0≤cap)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 1≤t) (z : ℍ) (f : Space) (g : AsymptoticRationalGroup.Group)
    (hg : g • z∉s) : operator hL b d s r hcap hd0 hd1 hstrip t z f g=0 := by
  rw [operator,tsum_apply_coordinate _
    (Summable.of_norm (term_norm_summable hL b d s r hcap hd0 hd1 hstrip ht z))]
  apply Eq.trans ?_ (show (∑' _n : ℤ,(0:ℂ))=0 by simp)
  apply tsum_congr
  intro n
  change AsymptoticFoldedLow.coefficient (show (0:ℝ)<L by exact_mod_cast hL)
    (b:ℝ) (d:ℝ) s r cap t n (g • z)*f (AsymptoticRationalBranches.fold hL b d n*g)=0
  have hn : g • z∉AsymptoticFoldedLow.region (show (0:ℝ)<L by exact_mod_cast hL)
      (b:ℝ) (d:ℝ) s r cap n := fun h => hg h.1.1
  rw [AsymptoticFoldedLow.coefficient,Set.indicator_of_notMem hn,zero_mul]

theorem operator_eq_zero_of_target (s r : Set ℍ) {cap : ℝ} (hcap : 0≤cap)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 1≤t) (z : ℍ) (f : Space)
    (hf : ∀ g : AsymptoticRationalGroup.Group,g • z∈r → f g=0) :
    operator hL b d s r hcap hd0 hd1 hstrip t z f=0 := by
  apply lp.ext
  funext g
  change operator hL b d s r hcap hd0 hd1 hstrip t z f g=0
  rw [operator,tsum_apply_coordinate _
    (Summable.of_norm (term_norm_summable hL b d s r hcap hd0 hd1 hstrip ht z))]
  apply Eq.trans ?_ (show (∑' _n : ℤ,(0:ℂ))=0 by simp)
  apply tsum_congr
  intro n
  change AsymptoticFoldedLow.coefficient (show (0:ℝ)<L by exact_mod_cast hL)
    (b:ℝ) (d:ℝ) s r cap t n (g • z)*f (AsymptoticRationalBranches.fold hL b d n*g)=0
  classical
  by_cases hn : g • z∈AsymptoticFoldedLow.region (show (0:ℝ)<L by exact_mod_cast hL)
      (b:ℝ) (d:ℝ) s r cap n
  · have hr : (AsymptoticRationalBranches.fold hL b d n*g) • z∈r := by
      rw [mul_smul,AsymptoticRationalBranches.fold_action]
      exact hn.1.2
    rw [hf _ hr,mul_zero]
  · rw [AsymptoticFoldedLow.coefficient,Set.indicator_of_notMem hn,zero_mul]

#print axioms operator_zero_off_source
#print axioms operator_eq_zero_of_target

end AsymptoticRegularFoldedLow

namespace AsymptoticRegularFoldedTerminal

open UpperHalfPlane Set AsymptoticRegularTrace
open AsymptoticRegularFoldedLow (Space)

variable {L : ℚ} (hL : 0<L) (b d : ℚ)

theorem operator_zero_off_source (s r : Set ℍ) {ε : ℝ} (hε : 0<ε)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hsource : s⊆{z | z.im≤ε})
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t) (z : ℍ)
    (f : Space) (g : AsymptoticRationalGroup.Group) (hg : g • z∉s) :
    operator hL b d s r hε hd0 hd1 hsource hstrip ht z f g=0 := by
  rw [operator,tsum_apply_coordinate _
    (Summable.of_norm (term_norm_summable hL b d s r hε hd0 hd1 hsource hstrip ht z))]
  apply Eq.trans ?_ (show (∑' _n : ℤ,(0:ℂ))=0 by simp)
  apply tsum_congr
  intro n
  change AsymptoticFoldedTerminal.coefficient (show (0:ℝ)<L by exact_mod_cast hL)
    (b:ℝ) (d:ℝ) s r ε t n (g • z)*f (AsymptoticRationalBranches.fold hL b d n*g)=0
  have hn : g • z∉AsymptoticFoldedTerminal.region (show (0:ℝ)<L by exact_mod_cast hL)
      (b:ℝ) (d:ℝ) s r n := fun h => hg h.1
  rw [AsymptoticFoldedTerminal.coefficient,Set.indicator_of_notMem hn,zero_mul]

#print axioms operator_zero_off_source

end AsymptoticRegularFoldedTerminal
