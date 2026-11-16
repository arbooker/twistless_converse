module

public import QuantitativeMaassCoprimeAnalyticLawsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

/-- The unnormalized complete ramified average in complex coordinates. -/
def ramifiedAverage (m : ℕ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ a : Fin m,F ((z+(a.val:ℂ))/(m:ℂ))

theorem ramifiedAverage_one (F : ℂ → ℂ) (z : ℂ) : ramifiedAverage 1 F z=F z := by
  simp [ramifiedAverage]

/-- Base-m digits give the exact multiplicative composition of complete
averages, with no analytic or periodicity hypothesis. -/
theorem ramifiedAverage_mul (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (F : ℂ → ℂ) (z : ℂ) :
    ramifiedAverage (m*n) F z=ramifiedAverage n (ramifiedAverage m F) z := by
  classical
  have hm0 : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  have hn0 : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  unfold ramifiedAverage
  rw [←Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)),Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg F
  change (z+((b.val+n*a.val:ℕ):ℂ))/((m*n:ℕ):ℂ)=((z+(b.val:ℂ))/(n:ℂ)+(a.val:ℂ))/(m:ℂ)
  push_cast
  field_simp
  ring

/-- A single ramified eigenrelation supplies all prime-power complete
averages. The parameter need only be a positive integer. -/
theorem ramifiedAverage_pow (p : ℕ) (hp : 0<p) (F : ℂ → ℂ) (δ : ℂ)
    (hU : ∀ z,ramifiedAverage p F z=δ*F z) (k : ℕ) (z : ℂ) :
    ramifiedAverage (p^k) F z=δ^k*F z := by
  induction k generalizing z with
  | zero => simp [ramifiedAverage_one]
  | succ k ih =>
    rw [pow_succ,ramifiedAverage_mul (p^k) p (pow_pos hp k) hp]
    change (∑ a : Fin p,ramifiedAverage (p^k) F ((z+(a.val:ℂ))/(p:ℂ)))=_
    simp_rw [ih]
    rw [←Finset.mul_sum]
    change δ^k*ramifiedAverage p F z=_
    rw [hU,pow_succ,mul_assoc]

/-- The complete translation sum at a prime power is a scaled dilation
of the original function whenever the actual ramified equation holds. -/
theorem completeTranslation_pow (p : ℕ) (hp : 0<p) (F : ℂ → ℂ) (δ : ℂ)
    (hU : ∀ z,ramifiedAverage p F z=δ*F z) (k : ℕ) (z : ℂ) :
    (∑ a : Fin (p^k),F (z+(a.val:ℂ)/(p^k:ℕ)))=δ^k*F ((p^k:ℕ)*z) := by
  have hn : ((p^k:ℕ):ℂ)≠0 := by exact_mod_cast (pow_pos hp k).ne'
  have he := ramifiedAverage_pow p hp F δ hU k (((p^k:ℕ):ℂ)*z)
  unfold ramifiedAverage at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg F
  field_simp

#print axioms ramifiedAverage_one
#print axioms ramifiedAverage_mul
#print axioms ramifiedAverage_pow
#print axioms completeTranslation_pow

end QuantitativeMaass
