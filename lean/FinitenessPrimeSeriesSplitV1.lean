module

public import FinitenessOriginalTwistLocalV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessPrimeSeriesSplit

abbrev Positive := {n : ℕ // n≠0}
abbrev CoprimePart (p : ℕ) := {n : ℕ // n≠0 ∧ p.Coprime n}

/-- Every positive integer is uniquely p^e*m with p coprime to m. -/
noncomputable def primeEquiv {p : ℕ} (hp : p.Prime) : ℕ × CoprimePart p ≃ Positive where
  toFun := fun x => ⟨p^x.1*x.2.val,mul_ne_zero (pow_ne_zero _ hp.ne_zero) x.2.property.1⟩
  invFun := fun n => (n.val.factorization p,
    ⟨n.val/(p^(n.val.factorization p)),(Nat.ordCompl_pos p n.property).ne',
      Nat.coprime_ordCompl hp n.property⟩)
  right_inv := by
    intro n
    apply Subtype.ext
    exact Nat.ordProj_mul_ordCompl_eq_self n.val p
  left_inv := by
    rintro ⟨e,m,hm0,hm⟩
    have hn : ¬p ∣ m := hp.coprime_iff_not_dvd.mp hm
    have hv : (p^e*m).factorization p=e := by
      rw [Nat.factorization_mul (pow_ne_zero e hp.ne_zero) hm0,Finsupp.add_apply,
        Nat.factorization_pow_self hp,Nat.factorization_eq_zero_of_not_dvd hn,Nat.add_zero]
    apply Prod.ext
    · exact hv
    · apply Subtype.ext
      change (p^e*m)/(p^((p^e*m).factorization p))=m
      rw [hv,Nat.mul_div_cancel_left _ (pow_pos hp.pos e)]

theorem tsum_positive {F : ℕ → ℂ} (hF : F 0=0) :
    (∑' n : Positive, F n.val)=∑' n : ℕ, F n := by
  apply tsum_subtype_eq_of_support_subset
  intro n hn
  change n≠0
  intro h
  exact hn (h ▸ hF)

/-- Actual reindexing of an absolutely convergent sum, with zero removed
explicitly. No formal rearrangement of a divergent Euler product. -/
theorem tsum_decomposition {p : ℕ} (hp : p.Prime) {F : ℕ → ℂ}
    (hF : F 0=0) (hs : Summable F) :
    (∑' n : ℕ, F n)=∑' e : ℕ, ∑' m : CoprimePart p, F (p^e*m.val) := by
  have ht : Summable (fun x : ℕ × CoprimePart p => F (p^x.1*x.2.val)) := by
    exact (primeEquiv hp).summable_iff.mpr (hs.subtype (fun n => n≠0))
  calc
    (∑' n : ℕ, F n)=(∑' n : Positive, F n.val) := (tsum_positive hF).symm
    _ = ∑' x : ℕ × CoprimePart p, F (p^x.1*x.2.val) :=
      ((primeEquiv hp).tsum_eq (fun n => F n.val)).symm
    _ = _ := ht.tsum_prod

theorem separated_sum {p : ℕ} (hp : p.Prime) {F : ℕ → ℂ}
    (hF : F 0=0) (hs : Summable F) (A : ℕ → ℂ) (B : CoprimePart p → ℂ)
    (he : ∀ e m, F (p^e*m.val)=A e*B m) :
    (∑' n : ℕ, F n)=(∑' e : ℕ, A e)*(∑' m : CoprimePart p, B m) := by
  rw [tsum_decomposition hp hF hs]
  have H : (∑' e : ℕ, ∑' m : CoprimePart p, F (p^e*m.val))=
      ∑' e : ℕ, A e*(∑' m : CoprimePart p, B m) := by
    apply tsum_congr
    intro e
    rw [← tsum_mul_left]
    exact tsum_congr (fun m => he e m)
  rw [H,tsum_mul_right]

#print axioms primeEquiv
#print axioms tsum_decomposition
#print axioms separated_sum

end FinitenessPrimeSeriesSplit
