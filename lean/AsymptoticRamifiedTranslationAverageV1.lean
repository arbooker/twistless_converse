module

public import AsymptoticRamifiedTwistedLawV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticRamifiedTwistedLaw

open AsymptoticIntegralSubgroup

abbrev Periodic (F : AsymptoticRationalGroup.Group → ℂ) : Prop :=
  ∀ j : ℤ,∀ g,F (translationLabel (j:ℚ)*g)=F g

theorem periodic_mod_fraction (p : ℕ) (hp : 0<p) (F : AsymptoticRationalGroup.Group → ℂ)
    (hF : Periodic F) (a : ℕ) (g : AsymptoticRationalGroup.Group) :
    F (translationLabel ((a%p:ℕ)/p:ℚ)*g)=F (translationLabel ((a:ℚ)/p)*g) := by
  have hp' : (p:ℚ)≠0 := by exact_mod_cast hp.ne'
  have ha : ((a%p:ℕ):ℚ)/p+((a/p:ℕ):ℚ)=(a:ℚ)/p := by
    have he : ((a%p:ℕ):ℚ)+(p:ℚ)*((a/p:ℕ):ℚ)=(a:ℚ) := by
      exact_mod_cast Nat.mod_add_div a p
    field_simp
    linear_combination he
  have he := hF ((a/p:ℕ):ℤ) (translationLabel (((a%p:ℕ):ℚ)/p)*g)
  rw [← mul_assoc,translationLabel_mul] at he
  simp only [Int.cast_natCast] at he
  rw [add_comm,ha] at he
  exact he.symm

theorem periodic_fraction_add (p : ℕ) (hp : 0<p) (F : AsymptoticRationalGroup.Group → ℂ)
    (hF : Periodic F) (a b : Fin p) (g : AsymptoticRationalGroup.Group) :
    F (translationLabel (((a+b).val:ℚ)/p)*g)=
      F (translationLabel ((a.val:ℚ)/p)*(translationLabel ((b.val:ℚ)/p)*g)) := by
  rw [← mul_assoc,translationLabel_mul,← add_div]
  rw [Fin.val_add]
  simpa only [Nat.cast_add] using periodic_mod_fraction p hp F hF (a.val+b.val) g

theorem residueSum_translate (p : ℕ) (hp : 0<p) (F : AsymptoticRationalGroup.Group → ℂ)
    (hF : Periodic F) (b : Fin p) (g : AsymptoticRationalGroup.Group) :
    residueSum p F (translationLabel ((b.val:ℚ)/p)*g)=residueSum p F g := by
  let : NeZero p := ⟨hp.ne'⟩
  unfold residueSum
  simp_rw [← periodic_fraction_add p hp F hF]
  exact Equiv.sum_comp (Equiv.addRight b) (fun a : Fin p => F (translationLabel ((a.val:ℚ)/p)*g))

/-- The full translation sum is p times an idempotent on period-one
functions. This is a finite counting argument, without a Fourier model. -/
theorem residueSum_squared (p : ℕ) (hp : 0<p) (F : AsymptoticRationalGroup.Group → ℂ)
    (hF : Periodic F) (g : AsymptoticRationalGroup.Group) :
    residueSum p (residueSum p F) g=(p:ℂ)*residueSum p F g := by
  change (∑ a : Fin p,residueSum p F (translationLabel ((a.val:ℚ)/p)*g))=_
  simp_rw [residueSum_translate p hp F hF]
  simp

theorem residueSum_sub (p : ℕ) (F H : AsymptoticRationalGroup.Group → ℂ)
    (g : AsymptoticRationalGroup.Group) :
    residueSum p (fun a => F a-H a) g=residueSum p F g-residueSum p H g := by
  simp only [residueSum,Finset.sum_sub_distrib]

/-- Invertibility of C_p on period-one functions, valid already for
any integer p>1 when C_p sums all nonzero residues. -/
theorem puncturedSum_eq_zero (p : ℕ) (hp : 1<p) (F : AsymptoticRationalGroup.Group → ℂ)
    (hF : Periodic F) (hz : ∀ g,puncturedSum p F g=0) : F=0 := by
  have he : residueSum p F=F := by
    funext g
    exact sub_eq_zero.mp (hz g)
  have hsq (g : AsymptoticRationalGroup.Group) : F g=(p:ℂ)*F g := by
    have hh := residueSum_squared p (by omega) F hF g
    simpa only [he] using hh
  funext g
  have hmul : ((p:ℂ)-1)*F g=0 := by
    linear_combination -(hsq g)
  have hp' : (p:ℂ)-1≠0 := by
    exact_mod_cast (show (p:ℤ)-1≠0 by omega)
  exact (mul_eq_zero.mp hmul).resolve_left hp'

#print axioms periodic_mod_fraction
#print axioms periodic_fraction_add
#print axioms residueSum_translate
#print axioms residueSum_squared
#print axioms residueSum_sub
#print axioms puncturedSum_eq_zero

end AsymptoticRamifiedTwistedLaw
