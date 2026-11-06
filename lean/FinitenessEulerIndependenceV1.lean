module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs

set_option autoImplicit false

public section

namespace FinitenessEulerIndependence

variable {I K : Type*} [Field K]

/-- Joint coefficient-Hecke eigenrelations separate Euler sequences.
Unlike multiplicative-only independence, no cofinite prime disagreement
or analytic inequivalence theorem is needed. -/
theorem relation (f : I → ℕ → K) (beta : ℕ → K) (P : ℕ → Prop)
    (hone : ∀ i, f i 1 = 1)
    (hrec : ∀ i p, P p → ∀ n,
      f i (p*n)+(if p ∣ n then beta p else 0)*f i (n/p)=f i p*f i n)
    (hsep : ∀ i j, i ≠ j → ∃ p, P p ∧ f i p ≠ f j p)
    (s : Finset I) : ∀ a : I → K,
      (∀ n, ∑ i ∈ s, a i*f i n=0) → ∀ i ∈ s, a i=0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      intro a ha
      have hs : ∀ j ∈ s, a j=0 := by
        intro j hj
        have hji : j ≠ i := fun he => hi (he ▸ hj)
        obtain ⟨p,hp,hd⟩ := hsep j i hji
        let b : I → K := fun l => a l*(f l p-f i p)
        have hb : ∀ n, ∑ l ∈ s, b l*f l n=0 := by
          intro n
          have he : (∑ l ∈ insert i s, b l*f l n)=
              (∑ l ∈ insert i s, a l*f l (p*n))+
                (if p ∣ n then beta p else 0)*(∑ l ∈ insert i s, a l*f l (n/p))-
                f i p*(∑ l ∈ insert i s, a l*f l n) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
              ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro l _
            have hr := hrec l p hp n
            dsimp only [b]
            calc
              a l*(f l p-f i p)*f l n
                  = a l*(f l p*f l n)-f i p*(a l*f l n) := by
                    simp only [mul_sub, sub_mul, mul_assoc, mul_left_comm]
              _ = a l*(f l (p*n)+(if p ∣ n then beta p else 0)*f l (n/p))-
                    f i p*(a l*f l n) := by rw [hr]
              _ = _ := by simp only [mul_add, mul_left_comm]
          rw [ha (p*n), ha (n/p), ha n] at he
          simpa [Finset.sum_insert, hi, b] using he
        have hz := ih b hb j hj
        exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hd)
      have hai : a i=0 := by
        have h := ha 1
        have hz : ∑ j ∈ s, a j=0 := Finset.sum_eq_zero hs
        simpa [Finset.sum_insert, hi, hone, hz] using h
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hai
      · exact hs j hj

theorem linearIndependent (f : I → ℕ → K) (beta : ℕ → K) (P : ℕ → Prop)
    (hone : ∀ i, f i 1=1)
    (hrec : ∀ i p, P p → ∀ n,
      f i (p*n)+(if p ∣ n then beta p else 0)*f i (n/p)=f i p*f i n)
    (hsep : ∀ i j, i ≠ j → ∃ p, P p ∧ f i p ≠ f j p) :
    LinearIndependent K f := by
  rw [linearIndependent_iff']
  intro s a ha
  apply relation f beta P hone hrec hsep s a
  intro n
  simpa using congrFun ha n

#print axioms relation
#print axioms linearIndependent

end FinitenessEulerIndependence
