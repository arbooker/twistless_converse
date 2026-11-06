module

public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

namespace SpanningVandermonde

variable {K : Type*} [Field K] {n : ℕ}

/-- Exactly the consecutive-coordinate Vandermonde statement needed in
both the addition lemma and initial Fourier vanishing. -/
theorem consecutive_moments_zero {z a : Fin n → K} (hi : Function.Injective z)
    (hz0 : ∀i,z i≠0) (s : ℕ)
    (hz : ∀j:Fin n,∑i:Fin n,a i*z i^(s+j.val)=0) : a=0 := by
  have hh : (fun i:Fin n => a i*z i^s)=0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hi (by
      intro j
      have he : (∑i:Fin n,(a i*z i^s)*z i^j.val)=∑i:Fin n,a i*z i^(s+j.val) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_add,mul_assoc]
      rw [he]
      exact hz j)
  funext i
  have hzero : a i*z i^s=0 := congrFun hh i
  exact (mul_eq_zero.mp hzero).resolve_right (pow_ne_zero _ (hz0 i))

theorem finite_moments_zero {I : Type*} [Fintype I] {z a : I → K}
    (hi : Function.Injective z) (hz0 : ∀i,z i≠0) {L : ℕ}
    (hcard : Fintype.card I≤L) (s : ℕ)
    (hz : ∀j:ℕ,j<L → ∑i:I,a i*z i^(s+j)=0) : a=0 := by
  classical
  let e := Fintype.equivFin I
  have hh := consecutive_moments_zero (z:=fun i => z (e.symm i))
    (a:=fun i => a (e.symm i)) (hi.comp e.symm.injective) (fun i => hz0 _) s (by
      intro j
      exact (e.symm.sum_comp (fun i:I => a i*z i^(s+j.val))).trans
        (hz j.val (j.isLt.trans_le hcard)))
  funext i
  have hi := congrFun hh (e i)
  simpa only [e.symm_apply_apply,Pi.zero_apply] using hi

#print axioms finite_moments_zero

theorem sparse_moments_zero {I : Type*} [Fintype I] {z a : I → K}
    (hi : Function.Injective z) (hz0 : ∀i,z i≠0) (S : Finset I) {L : ℕ}
    (hcard : S.card≤L) (hsupp : ∀i,i∉S → a i=0) (s : ℕ)
    (hz : ∀j:ℕ,j<L → ∑i:I,a i*z i^(s+j)=0) : a=0 := by
  classical
  have hh := finite_moments_zero (I:=S) (z:=fun i => z i.val) (a:=fun i => a i.val)
    (hi.comp Subtype.val_injective) (fun i => hz0 _) (by simpa using hcard) s (by
      intro j hj
      have he := Fintype.sum_of_injective (fun i:S => i.val) Subtype.val_injective
        (fun i:S => a i.val*z i.val^(s+j)) (fun i:I => a i*z i^(s+j))
        (by
          intro i hi
          have hh : i∉S := by simpa using hi
          simp [hsupp i hh])
        (by intro i; rfl)
      exact he.trans (hz j hj))
  funext i
  by_cases hiS : i∈S
  · exact congrFun hh ⟨i,hiS⟩
  · exact hsupp i hiS

#print axioms sparse_moments_zero

end SpanningVandermonde
