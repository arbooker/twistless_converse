module

public import FinitenessTwistExponentialV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessNormalizedTwistLocal

open Complex FinitenessOriginalInput FinitenessOriginalTwistLocal
  FinitenessTwistConductor FinitenessTwistExponential

noncomputable def sign (N : ℕ) (f : ℕ → ℂ) (p α : ℕ) : ℂ :=
  if α=0 then 1 else if p ∣ N ∧ ¬p^2 ∣ N then -f p*Real.sqrt p else 1

noncomputable def factor (N : ℕ) (f : ℕ → ℂ) (p α : ℕ) (s : ℂ) : ℂ :=
  if α=0 then 1 else scale p (excess N p α) s*D N f p (α-1) (power p (-s))

theorem sign_unit {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (α : ℕ) : sign N f p α=1 ∨ sign N f p α= -1 := by
  unfold sign
  split_ifs with hα hbad
  · exact Or.inl rfl
  · exact bad_root_sign hf hp hbad.1 hbad.2
  · exact Or.inl rfl

theorem reciprocal_succ {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    (hN : 0<N) {p : ℕ} (hp : p.Prime) (j : ℕ) (s : ℂ) :
    factor N f p (j+1) s=(sign N f p (j+1):ℂ)*factor N f p (j+1) (1-s) := by
  simp only [factor,sign,ite_eq_right (by omega : j+1≠0),Nat.add_sub_cancel]
  by_cases hpN : p ∣ N
  · by_cases hpsq : p^2 ∣ N
    · simp only [ite_eq_right (show ¬(p ∣ N ∧ ¬p^2 ∣ N) from fun h => h.2 hpsq),
        one_mul]
      cases j with
      | zero =>
          rw [square_bad_excess hN hp hpsq]
          simp only [scale,power,Nat.cast_zero,zero_mul,zero_div,mul_zero,exp_zero,one_mul,
            (square_bad hf hp hpsq _).1]
      | succ j =>
          rw [(square_bad hf hp hpsq _).2 j,(square_bad hf hp hpsq _).2 j]
          simp
    · simp only [ite_eq_left (show p ∣ N ∧ ¬p^2 ∣ N from ⟨hpN,hpsq⟩)]
      rw [simple_bad_excess hN hp hpN hpsq]
      have hd := bad_reciprocal hf hp hpN hpsq j (power_ne_zero p (-s))
      rw [← reflected hp.pos s,bad_scalar hp.pos j] at hd
      rw [hd]
      have ht := scale_transport p (2*j+1) s
      push_cast at ht
      calc
        _ = (-(f p:ℂ)*(Real.sqrt p:ℂ))*
            (scale p (2*j+1) s*power p ((2*(j:ℂ)+1)*(1/2-s)))*
              D N f p j (power p (-(1-s))) := by ring
        _ = _ := by rw [ht]; ring
  · simp only [ite_eq_right (show ¬(p ∣ N ∧ ¬p^2 ∣ N) from fun h => hpN h.1),
      one_mul]
    rw [good_excess hpN]
    have hd := good_reciprocal f hp.pos hpN j (power_ne_zero p (-s))
    rw [← reflected hp.pos s,good_scalar hp.pos j] at hd
    rw [hd]
    have ht := scale_transport p (2*(j+1)) s
    push_cast at ht
    rw [← mul_assoc,ht]

theorem reciprocal {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    (hN : 0<N) {p : ℕ} (hp : p.Prime) (α : ℕ) (s : ℂ) :
    factor N f p α s=(sign N f p α:ℂ)*factor N f p α (1-s) := by
  cases α with
  | zero => simp [factor,sign]
  | succ j => exact reciprocal_succ hf hN hp j s

theorem polynomial_entire (N : ℕ) (f : ℕ → ℂ) (p j : ℕ) :
    Differentiable ℂ (fun s => D N f p j (power p (-s))) := by
  have hz := (power_entire p).comp differentiable_id.neg
  unfold D FinitenessEulerTwistLocal.polynomial
  exact ((differentiable_const _).mul (hz.pow j)).mul
    (((differentiable_const _).add ((differentiable_const _).mul hz)).sub
      ((differentiable_const _).mul (hz.pow 2)))

theorem factor_entire (N : ℕ) (f : ℕ → ℂ) (p α : ℕ) :
    Differentiable ℂ (factor N f p α) := by
  change Differentiable ℂ (fun s => factor N f p α s)
  by_cases hα : α=0
  · simp only [factor,hα,ite_eq_left]
    exact differentiable_const _
  · simp only [factor,ite_eq_right hα]
    exact (scale_entire p _).mul (polynomial_entire N f p _)

theorem polynomial_bound (N : ℕ) (f : ℕ → ℂ) (p j : ℕ) :
    FinitenessFiniteOrder.Bound (fun s => D N f p j (power p (-s))) := by
  have hz : FinitenessFiniteOrder.Bound (fun s : ℂ => power p (-s)) := by
    have he : (fun s : ℂ => power p (-s))=(fun s => exp (((-Real.log p:ℝ):ℂ)*s)) := by
      funext s
      simp only [power,ofReal_neg,mul_neg,neg_mul]
    rw [he]
    exact FinitenessFiniteOrder.exp_linear _
  unfold D FinitenessEulerTwistLocal.polynomial
  exact FinitenessFiniteOrder.mul
    (FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const _)
      (FinitenessFiniteOrderClosure.pow hz j))
    (FinitenessFiniteOrderClosure.sub
      (FinitenessFiniteOrderClosure.add (FinitenessInputBounds.bound_const _)
        (FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const _) hz))
      (FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const _)
        (FinitenessFiniteOrderClosure.pow hz 2)))

theorem factor_bound (N : ℕ) (f : ℕ → ℂ) (p α : ℕ) :
    FinitenessFiniteOrder.Bound (factor N f p α) := by
  change FinitenessFiniteOrder.Bound (fun s => factor N f p α s)
  by_cases hα : α=0
  · simp only [factor,hα,ite_eq_left]
    exact FinitenessInputBounds.bound_const _
  · simp only [factor,ite_eq_right hα]
    exact FinitenessFiniteOrder.mul (scale_bound p _) (polynomial_bound N f p _)

#print axioms reciprocal
#print axioms factor_entire
#print axioms factor_bound

end FinitenessNormalizedTwistLocal
