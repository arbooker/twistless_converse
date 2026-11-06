module

public import AsymptoticHolomorphicTraceV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticDiagonalTrace

open ContinuousLinearMap InnerProductSpace AsymptoticFourierNorm
open scoped InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem diagonal_sub_norm_le (b : HilbertBasis ℕ ℂ H) (Q R : H →L[ℂ] H) (n : ℕ) :
    ‖(⟪Q (b n),b n⟫_ℂ).re-(⟪R (b n),b n⟫_ℂ).re‖≤‖Q-R‖ := by
  have he : (⟪Q (b n),b n⟫_ℂ).re-(⟪R (b n),b n⟫_ℂ).re=
      (⟪(Q-R) (b n),b n⟫_ℂ).re := by rw [sub_apply,inner_sub_left,Complex.sub_re]
  rw [he,Real.norm_eq_abs]
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_inner_le_norm _ _).trans
  have hb := b.orthonormal.norm_eq_one n
  rw [hb,mul_one]
  simpa only [hb,mul_one] using (Q-R).le_opNorm (b n)

/-- Norm error and the common quadratic Fourier tail imply a trace
error. Summability of each positive trace is derived from the same tail. -/
theorem trace_sub_le_fourier_cutoff (b : HilbertBasis ℕ ℂ H) (Q R : H →L[ℂ] H)
    (hQ : Q.IsPositive) (hR : R.IsPositive) (m t M : ℕ) (hM : 0<M)
    {scale ε C δ : ℝ} (hs : 0<scale) (hε : 0<ε) (hC : 0≤C)
    (hδ : ‖Q-R‖≤δ)
    (hQb : ∀ n,(⟪Q (b n),b n⟫_ℂ).re≤C*modeRatio m t scale ε (n+1))
    (hRb : ∀ n,(⟪R (b n),b n⟫_ℂ).re≤C*modeRatio m t scale ε (n+1)) :
    ‖trace b Q-trace b R‖≤(M:ℝ)*δ+
      (2*C*majorantConstant t scale ε)*(m+2:ℕ)^2/(M:ℝ) := by
  let q := fun n => (⟪Q (b n),b n⟫_ℂ).re
  let r := fun n => (⟪R (b n),b n⟫_ℂ).re
  have hq0 : ∀ n,0≤q n := fun n => hQ.re_inner_nonneg_left (b n)
  have hr0 : ∀ n,0≤r n := fun n => hR.re_inner_nonneg_left (b n)
  have hmaj := (positive_modeRatio_summable_bound m t hs hε).1.mul_left C
  have hqs : Summable q := Summable.of_nonneg_of_le hq0 hQb hmaj
  have hrs : Summable r := Summable.of_nonneg_of_le hr0 hRb hmaj
  let d : ℕ → ℝ := fun n => if n=0 then 0 else ‖q (n-1)-r (n-1)‖
  have hd0 : d 0=0 := by simp [d]
  have hdsucc (n : ℕ) : d (n+1)=‖q n-r n‖ := by simp [d]
  have hdhead (n : ℕ) (hn : 0<n) : d n≤δ := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [hdsucc]
    exact (diagonal_sub_norm_le b Q R j).trans hδ
  have hdtail (n : ℕ) (hn : 0<n) :
      d n≤(2*C*majorantConstant t scale ε)*(m+2:ℕ)^2*((n:ℝ)^2)⁻¹ := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [hdsucc]
    have hdqr : ‖q j-r j‖≤2*C*modeRatio m t scale ε (j+1) := by
      rw [Real.norm_eq_abs]
      exact (abs_sub_le (q j) 0 (r j)).trans (by
        rw [sub_zero,zero_sub,abs_of_nonneg (hq0 j),abs_neg,abs_of_nonneg (hr0 j)]
        nlinarith [hQb j,hRb j])
    apply hdqr.trans
    calc
      2*C*modeRatio m t scale ε (j+1) ≤
          2*C*(majorantConstant t scale ε*(m+2:ℕ)^2*((((j+1:ℕ):ℝ)^2)⁻¹)) :=
        mul_le_mul_of_nonneg_left (modeRatio_le_tail m t (j+1) hs hε) (by positivity)
      _ = _ := by ring
  have hct : 0≤2*C*majorantConstant t scale ε := by dsimp [majorantConstant]; positivity
  have hd := AsymptoticTraceCutoff.summable_and_tsum_bound d hM hct hd0
    (fun n => by dsimp [d]; split_ifs <;> positivity)
    (fun n hn _ => hdhead n hn) (fun n hn => hdtail n (lt_trans hM hn))
  have hdshift : Summable (fun n => d (n+1)) := hd.1.comp_injective Nat.succ_injective
  have he := tsum_eq_zero_add' hdshift
  rw [hd0,zero_add] at he
  change ‖(∑' n,q n)-(∑' n,r n)‖≤_
  rw [← hqs.tsum_sub hrs]
  apply (norm_tsum_le_tsum_norm (hqs.sub hrs).norm).trans
  have hshift : (∑' n,‖q n-r n‖)=∑' n,d n := by
    rw [he]
    exact tsum_congr (fun n => (hdsucc n).symm)
  rw [hshift]
  exact hd.2

#print axioms diagonal_sub_norm_le
#print axioms trace_sub_le_fourier_cutoff

end AsymptoticDiagonalTrace
