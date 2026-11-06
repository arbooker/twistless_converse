module

public import AsymptoticFourierTraceContinuityV1
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

/-- Optimizing the actual integer Fourier cutoff gives a square-root loss.
The cutoff is the ceiling of `(m+2)/sqrt(delta)`, not a qualitative choice. -/
theorem exists_fourier_cutoff_sqrt_bound (m : ℕ) {A δ : ℝ} (hA : 0 ≤ A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ M : ℕ, 0 < M ∧
      (M : ℝ) * δ + A * (m + 2 : ℝ) ^ 2 / M ≤
        (2 + A) * (m + 2 : ℝ) * Real.sqrt δ := by
  let a : ℝ := m + 2
  let s : ℝ := Real.sqrt δ
  let M : ℕ := Nat.ceil (a / s)
  have ha : 1 ≤ a := by dsimp [a]; have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hs : 0 < s := Real.sqrt_pos.2 hδ
  have hs1 : s ≤ 1 := by simpa [s] using Real.sqrt_le_sqrt hδ1
  have hss : s ^ 2 = δ := Real.sq_sqrt hδ.le
  have hM : 0 < M := Nat.one_le_ceil_iff.2 (div_pos (lt_of_lt_of_le zero_lt_one ha) hs)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hlo : a ≤ (M : ℝ) * s := (div_le_iff₀ hs).1 (Nat.le_ceil (a / s))
  have hhi : (M : ℝ) * s ≤ a + s := by
    calc
      _ ≤ (a / s + 1) * s := mul_le_mul_of_nonneg_right
        (Nat.ceil_lt_add_one (div_nonneg (le_trans zero_le_one ha) hs.le)).le hs.le
      _ = _ := by field_simp
  have hhead : (M : ℝ) * δ ≤ 2 * a * s := by
    calc
      _ = ((M : ℝ) * s) * s := by rw [← hss]; ring
      _ ≤ (a + s) * s := mul_le_mul_of_nonneg_right hhi hs.le
      _ ≤ 2 * a * s := mul_le_mul_of_nonneg_right (by linarith) hs.le
  have htail : A * a ^ 2 / M ≤ A * a * s := by
    apply (div_le_iff₀ hMr).2
    have hh := mul_le_mul_of_nonneg_left hlo (mul_nonneg hA (le_trans zero_le_one ha))
    nlinarith only [hh]
  refine ⟨M, hM, ?_⟩
  change (M : ℝ) * δ + A * a ^ 2 / M ≤ (2 + A) * a * s
  exact (add_le_add hhead htail).trans_eq (by ring)

open ContinuousLinearMap InnerProductSpace AsymptoticFourierNorm AsymptoticDiagonalTrace
open scoped InnerProduct

/-- Absolute diagonal majorants suffice even when a finite approximation
is not positive. The trace error is bounded using its actual Fourier series. -/
theorem trace_sub_le_absolute_fourier_cutoff {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (b : HilbertBasis ℕ ℂ H) (Q R : H →L[ℂ] H)
    (m t M : ℕ) (hM : 0<M)
    {scale ε C δ : ℝ} (hs : 0<scale) (hε : 0<ε) (hC : 0≤C)
    (hδ : ‖Q-R‖≤δ)
    (hQb : ∀ n,‖(⟪Q (b n),b n⟫_ℂ).re‖≤C*modeRatio m t scale ε (n+1))
    (hRb : ∀ n,‖(⟪R (b n),b n⟫_ℂ).re‖≤C*modeRatio m t scale ε (n+1)) :
    ‖trace b Q-trace b R‖≤(M:ℝ)*δ+
      (2*C*majorantConstant t scale ε)*(m+2:ℕ)^2/(M:ℝ) := by
  let q := fun n => (⟪Q (b n),b n⟫_ℂ).re
  let r := fun n => (⟪R (b n),b n⟫_ℂ).re
  have hmaj := (positive_modeRatio_summable_bound m t hs hε).1.mul_left C
  have hqs : Summable q := Summable.of_norm_bounded hmaj hQb
  have hrs : Summable r := Summable.of_norm_bounded hmaj hRb
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
      exact (norm_sub_le (q j) (r j)).trans (by
        nlinarith [hQb j, hRb j])
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

/-- A quantitative normalized trace estimate for actual Hilbert-basis
traces. Positivity and the common Fourier majorant are the stated inputs;
the infinite trace estimate and integer cutoff are proved, not assumed. -/
theorem normalized_trace_sub_le_sqrt {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (b : HilbertBasis ℕ ℂ H) (Q R : H →L[ℂ] H)
    (hQ : Q.IsPositive) (hR : R.IsPositive) (m t : ℕ)
    {scale ε C δ : ℝ} (hs : 0 < scale) (hε : 0 < ε) (hC : 0 ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hQR : ‖Q - R‖ ≤ δ)
    (hQb : ∀ n, (⟪Q (b n), b n⟫_ℂ).re ≤ C * modeRatio m t scale ε (n + 1))
    (hRb : ∀ n, (⟪R (b n), b n⟫_ℂ).re ≤ C * modeRatio m t scale ε (n + 1)) :
    ‖trace b Q - trace b R‖ / (2 * m + 2 : ℝ) ≤
      (2 + 2 * C * majorantConstant t scale ε) * Real.sqrt δ := by
  have hA : 0 ≤ 2 * C * majorantConstant t scale ε := by
    dsimp [majorantConstant]
    positivity
  obtain ⟨M, hM, hbound⟩ := exists_fourier_cutoff_sqrt_bound m hA hδ hδ1
  have htrace := trace_sub_le_fourier_cutoff b Q R hQ hR m t M hM hs hε hC hQR hQb hRb
  have htrace' : ‖trace b Q - trace b R‖ ≤
      (2 + 2 * C * majorantConstant t scale ε) * (m + 2 : ℝ) * Real.sqrt δ := by
    apply htrace.trans
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hbound
  have hk : 0 < (2 * m + 2 : ℝ) := by positivity
  apply (div_le_iff₀ hk).2
  apply htrace'.trans
  have hm : (m + 2 : ℝ) ≤ 2 * m + 2 := by
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have hh := mul_le_mul_of_nonneg_left hm
    (mul_nonneg (by linarith : 0 ≤ 2 + 2 * C * majorantConstant t scale ε)
      (Real.sqrt_nonneg δ))
  nlinarith only [hh]

/-- The same normalized estimate for signed or nonpositive approximants. -/
theorem normalized_trace_sub_le_sqrt_of_absolute_majorants {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (b : HilbertBasis ℕ ℂ H) (Q R : H →L[ℂ] H)
    (m t : ℕ)
    {scale ε C δ : ℝ} (hs : 0 < scale) (hε : 0 < ε) (hC : 0 ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hQR : ‖Q - R‖ ≤ δ)
    (hQb : ∀ n, ‖(⟪Q (b n), b n⟫_ℂ).re‖ ≤ C * modeRatio m t scale ε (n + 1))
    (hRb : ∀ n, ‖(⟪R (b n), b n⟫_ℂ).re‖ ≤ C * modeRatio m t scale ε (n + 1)) :
    ‖trace b Q - trace b R‖ / (2 * m + 2 : ℝ) ≤
      (2 + 2 * C * majorantConstant t scale ε) * Real.sqrt δ := by
  have hA : 0 ≤ 2 * C * majorantConstant t scale ε := by
    dsimp [majorantConstant]
    positivity
  obtain ⟨M, hM, hbound⟩ := exists_fourier_cutoff_sqrt_bound m hA hδ hδ1
  have htrace := trace_sub_le_absolute_fourier_cutoff b Q R m t M hM hs hε hC hQR hQb hRb
  have htrace' : ‖trace b Q - trace b R‖ ≤
      (2 + 2 * C * majorantConstant t scale ε) * (m + 2 : ℝ) * Real.sqrt δ := by
    apply htrace.trans
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hbound
  have hk : 0 < (2 * m + 2 : ℝ) := by positivity
  apply (div_le_iff₀ hk).2
  apply htrace'.trans
  have hm : (m + 2 : ℝ) ≤ 2 * m + 2 := by
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have hh := mul_le_mul_of_nonneg_left hm
    (mul_nonneg (by linarith : 0 ≤ 2 + 2 * C * majorantConstant t scale ε)
      (Real.sqrt_nonneg δ))
  nlinarith only [hh]

#print axioms exists_fourier_cutoff_sqrt_bound
#print axioms normalized_trace_sub_le_sqrt
#print axioms trace_sub_le_absolute_fourier_cutoff
#print axioms normalized_trace_sub_le_sqrt_of_absolute_majorants

end QuantitativeHolomorphic
