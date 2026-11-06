module

public import AsymptoticFourierNormV1
public import AsymptoticTraceCutoffV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFourierNorm

open scoped BigOperators

theorem ratio_le_uniform_quadratic (m t : ℕ) {r ε : ℝ} (hr : 0<r) (hε : 0<ε) :
    beta m (t+1) r ε / beta m t r ε ≤
      4*((m+2*t:ℕ)+1:ℝ)*((m+2*t:ℕ)+2:ℝ)/(r*ε)^2 := by
  by_cases ht : 2*((m+2*t:ℕ)+1:ℝ)≤r*ε
  · apply (ratio_le_quadratic m t hr hε ht).trans
    gcongr
    norm_num
  · have hsmall : r*ε<2*((m+2*t:ℕ)+1:ℝ) := lt_of_not_ge ht
    apply (ratio_le_one m t hr hε).trans
    apply (le_div_iff₀ (sq_pos_of_pos (mul_pos hr hε))).mpr
    have hsq := mul_self_le_mul_self (mul_nonneg hr.le hε.le) hsmall.le
    nlinarith

/-- Mode zero is absent for cusp functions. Positive modes use the actual
radial integrals, with frequency scale 4π in the paper. -/
noncomputable def modeRatio (m t : ℕ) (scale ε : ℝ) (n : ℕ) : ℝ :=
  if n=0 then 0 else beta m (t+1) (scale*n) ε / beta m t (scale*n) ε

theorem modeRatio_nonneg (m t n : ℕ) (scale : ℝ) {ε : ℝ} (hε : 0<ε) :
    0≤modeRatio m t scale ε n := by
  unfold modeRatio
  split_ifs
  · exact le_rfl
  · exact div_nonneg (beta_nonneg m (t+1) hε) (beta_nonneg m t hε)

theorem modeRatio_le_one (m t n : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    modeRatio m t scale ε n≤1 := by
  unfold modeRatio
  split_ifs with hn
  · norm_num
  · exact ratio_le_one m t (mul_pos hs (by exact_mod_cast Nat.pos_of_ne_zero hn)) hε

/-- A constant depending only on the fixed cylinder weight and cutoff,
not on the holomorphic weight or the Fourier mode. -/
noncomputable def majorantConstant (t : ℕ) (scale ε : ℝ) : ℝ :=
  4*((t:ℝ)+1)^2/(scale*ε)^2

theorem modeRatio_le_tail (m t n : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    modeRatio m t scale ε n≤majorantConstant t scale ε*(m+2:ℕ)^2*((n:ℝ)^2)⁻¹ := by
  by_cases hn : n=0
  · simp [modeRatio,hn]
  have hn' : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [modeRatio,ite_eq_right hn]
  apply (ratio_le_uniform_quadratic m t (mul_pos hs hn') hε).trans
  have hma : ((m+2*t:ℕ)+1:ℝ)≤((t:ℝ)+1)*((m:ℝ)+2) := by push_cast; nlinarith
  have hmb : ((m+2*t:ℕ)+2:ℝ)≤((t:ℝ)+1)*((m:ℝ)+2) := by push_cast; nlinarith
  calc
    4*((m+2*t:ℕ)+1:ℝ)*((m+2*t:ℕ)+2:ℝ)/((scale*(n:ℝ))*ε)^2 ≤
      4*(((t:ℝ)+1)*((m:ℝ)+2))*(((t:ℝ)+1)*((m:ℝ)+2))/((scale*(n:ℝ))*ε)^2 := by gcongr
    _ = _ := by dsimp [majorantConstant]; push_cast; field_simp

/-- The actual Fourier-ratio diagonal is summable, with a bound linear in
k=m+2 and uniform in the observation operator. -/
theorem modeRatio_summable_bound (m t : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    Summable (modeRatio m t scale ε) ∧
      (∑' n,modeRatio m t scale ε n)≤(1+majorantConstant t scale ε)*(m+2:ℕ) := by
  have hC : 0≤majorantConstant t scale ε := by dsimp [majorantConstant]; positivity
  have hh := AsymptoticTraceCutoff.summable_and_tsum_bound
    (modeRatio m t scale ε) (k:=m+2) (M:=m+2) (δ:=1) (C:=majorantConstant t scale ε)
    (by omega) hC (by simp [modeRatio]) (fun n => modeRatio_nonneg m t n scale hε)
    (fun n _ _ => modeRatio_le_one m t n hs hε) (fun n _ => modeRatio_le_tail m t n hs hε)
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  have hm : (m+2:ℕ)≠0 := by omega
  field_simp

/-- The positive-frequency indexing used by a Hilbert basis, starting at
frequency n+1. -/
theorem positive_modeRatio_summable_bound (m t : ℕ) {scale ε : ℝ}
    (hs : 0<scale) (hε : 0<ε) :
    Summable (fun n => modeRatio m t scale ε (n+1)) ∧
      (∑' n,modeRatio m t scale ε (n+1))≤(1+majorantConstant t scale ε)*(m+2:ℕ) := by
  have hh := modeRatio_summable_bound m t hs hε
  have hshift : Summable (fun n => modeRatio m t scale ε (n+1)) :=
    hh.1.comp_injective Nat.succ_injective
  refine ⟨hshift,?_⟩
  have he := tsum_eq_zero_add' hshift
  have hz : modeRatio m t scale ε 0=0 := by simp [modeRatio]
  rw [hz,zero_add] at he
  rw [← he]
  exact hh.2

#print axioms positive_modeRatio_summable_bound
#print axioms modeRatio_le_tail
#print axioms modeRatio_summable_bound

end AsymptoticFourierNorm
