module

public import AsymptoticFoldSumV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFoldMajorant

/-- A width-one strip leaves three central integer folds. Every other
fold is separated uniformly, even as the target varies across the strip. -/
theorem separation {a : ℝ} (ha : |a|≤1) {n : ℤ} (hn : 1 < |n|) :
    |(n:ℝ)|/2≤|(n:ℝ)+a| := by
  have hn' : (2 : ℝ)≤|(n:ℝ)| := by exact_mod_cast (show 2≤|n| by omega)
  have hh := abs_add_le ((n:ℝ)+a) (-a)
  simp only [add_neg_cancel_right,abs_neg] at hh
  linarith

theorem inverse_ratio_tail {a L v : ℝ} (ha : |a|≤1) (hL : 0<L)
    {n : ℤ} (hn : 1 < |n|) :
    (L*(((n:ℝ)+a)^2+v^2))⁻¹≤(4/L)*((n:ℝ)^2)⁻¹ := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by rintro rfl; norm_num at hn)
  have hs := separation ha hn
  have hd : (n:ℝ)^2/4≤((n:ℝ)+a)^2+v^2 := by
    have hh := mul_self_le_mul_self (by positivity : 0≤|(n:ℝ)|/2) hs
    nlinarith [sq_abs (n:ℝ),sq_abs ((n:ℝ)+a),sq_nonneg v]
  calc
    (L*(((n:ℝ)+a)^2+v^2))⁻¹≤(L*((n:ℝ)^2/4))⁻¹ :=
      inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hd hL.le)
    _ = _ := by field_simp

/-- A bound uniform over a width-one strip, suitable for summing the
operator norms of the separate Möbius folds. -/
theorem sum_bound (r : ℤ → ℝ) {cap D : ℝ} (hD : 0≤D)
    (hr : ∀ n,0≤r n) (hcap : ∀ n,r n≤cap)
    (htail : ∀ n,1 < |n| → r n≤D*((n:ℝ)^2)⁻¹) :
    Summable r ∧ (∑' n,r n)≤3*cap+4*D := by
  let b : ℤ → ℝ := fun n =>
    (if n = -1 then cap else 0)+(if n=0 then cap else 0)+
      (if n=1 then cap else 0)+D*((n:ℝ)^2)⁻¹
  have hb : Summable b := (((hasSum_ite_eq (-1 : ℤ) cap).summable.add
    (hasSum_ite_eq (0 : ℤ) cap).summable).add (hasSum_ite_eq (1 : ℤ) cap).summable).add
      (AsymptoticFoldSum.int_inverse_square_summable.mul_left D)
  have hle (n : ℤ) : r n≤b n := by
    by_cases hn : |n|≤1
    · have hc : n = -1 ∨ n=0 ∨ n=1 := by
        have hh := abs_le.mp hn
        omega
      rcases hc with rfl | rfl | rfl <;> norm_num [b] <;>
        linarith [hcap (-1),hcap 0,hcap 1]
    · have h₁ : n≠-1 := by rintro rfl; norm_num at hn
      have h₀ : n≠0 := by rintro rfl; norm_num at hn
      have h₂ : n≠1 := by rintro rfl; norm_num at hn
      simpa [b,h₁,h₀,h₂] using htail n (by omega)
  have hrs := Summable.of_nonneg_of_le hr hle hb
  refine ⟨hrs,(hrs.tsum_le_tsum hle hb).trans ?_⟩
  have hbs : (∑' n,b n)=3*cap+D*(∑' n : ℤ,((n:ℝ)^2)⁻¹) := by
    dsimp [b]
    rw [Summable.tsum_add (((hasSum_ite_eq (-1 : ℤ) cap).summable.add
      (hasSum_ite_eq (0 : ℤ) cap).summable).add (hasSum_ite_eq (1 : ℤ) cap).summable)
      (AsymptoticFoldSum.int_inverse_square_summable.mul_left D)]
    rw [Summable.tsum_add ((hasSum_ite_eq (-1 : ℤ) cap).summable.add
      (hasSum_ite_eq (0 : ℤ) cap).summable) (hasSum_ite_eq (1 : ℤ) cap).summable]
    rw [Summable.tsum_add (hasSum_ite_eq (-1 : ℤ) cap).summable
      (hasSum_ite_eq (0 : ℤ) cap).summable]
    simp only [tsum_ite_eq,tsum_mul_left]
    ring
  rw [hbs]
  have hh := mul_le_mul_of_nonneg_left AsymptoticFoldSum.int_inverse_square_sum hD
  linarith

noncomputable def majorant (cap D : ℝ) (n : ℤ) : ℝ :=
  min cap (if |n|≤1 then cap else D*((n:ℝ)^2)⁻¹)

theorem majorant_nonneg {cap D : ℝ} (hcap : 0≤cap) (hD : 0≤D) (n : ℤ) :
    0≤majorant cap D n := by
  unfold majorant
  split_ifs <;> positivity

theorem majorant_le_cap (cap D : ℝ) (n : ℤ) : majorant cap D n≤cap := min_le_left _ _

theorem le_majorant {cap D : ℝ} (r : ℤ → ℝ) (hcap : ∀ n,r n≤cap)
    (htail : ∀ n,1 < |n| → r n≤D*((n:ℝ)^2)⁻¹) (n : ℤ) : r n≤majorant cap D n := by
  apply le_min (hcap n)
  split_ifs with hn
  · exact hcap n
  · exact htail n (by omega)

theorem majorant_summable_bound {cap D : ℝ} (hcap : 0≤cap) (hD : 0≤D) :
    Summable (majorant cap D) ∧ (∑' n,majorant cap D n)≤3*cap+4*D :=
  sum_bound _ hD (majorant_nonneg hcap hD) (majorant_le_cap _ _) (by
    intro n hn
    exact (min_le_right _ _).trans_eq (by simp [hn.not_ge]))

theorem power_summable_bound {cap D : ℝ} (hcap : 0≤cap) (hD : 0≤D)
    {t : ℕ} (ht : 1≤t) :
    Summable (fun n => majorant cap D n^t) ∧
      (∑' n,majorant cap D n^t)≤cap^(t-1)*(3*cap+4*D) := by
  have hs := majorant_summable_bound hcap hD
  have hle (n : ℤ) : majorant cap D n^t≤cap^(t-1)*majorant cap D n := by
    calc
      majorant cap D n^t=majorant cap D n^(t-1)*majorant cap D n := by
        rw [← pow_succ]; congr 1; omega
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (majorant_nonneg hcap hD n) (majorant_le_cap _ _ _) _)
        (majorant_nonneg hcap hD n)
  have hm := hs.1.mul_left (cap^(t-1))
  have hr := Summable.of_nonneg_of_le (fun n => pow_nonneg (majorant_nonneg hcap hD n) t) hle hm
  refine ⟨hr,(hr.tsum_le_tsum hle hm).trans ?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hs.2 (pow_nonneg hcap _)

/-- The terminal-height factor has a 1/|n| bound before squaring.
Unlike the ascending ratio estimate, this is uniform over all v>0. -/
theorem terminal_ratio_tail {a L ε v : ℝ} (ha : |a|≤1) (hL : 0<L)
    (hε : 0<ε) (hv : 0<v) {n : ℤ} (hn : 1 < |n|) :
    v/(ε*L*(((n:ℝ)+a)^2+v^2))≤(ε*L*|(n:ℝ)|)⁻¹ := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by rintro rfl; norm_num at hn)
  have hs := separation ha hn
  have hd : |(n:ℝ)| *v≤((n:ℝ)+a)^2+v^2 := by
    nlinarith [sq_abs ((n:ℝ)+a),sq_nonneg (|(n:ℝ)+a| -v)]
  rw [← one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left hd (mul_pos hε hL).le
  nlinarith

#print axioms inverse_ratio_tail
#print axioms power_summable_bound
#print axioms terminal_ratio_tail

end AsymptoticFoldMajorant
