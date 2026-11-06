module

public import AsymptoticFoldTruncationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open AsymptoticFoldMajorant

/-- The omitted inverse-square tail outside a symmetric integer cutoff. -/
def integerSquareTail (J : ℕ) (n : ℤ) : ℝ :=
  if |n| ≤ J then 0 else ((n : ℝ) ^ 2)⁻¹

theorem integerSquareTail_nonneg (J : ℕ) (n : ℤ) : 0 ≤ integerSquareTail J n := by
  unfold integerSquareTail
  split_ifs <;> positivity

theorem integerSquareTail_sum (J : ℕ) (hJ : 0 < J) :
    Summable (integerSquareTail J) ∧ (∑' n, integerSquareTail J n) ≤ 2 / (J : ℝ) := by
  let f : ℕ → ℝ := fun n => if n ≤ J then 0 else ((n : ℝ) ^ 2)⁻¹
  have hn := AsymptoticTraceCutoff.summable_and_tsum_bound f (k := 1) hJ
    (δ := 0) (C := 1) (by norm_num) (by simp [f])
    (fun n => by dsimp [f]; split_ifs <;> positivity)
    (fun n _ hn => by simp [f, hn]) (fun n hn => by simp [f, hn.not_ge])
  have hs : Summable (integerSquareTail J) := by
    apply Summable.of_nonneg_of_le (integerSquareTail_nonneg J) _ AsymptoticFoldSum.int_inverse_square_summable
    intro n
    unfold integerSquareTail
    split_ifs
    · positivity
    · exact le_rfl
  have he := hs.hasSum.nat_add_neg
  have hp (n : ℕ) : integerSquareTail J (n : ℤ) = f n := by
    simp [integerSquareTail, f]
  have hm (n : ℕ) : integerSquareTail J (-(n : ℤ)) = f n := by
    simp [integerSquareTail, f]
  have hz : integerSquareTail J 0 = 0 := by simp [integerSquareTail]
  simp only [hp, hm, hz, add_zero] at he
  have hh := he.tsum_eq
  rw [hn.1.tsum_add hn.1] at hh
  refine ⟨hs, ?_⟩
  simp only [Nat.cast_one, one_pow, mul_zero, zero_add, mul_one] at hn
  rw [← hh]
  exact (add_le_add hn.2 hn.2).trans_eq (by ring)

/-- An explicit tail estimate for the actual fold majorant. -/
theorem fold_majorant_tail_sum {cap D : ℝ} (hcap : 0 ≤ cap) (hD : 0 ≤ D)
    (J : ℕ) (hJ : 0 < J) :
    Summable (fun n : ℤ => if |n| ≤ J then 0 else majorant cap D n) ∧
      (∑' n : ℤ, if |n| ≤ J then 0 else majorant cap D n) ≤ 2 * D / (J : ℝ) := by
  have hb := integerSquareTail_sum J hJ
  have hle (n : ℤ) : (if |n| ≤ J then 0 else majorant cap D n) ≤ D * integerSquareTail J n := by
    by_cases hn : |n| ≤ J
    · simp only [hn, ite_true, integerSquareTail, mul_zero, le_refl]
    · have hlarge : ¬ |n| ≤ 1 := by
        have hJ' : (1 : ℤ) ≤ J := by exact_mod_cast hJ
        omega
      simp only [hn, ite_false, integerSquareTail]
      exact (min_le_right _ _).trans_eq (by simp only [ite_eq_right hlarge])
  have hnonneg (n : ℤ) : 0 ≤ (if |n| ≤ J then 0 else majorant cap D n) := by
    split_ifs
    · exact le_rfl
    · exact majorant_nonneg hcap hD n
  have hs := Summable.of_nonneg_of_le hnonneg hle (hb.1.mul_left D)
  refine ⟨hs, (hs.tsum_le_tsum hle (hb.1.mul_left D)).trans ?_⟩
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left hb.2 hD).trans_eq (by ring)

/-- The same bound for powers, retaining the actual contraction cap. -/
theorem fold_majorant_power_tail_sum {cap D : ℝ} (hcap : 0 ≤ cap) (hD : 0 ≤ D)
    (J : ℕ) (hJ : 0 < J) {t : ℕ} (ht : 1 ≤ t) :
    Summable (fun n : ℤ => if |n| ≤ J then 0 else majorant cap D n ^ t) ∧
      (∑' n : ℤ, if |n| ≤ J then 0 else majorant cap D n ^ t) ≤
        cap ^ (t - 1) * (2 * D / (J : ℝ)) := by
  have hb := fold_majorant_tail_sum hcap hD J hJ
  have hle (n : ℤ) : (if |n| ≤ J then 0 else majorant cap D n ^ t) ≤
      cap ^ (t - 1) * (if |n| ≤ J then 0 else majorant cap D n) := by
    split_ifs
    · simp
    · have he : t = (t - 1) + 1 := by omega
      conv_lhs => rw [he, pow_succ]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (majorant_nonneg hcap hD n) (majorant_le_cap cap D n) _)
        (majorant_nonneg hcap hD n)
  have hs := Summable.of_nonneg_of_le (fun n => by
    split_ifs
    · exact le_rfl
    · exact pow_nonneg (majorant_nonneg hcap hD n) t) hle (hb.1.mul_left (cap ^ (t - 1)))
  refine ⟨hs, (hs.tsum_le_tsum hle (hb.1.mul_left (cap ^ (t - 1)))).trans ?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hb.2 (pow_nonneg hcap _)

/-- A norm-majorized series has an explicit symmetric truncation error. -/
theorem norm_tsum_sub_symmetric_sum_le {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {f : ℤ → E} {u : ℤ → ℝ} (hu : Summable u)
    (hfu : ∀ n, ‖f n‖ ≤ u n) (J : ℕ) :
    ‖(∑' n, f n) - ∑ n ∈ Finset.Icc (-(J : ℤ)) J, f n‖ ≤
      ∑' n : ℤ, if |n| ≤ J then 0 else u n := by
  classical
  let I : Finset ℤ := Finset.Icc (-(J : ℤ)) J
  have hn : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hfu hu
  change ‖(∑' n, f n) - ∑ n ∈ I, f n‖ ≤ _
  rw [← hn.of_norm.sum_add_tsum_subtype_compl I, add_sub_cancel_left]
  apply (norm_tsum_le_tsum_norm (hn.subtype _)).trans
  apply ((hn.subtype _).tsum_le_tsum (fun n : {x // x ∉ I} => hfu n.val) (hu.subtype _)).trans_eq
  change (∑' n : ↥((I : Set ℤ)ᶜ), u n) = _
  rw [tsum_subtype ((I : Set ℤ)ᶜ) u]
  apply tsum_congr
  intro n
  simp only [Set.indicator, Set.mem_compl_iff, Finset.mem_coe, I, Finset.mem_Icc,
    ← abs_le]
  split_ifs <;> rfl

/-- The actual operator tail estimate is uniform in every parameter entering
only through the termwise fold majorant. -/
theorem fold_operator_tail_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℤ → E} {cap D : ℝ} (hcap : 0 ≤ cap) (hD : 0 ≤ D)
    (hterm : ∀ n, ‖f n‖ ≤ majorant cap D n) (J : ℕ) (hJ : 0 < J) :
    ‖(∑' n, f n) - ∑ n ∈ Finset.Icc (-(J : ℤ)) J, f n‖ ≤
      2 * D / (J : ℝ) :=
  (norm_tsum_sub_symmetric_sum_le (majorant_summable_bound hcap hD).1 hterm J).trans
    (fold_majorant_tail_sum hcap hD J hJ).2

theorem fold_operator_power_tail_bound {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {f : ℤ → E} {cap D : ℝ} (hcap : 0 ≤ cap) (hD : 0 ≤ D)
    {t : ℕ} (ht : 1 ≤ t) (hterm : ∀ n, ‖f n‖ ≤ majorant cap D n ^ t)
    (J : ℕ) (hJ : 0 < J) :
    ‖(∑' n, f n) - ∑ n ∈ Finset.Icc (-(J : ℤ)) J, f n‖ ≤
      cap ^ (t - 1) * (2 * D / (J : ℝ)) :=
  (norm_tsum_sub_symmetric_sum_le (power_summable_bound hcap hD ht).1 hterm J).trans
    (fold_majorant_power_tail_sum hcap hD J hJ ht).2

open MeasureTheory UpperHalfPlane in
/-- Explicit symmetric truncation of the actual physical
low fold operator, uniform in the holomorphic weight. -/
theorem physical_low_fold_truncation_bound {L : ℝ} (hL : 0 < L) (b d : ℝ)
    {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r) {cap : ℝ} (hcap : 0 ≤ cap)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) 
    (hstrip : r ⊆ AsymptoticMassTransport.strip) {t : ℕ} (ht : 1 ≤ t)
    (m : ℕ) (J : ℕ) (hJ : 0 < J) :
    ‖AsymptoticFoldedLow.operator hL b d hs hr hcap hd0 hd1 hstrip t m -
      ∑ n ∈ Finset.Icc (-(J : ℤ)) J, AsymptoticFoldedLow.term hL b d hs hr hcap hd0 hd1 hstrip t m n‖ ≤
        cap ^ (t - 1) * (2 * (4 / L) / (J : ℝ)) := by
  exact fold_operator_power_tail_bound hcap (by positivity) ht
    (fun n => AsymptoticFoldedLow.term_norm_le hL b d hs hr hcap hd0 hd1 hstrip t m n) J hJ

#print axioms physical_low_fold_truncation_bound

open MeasureTheory UpperHalfPlane in
/-- Explicit symmetric truncation of the actual physical
terminal fold operator, uniform in the holomorphic weight. -/
theorem physical_terminal_fold_truncation_bound {L : ℝ} (hL : 0 < L) (b d : ℝ)
    {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r) {ε : ℝ} (hε : 0 < ε)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hsource : s ⊆ {z | z.im ≤ ε})
    (hstrip : r ⊆ AsymptoticMassTransport.strip) {t : ℕ} (ht : 2 ≤ t)
    (m : ℕ) (J : ℕ) (hJ : 0 < J) :
    ‖AsymptoticFoldedTerminal.operator hL b d hs hr hε hd0 hd1 hsource hstrip ht m -
      ∑ n ∈ Finset.Icc (-(J : ℤ)) J, AsymptoticFoldedTerminal.term hL b d hs hr hε hd0 hd1 hsource hstrip ht m n‖ ≤
        2 * ((ε * L) ^ 2)⁻¹ / (J : ℝ) := by
  exact fold_operator_tail_bound zero_le_one (by positivity)
    (fun n => AsymptoticFoldedTerminal.term_norm_le hL b d hs hr hε hd0 hd1 hsource hstrip ht m n) J hJ

#print axioms physical_terminal_fold_truncation_bound

open MeasureTheory UpperHalfPlane in
/-- Explicit symmetric truncation of the actual regular
low fold operator, uniform in the root. -/
theorem regular_low_fold_truncation_bound {L : ℚ} (hL : 0 < L) (b d : ℚ)
    (s r : Set ℍ) {cap : ℝ} (hcap : 0 ≤ cap)
    (hd0 : 0 ≤ (d : ℝ)) (hd1 : (d : ℝ) ≤ 1) 
    (hstrip : r ⊆ AsymptoticMassTransport.strip) {t : ℕ} (ht : 1 ≤ t)
    (z : ℍ) (J : ℕ) (hJ : 0 < J) :
    ‖AsymptoticRegularFoldedLow.operator hL b d s r hcap hd0 hd1 hstrip t z -
      ∑ n ∈ Finset.Icc (-(J : ℤ)) J, AsymptoticRegularFoldedLow.term hL b d s r hcap hd0 hd1 hstrip t n z‖ ≤
        cap ^ (t - 1) * (2 * (4 / (L : ℝ)) / (J : ℝ)) := by
  exact fold_operator_power_tail_bound hcap (by positivity) ht
    (fun n => AsymptoticRegularFoldedLow.term_norm_le hL b d s r hcap hd0 hd1 hstrip t n z) J hJ

#print axioms regular_low_fold_truncation_bound

open MeasureTheory UpperHalfPlane in
/-- Explicit symmetric truncation of the actual regular
terminal fold operator, uniform in the root. -/
theorem regular_terminal_fold_truncation_bound {L : ℚ} (hL : 0 < L) (b d : ℚ)
    (s r : Set ℍ) {ε : ℝ} (hε : 0 < ε)
    (hd0 : 0 ≤ (d : ℝ)) (hd1 : (d : ℝ) ≤ 1) (hsource : s ⊆ {z | z.im ≤ ε})
    (hstrip : r ⊆ AsymptoticMassTransport.strip) {t : ℕ} (ht : 2 ≤ t)
    (z : ℍ) (J : ℕ) (hJ : 0 < J) :
    ‖AsymptoticRegularFoldedTerminal.operator hL b d s r hε hd0 hd1 hsource hstrip ht z -
      ∑ n ∈ Finset.Icc (-(J : ℤ)) J, AsymptoticRegularFoldedTerminal.term hL b d s r hε hd0 hd1 hsource hstrip ht n z‖ ≤
        2 * ((ε * (L : ℝ)) ^ 2)⁻¹ / (J : ℝ) := by
  exact fold_operator_tail_bound zero_le_one (by positivity)
    (fun n => AsymptoticRegularFoldedTerminal.term_norm_le hL b d s r hε hd0 hd1 hsource hstrip ht n z) J hJ

#print axioms regular_terminal_fold_truncation_bound

#print axioms fold_operator_tail_bound
#print axioms fold_operator_power_tail_bound

#print axioms integerSquareTail_sum
#print axioms fold_majorant_tail_sum
#print axioms fold_majorant_power_tail_sum

end QuantitativeHolomorphic
