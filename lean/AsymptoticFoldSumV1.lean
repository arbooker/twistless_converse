module

public import AsymptoticTraceCutoffV1
public import Mathlib.Algebra.Order.Round
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFoldSum

open scoped BigOperators

/-- An elementary bound, sufficient for controlling all integer folds. -/
theorem nat_inverse_square_sum : (∑' n : ℕ, ((n:ℝ)^2)⁻¹) ≤ 2 := by
  have h := AsymptoticTraceCutoff.summable_and_tsum_bound
    (fun n : ℕ => ((n:ℝ)^2)⁻¹) (k:=1) (M:=1) (δ:=1) (C:=1)
    (by omega) (by norm_num) (by norm_num) (fun _ => by positivity)
    (by
      intro n hn hn'
      have : n=1 := by omega
      simp [this])
    (by intro n _; simp)
  norm_num at h ⊢
  exact h

theorem int_inverse_square_summable : Summable (fun n : ℤ => ((n:ℝ)^2)⁻¹) := by
  simpa only [one_div] using (Real.summable_one_div_int_pow (p:=2)).mpr (by omega)

theorem int_inverse_square_sum : (∑' n : ℤ, ((n:ℝ)^2)⁻¹) ≤ 4 := by
  have h := int_inverse_square_summable.hasSum.nat_add_neg
  simp only [Int.cast_natCast, Int.cast_neg, neg_sq, Int.cast_zero, zero_pow (by omega : 2≠0),
    inv_zero, add_zero] at h
  have hn : Summable (fun n : ℕ => ((n:ℝ)^2)⁻¹) := by
    simpa only [one_div] using (Real.summable_one_div_nat_pow (p:=2)).mpr (by omega)
  have he := h.tsum_eq
  rw [hn.tsum_add hn] at he
  linarith [nat_inverse_square_sum]

/-- All noncentral translates are at least half their integer distance
from the centre, uniformly for a displacement of at most one half. -/
theorem translate_separation {a : ℝ} (ha : |a|≤1/2) {n : ℤ} (hn : n≠0) :
    |(n:ℝ)|/2 ≤ |(n:ℝ)+a| := by
  have hn' : (1:ℝ)≤|(n:ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hh := abs_add_le ((n:ℝ)+a) (-a)
  simp only [add_neg_cancel_right, abs_neg] at hh
  linarith

/-- The inverse-square majorant for every noncentral inverse branch. -/
theorem inverse_branch_le {a c v : ℝ} (ha : |a|≤1/2) (hc : c≠0)
    {n : ℤ} (hn : n≠0) :
    (c^2*(((n:ℝ)+a)^2+v^2))⁻¹ ≤ (4/c^2)*((n:ℝ)^2)⁻¹ := by
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn
  have hsep := translate_separation ha hn
  have hs : (n:ℝ)^2/4≤((n:ℝ)+a)^2+v^2 := by
    have hh := mul_self_le_mul_self (by positivity : 0≤|(n:ℝ)|/2) hsep
    nlinarith [sq_abs (n:ℝ),sq_abs ((n:ℝ)+a),sq_nonneg v]
  have hc' : 0<c^2 := sq_pos_of_ne_zero hc
  have hn2 : 0<(n:ℝ)^2 := sq_pos_of_ne_zero hn'
  calc
    (c^2*(((n:ℝ)+a)^2+v^2))⁻¹ ≤ (c^2*((n:ℝ)^2/4))⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact mul_le_mul_of_nonneg_left hs hc'.le
    _ = _ := by field_simp

/-- Summing the central cap and the separated inverse-square tails gives
the uniform column bound in the reconstruction lemma. -/
theorem centered_sum_bound (r : ℤ → ℝ) {a c v cap : ℝ}
    (ha : |a|≤1/2) (hc : c≠0)
    (hr : ∀ n, 0≤r n) (hzero : r 0≤cap)
    (hbranch : ∀ n, n≠0 → r n≤(c^2*(((n:ℝ)+a)^2+v^2))⁻¹) :
    Summable r ∧ (∑' n,r n)≤cap+16/c^2 := by
  let b : ℤ → ℝ := fun n => (if n=0 then cap else 0)+(4/c^2)*((n:ℝ)^2)⁻¹
  have hb : Summable b := (hasSum_ite_eq 0 cap).summable.add
    (int_inverse_square_summable.mul_left (4/c^2))
  have hle : ∀ n,r n≤b n := by
    intro n
    by_cases hn : n=0
    · simpa [b,hn] using hzero
    · simpa [b,hn] using (hbranch n hn).trans (inverse_branch_le ha hc hn)
  have hrs := Summable.of_nonneg_of_le hr hle hb
  refine ⟨hrs,(hrs.tsum_le_tsum hle hb).trans ?_⟩
  calc
    (∑' n,b n) = cap+(4/c^2)*(∑' n : ℤ,((n:ℝ)^2)⁻¹) := by
      rw [Summable.tsum_add (hasSum_ite_eq 0 cap).summable
        (int_inverse_square_summable.mul_left (4/c^2))]
      simp [tsum_mul_left]
    _ ≤ cap+(4/c^2)*4 := by gcongr; exact int_inverse_square_sum
    _ = _ := by ring

/-- Nearest-integer translation removes any restriction on the real part
of the target of an inverse branch. -/
theorem sum_bound (r : ℤ → ℝ) {a c v cap : ℝ} (hc : c≠0)
    (hr : ∀ n,0≤r n) (hcap : ∀ n,r n≤cap)
    (hbranch : ∀ n,r n≤(c^2*(((n:ℝ)+a)^2+v^2))⁻¹) :
    Summable r ∧ (∑' n,r n)≤cap+16/c^2 := by
  let e : ℤ ≃ ℤ := Equiv.addRight (-round a)
  have h := centered_sum_bound (r ∘ e) (a:=a-round a) (v:=v)
    (abs_sub_round a) hc (fun n => hr (e n)) (hcap (e 0)) (by
      intro n _
      have he : ((e n:ℤ):ℝ)+a=(n:ℝ)+(a-round a) := by
        simp only [e,Equiv.coe_addRight,Int.cast_add,Int.cast_neg]
        ring
      simpa only [Function.comp_apply,he] using hbranch (e n))
  exact ⟨e.summable_iff.mp h.1, by simpa only [Function.comp_def,e.tsum_eq] using h.2⟩

/-- The ascending-height cap supplies the extra geometric decay at every
integer weight, with all integer folds still included. -/
theorem power_sum_bound (r : ℤ → ℝ) {a c v cap : ℝ} (hc : c≠0)
    (hr : ∀ n,0≤r n) (hcap : ∀ n,r n≤cap)
    (hbranch : ∀ n,r n≤(c^2*(((n:ℝ)+a)^2+v^2))⁻¹)
    {t : ℕ} (ht : 1≤t) :
    Summable (fun n => r n^t) ∧
      (∑' n,r n^t)≤cap^(t-1)*(cap+16/c^2) := by
  have hh := sum_bound r hc hr hcap hbranch
  have hcap0 : 0≤cap := (hr 0).trans (hcap 0)
  have hle : ∀ n,r n^t≤cap^(t-1)*r n := by
    intro n
    calc
      r n^t = r n^(t-1)*r n := by rw [← pow_succ]; congr 1; omega
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hr n) (hcap n) _) (hr n)
  have hb := hh.1.mul_left (cap^(t-1))
  have hp := Summable.of_nonneg_of_le (fun n => pow_nonneg (hr n) t) hle hb
  refine ⟨hp,(hp.tsum_le_tsum hle hb).trans ?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hh.2 (pow_nonneg hcap0 _)

/-- The actual inverse-branch height ratio, retaining precisely the
ascending branches at the prescribed cap. -/
noncomputable def ascendingRatio (a c v cap : ℝ) (n : ℤ) : ℝ :=
  let r := (c^2*(((n:ℝ)+a)^2+v^2))⁻¹
  if r≤cap then r else 0

theorem ascendingRatio_bounds (a c v cap : ℝ) (hcap : 0≤cap) (n : ℤ) :
    0≤ascendingRatio a c v cap n ∧ ascendingRatio a c v cap n≤cap ∧
      ascendingRatio a c v cap n≤(c^2*(((n:ℝ)+a)^2+v^2))⁻¹ := by
  dsimp [ascendingRatio]
  split_ifs with h
  · exact ⟨by positivity,h,le_rfl⟩
  · exact ⟨le_rfl,hcap,by positivity⟩

theorem ascending_sum_bound {a c v cap : ℝ} (hc : c≠0) (hcap : 0≤cap) :
    Summable (ascendingRatio a c v cap) ∧
      (∑' n,ascendingRatio a c v cap n)≤cap+16/c^2 :=
  sum_bound _ hc (fun n => (ascendingRatio_bounds a c v cap hcap n).1)
    (fun n => (ascendingRatio_bounds a c v cap hcap n).2.1)
    (fun n => (ascendingRatio_bounds a c v cap hcap n).2.2)

theorem ascending_power_sum_bound {a c v cap : ℝ} (hc : c≠0) (hcap : 0≤cap)
    {t : ℕ} (ht : 1≤t) :
    Summable (fun n => ascendingRatio a c v cap n^t) ∧
      (∑' n,ascendingRatio a c v cap n^t)≤cap^(t-1)*(cap+16/c^2) :=
  power_sum_bound _ hc (fun n => (ascendingRatio_bounds a c v cap hcap n).1)
    (fun n => (ascendingRatio_bounds a c v cap hcap n).2.1)
    (fun n => (ascendingRatio_bounds a c v cap hcap n).2.2) ht

#print axioms ascending_power_sum_bound
#print axioms centered_sum_bound
#print axioms sum_bound
#print axioms power_sum_bound

end AsymptoticFoldSum
