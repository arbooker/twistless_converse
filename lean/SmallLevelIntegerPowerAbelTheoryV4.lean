module

public import Mathlib.Tactic

/-! Consolidated chapter: SmallLevelIntegerPowerAbel. Original declarations and local scopes are retained. -/

/-! ## SmallLevelIntegerPowerAbelV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelIntegerPowerAbel

abbrev Datum := ℕ × ℤ

/-- Descending positive integer bases, checked in one linear scan. -/
def boundsGood (upper : ℕ) : List Datum→Bool
  | [] => true
  | (b,_c)::xs => decide (0<b ∧ b≤upper) && boundsGood b xs

def total (M : ℕ) (acc : ℤ) : List Datum→ℤ
  | [] => acc
  | (b,c)::xs => total M (acc+c*(b:ℤ)^M) xs

/-- Nonnegative partial sums after weighting at the initial exponent. -/
def prefixesGood (M : ℕ) (acc : ℤ) : List Datum→Bool
  | [] => true
  | (b,c)::xs => decide (0≤acc+c*(b:ℤ)^M) && prefixesGood M (acc+c*(b:ℤ)^M) xs

def powerSum (n : ℕ) : List Datum→ℝ
  | [] => 0
  | (b,c)::xs => (c:ℝ)*(b:ℝ)^n+powerSum n xs

/-- Discrete Abel summation with a carried partial sum. Its strictness
requires only the final total to be positive; earlier sums may vanish. -/
theorem positive_aux (M r : ℕ) (xs : List Datum) (upper : ℕ) (acc : ℤ)
    (hu : 0<upper) (ha : 0≤acc) (hb : boundsGood upper xs=true)
    (hp : prefixesGood M acc xs=true) (ht : 0<total M acc xs) :
    0<(acc:ℝ)*(upper:ℝ)^r+powerSum (M+r) xs := by
  induction xs generalizing upper acc with
  | nil =>
    simp only [total] at ht
    simp only [powerSum,add_zero]
    exact mul_pos (by exact_mod_cast ht) (pow_pos (by exact_mod_cast hu) r)
  | cons d xs ih =>
    rcases d with ⟨b,c⟩
    simp only [boundsGood,Bool.and_eq_true,decide_eq_true_eq] at hb
    simp only [prefixesGood,Bool.and_eq_true,decide_eq_true_eq] at hp
    simp only [total] at ht
    have hh:=ih b (acc+c*(b:ℤ)^M) hb.1.1 hp.1 hb.2 hp.2 ht
    have hm : (b:ℝ)^r≤(upper:ℝ)^r := by
      gcongr
      exact_mod_cast hb.1.2
    have han : (0:ℝ)≤acc := by exact_mod_cast ha
    have hn:=mul_nonneg han (sub_nonneg.mpr hm)
    have he : (acc:ℝ)*(upper:ℝ)^r+powerSum (M+r) ((b,c)::xs)=
        (acc:ℝ)*((upper:ℝ)^r-(b:ℝ)^r)+
        ((acc+c*(b:ℤ)^M:ℤ):ℝ)*(b:ℝ)^r+powerSum (M+r) xs := by
      simp only [powerSum,pow_add,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_natCast]
      ring
    rw [he]
    linarith

/-- Exact integer checks at one threshold prove nonvanishing at every
larger integer exponent, without numerical estimates of logarithms. -/
theorem positive_from_threshold (M n upper : ℕ) (xs : List Datum) (hn : M≤n)
    (hu : 0<upper) (hb : boundsGood upper xs=true)
    (hp : prefixesGood M 0 xs=true) (ht : 0<total M 0 xs) :
    0<powerSum n xs := by
  have hh:=positive_aux M (n-M) xs upper 0 hu (by norm_num) hb hp ht
  have he : M+(n-M)=n := by omega
  simpa only [Int.cast_zero,zero_mul,zero_add,he] using hh

#print axioms positive_from_threshold
end SmallLevelIntegerPowerAbel
end
end

/-! ## SmallLevelIntegerPowerAbelEvaluationV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelIntegerPowerAbel

theorem total_add (M : ℕ) (xs : List Datum) (acc : ℤ) :
    total M acc xs=acc+total M 0 xs := by
  induction xs generalizing acc with
  | nil => simp [total]
  | cons d xs ih =>
    rcases d with ⟨b,c⟩
    simp only [total]
    rw [ih (acc+c*(b:ℤ)^M),ih (0+c*(b:ℤ)^M)]
    ring

theorem powerSum_eq_total (n : ℕ) (xs : List Datum) :
    powerSum n xs=(total n 0 xs:ℝ) := by
  induction xs with
  | nil => simp [powerSum,total]
  | cons d xs ih =>
    rcases d with ⟨b,c⟩
    change (c:ℝ)*(b:ℝ)^n+powerSum n xs=(total n (0+c*(b:ℤ)^n) xs:ℝ)
    rw [total_add,ih]
    push_cast
    ring

theorem powerSum_ne_zero_of_total (n : ℕ) (xs : List Datum)
    (h : total n 0 xs≠0) : powerSum n xs≠0 := by
  rw [powerSum_eq_total]
  exact_mod_cast h

#print axioms powerSum_eq_total
end SmallLevelIntegerPowerAbel
end
end
