module

public import SpanningSpectralTracesV1

@[expose] public section

namespace SpanningCriterionCharacter

open SpanningTraceAlgebra

variable {K : Type*} [Field K]

/-- A character supported on the subgroup of multiples of `m`. -/
noncomputable def supported (m : ℕ) (ζ : K) (n : ℤ) : K :=
  if (m : ℤ) ∣ n then ζ^(n/(m : ℤ)) else 0

theorem supported_shift {m : ℕ} (hm : 0 < m) {ζ : K} (hζ : ζ ≠ 0)
    (n b : ℤ) : supported m ζ (n + m*b) = supported m ζ n * ζ^b := by
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hd : (m : ℤ) ∣ n + m*b ↔ (m : ℤ) ∣ n :=
    by
      constructor
      · intro hh; exact (dvd_sub hh (dvd_mul_right (m : ℤ) b)) |> (by simpa using ·)
      · intro hh; exact dvd_add hh (dvd_mul_right _ _)
  unfold supported
  simp only [hd]
  split_ifs
  · rw [Int.add_mul_ediv_left _ _ hm0, zpow_add₀ hζ]
  · rw [zero_mul]

theorem supported_cyclic {m s : ℕ} (hm : 0 < m) (hs : 0 < s)
    {ζ : K} (hζ : IsPrimitiveRoot ζ s) : Cyclic (m*s) (supported m ζ) := by
  intro n
  have hh := supported_shift hm (hζ.ne_zero hs.ne') n (s : ℤ)
  simpa only [Nat.cast_mul, zpow_natCast, hζ.pow_eq_one, mul_one] using hh

theorem supported_trace_zero {m s p : ℕ} (hm : 0 < m) (hs : 0 < s)
    {ζ : K} (hζ : IsPrimitiveRoot ζ s) (hp : 1 < p) (hps : p ∣ s) :
    trace p ((m*s)/p) (supported m ζ) = 0 := by
  have he : (m*s)/p = m*(s/p) := Nat.mul_div_assoc m hps
  have hfactor : p*((m*s)/p) = m*s :=
    Nat.mul_div_cancel' (hps.trans (dvd_mul_left s m))
  have hcyc := trace_cyclic (show Cyclic (p*((m*s)/p)) (supported m ζ) by
    rw [hfactor]; exact supported_cyclic hm hs hζ)
  have hsp : 0 < s/p := Nat.div_pos (Nat.le_of_dvd hs hps) (by omega)
  have hsplt : s/p < s := Nat.div_lt_self hs hp
  have hne := hζ.pow_ne_one_of_pos_of_lt hsp.ne' hsplt
  funext u
  have hshift : trace p ((m*s)/p) (supported m ζ) (u + ((m*s)/p : ℕ)) =
      trace p ((m*s)/p) (supported m ζ) u * ζ^(s/p) := by
    change (∑ a ∈ Finset.range p, supported m ζ ((u + ((m*s)/p : ℕ)) + a*((m*s)/p : ℕ))) = _
    rw [trace, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    have hh := supported_shift hm (hζ.ne_zero hs.ne')
      (u + a*((m*s)/p : ℕ)) ((s/p : ℕ) : ℤ)
    rw [zpow_natCast] at hh
    convert hh using 1
    rw [he]
    push_cast
    ring
  have hh : trace p ((m*s)/p) (supported m ζ) u * (ζ^(s/p)-1) = 0 := by
    rw [mul_sub, mul_one, ←hshift, hcyc, sub_self]
  exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hne)

noncomputable def obstruction (m : ℕ) (ζ : K) : ℤ → K :=
  fun n => supported m ζ n - supported m ζ⁻¹ n

theorem obstruction_zero (m : ℕ) (ζ : K) : obstruction m ζ 0 = 0 := by
  simp [obstruction, supported]

theorem obstruction_off_support {m : ℕ} {ζ : K} {n : ℤ}
    (hn : ¬ (m : ℤ) ∣ n) : obstruction m ζ n = 0 := by
  simp [obstruction, supported, hn]

theorem obstruction_nonzero {m s : ℕ} (hm : 0 < m) (hs : 2 < s)
    {ζ : K} (hζ : IsPrimitiveRoot ζ s) : obstruction m ζ ≠ 0 := by
  intro hz
  have hh := congrFun hz (m : ℤ)
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [obstruction, supported, dvd_refl, ite_true, Int.ediv_self hm0,
    zpow_one, Pi.zero_apply, sub_eq_zero] at hh
  have hh' : ζ^2 = 1 := by
    calc ζ^2 = ζ * ζ := pow_two ζ
         _ = ζ⁻¹ * ζ := congrArg (fun x => x * ζ) hh
         _ = 1 := inv_mul_cancel₀ (hζ.ne_zero (by omega))
  exact hζ.pow_ne_one_of_pos_of_lt (by omega : (2 : ℕ) ≠ 0) hs hh'

theorem obstruction_cyclic {m s : ℕ} (hm : 0 < m) (hs : 0 < s)
    {ζ : K} (hζ : IsPrimitiveRoot ζ s) : Cyclic (m*s) (obstruction m ζ) := by
  intro n
  rw [obstruction, supported_cyclic hm hs hζ n, supported_cyclic hm hs hζ.inv n]
  rfl

theorem obstruction_trace_zero {m s p : ℕ} (hm : 0 < m) (hs : 0 < s)
    {ζ : K} (hζ : IsPrimitiveRoot ζ s) (hp : 1 < p) (hps : p ∣ s) :
    trace p ((m*s)/p) (obstruction m ζ) = 0 := by
  funext u
  change (∑ a ∈ Finset.range p, (supported m ζ (u+a*((m*s)/p : ℕ)) -
    supported m ζ⁻¹ (u+a*((m*s)/p : ℕ)))) = 0
  rw [Finset.sum_sub_distrib]
  change trace p ((m*s)/p) (supported m ζ) u -
    trace p ((m*s)/p) (supported m ζ⁻¹) u = 0
  rw [supported_trace_zero hm hs hζ hp hps, supported_trace_zero hm hs hζ.inv hp hps]
  simp

#print axioms obstruction_nonzero
#print axioms obstruction_trace_zero

end SpanningCriterionCharacter
