module

public import SpanningCriterionConditionV1
public import SpanningActualKernelV1
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

namespace SpanningCriterionObstructionBounds

open GridPrimeParts GridAdmissibleGap SpanningActualKernel SpanningLevelArithmetic
  SpanningWindows

theorem coprime_levelPart {N q s : ℕ} (hN : 0 < N) (hc : Nat.Coprime q s) :
    Nat.Coprime q (levelPart N s) := by
  apply Nat.coprime_of_dvd'
  intro p hp hpq hpn
  have hps := ((prime_dvd_part hN.ne' hp (fun p => p ∣ s)).mp hpn).2
  exact False.elim (hp.ne_one (Nat.eq_one_of_dvd_coprimes hc hpq hps))

theorem level_lower_bound {N q s : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hc : Nat.Coprime q s) (hbad : s^2 ≤ levelPart N s) :
    (q*s)^2 ≤ level N q := by
  have hd : q^2 * levelPart N s ∣ level N q :=
    ((coprime_levelPart hN hc).pow_left 2).mul_dvd_of_dvd_of_dvd
      (Nat.dvd_lcm_right N (q^2)) ((part_dvd N _).trans (Nat.dvd_lcm_left N (q^2)))
  have hh := Nat.le_of_dvd (level_pos hN hq) hd
  calc (q*s)^2 = q^2*s^2 := mul_pow q s 2
       _ ≤ q^2*levelPart N s := Nat.mul_le_mul_left _ hbad
       _ ≤ level N q := hh

theorem radius_le {N q s m : ℕ} (hN : 0 < N) (hq : 0 < q) (hs : 0 < s)
    (hc : Nat.Coprime q s) (hbad : s^2 ≤ levelPart N s) :
    radius N (m*s) q ≤ (m : ℝ)/q := by
  have hsq : ((q : ℝ)*s)^2 ≤ (level N q : ℝ) := by
    exact_mod_cast level_lower_bound hN hq hc hbad
  have hsqrt : (q : ℝ)*s ≤ Real.sqrt (level N q) := Real.le_sqrt_of_sq_le hsq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  calc radius N (m*s) q = ((m : ℝ)*s)/Real.sqrt (level N q) := by
         simp only [radius, Nat.cast_mul]
       _ ≤ ((m : ℝ)*s)/((q : ℝ)*s) :=
         div_le_div_of_nonneg_left (by positivity) (mul_pos hqR hsR) hsqrt
       _ = (m : ℝ)/q := by field_simp

theorem legal_small {N q s m : ℕ} (hN : 0 < N) (hq : 0 < q) (hs : 0 < s)
    (hc : Nat.Coprime q s) (hbad : s^2 ≤ levelPart N s) {u : ℤ}
    (hu : Legal (radius N (m*s) q) u) : -(m : ℤ) < (q : ℤ)*u ∧ (q : ℤ)*u < m := by
  have hh := radius_le (m:=m) hN hq hs hc hbad
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlo : -(m : ℝ) < (q : ℝ)*u := by
    have h := (mul_lt_mul_of_pos_left hu.1 hqR)
    have h' := (le_div_iff₀ hqR).mp hh
    nlinarith
  have hhi : (q : ℝ)*u < m := by
    have h := (mul_lt_mul_of_pos_left hu.2 hqR)
    have h' := (le_div_iff₀ hqR).mp hh
    nlinarith
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

/-- A legal row coprime to the obstruction order can meet its support only
at translate zero. -/
theorem legal_support_translate_zero {N q s m : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hm : 0 < m) (hs : 0 < s) (hqd : q ∣ m*s)
    (hc : Nat.Coprime q s) (hbad : s^2 ≤ levelPart N s) {u : ℤ}
    (hu : Legal (radius N (m*s) q) u) (a : ℕ)
    (hd : (m : ℤ) ∣ u + a*((m*s)/q : ℕ)) : u = 0 := by
  have he : (q : ℤ)*((m*s)/q : ℕ) = (m : ℤ)*s := by
    exact_mod_cast Nat.mul_div_cancel' hqd
  have hd' : (m : ℤ) ∣ (q : ℤ)*u := by
    have hh := dvd_mul_of_dvd_right hd (q : ℤ)
    have he' : (q : ℤ)*(u+a*((m*s)/q : ℕ)) = (q : ℤ)*u + (m : ℤ)*(a*s) := by
      calc _ = (q : ℤ)*u + a*((q : ℤ)*((m*s)/q : ℕ)) := by ring
           _ = _ := by rw [he]; ring
    rw [he'] at hh
    exact (Int.dvd_add_left (dvd_mul_right _ _)).mp hh
  obtain ⟨k,hk⟩ := hd'
  obtain ⟨hlo,hhi⟩ := legal_small hN hq hs hc hbad hu
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hk0 : k = 0 := by
    have h1 : k < 1 := by nlinarith
    have h2 : -1 < k := by nlinarith
    omega
  rw [hk0, mul_zero] at hk
  exact (mul_eq_zero.mp hk).resolve_left (by exact_mod_cast hq.ne')

#print axioms legal_support_translate_zero

end SpanningCriterionObstructionBounds
