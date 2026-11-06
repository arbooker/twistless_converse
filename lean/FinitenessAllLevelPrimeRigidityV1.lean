module

public import IndependentBasesV1
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

set_option autoImplicit false

public section

namespace FinitenessAllLevelPrimeRigidity

/-- The ceiling errors in all positive powers disappear in the slope
inequality. This is the arithmetic limit step in the two-prime argument. -/
theorem slope_le {a u v : ℝ} (ha : 0 ≤ a) (hu : 0 < u)
    (h : ∀ m : ℕ, 0 < m → (m : ℝ)*v ≤ (Nat.ceil ((m : ℝ)*a) : ℝ)*u) :
    v ≤ a*u := by
  by_contra! hv
  have hd : 0 < v-a*u := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (u/(v-a*u))
  have hmpos : 0 < m := by
    have : (0 : ℝ) < m := lt_trans (div_pos hu hd) hm
    exact_mod_cast this
  have hm' := (div_lt_iff₀ hd).mp hm
  have hc := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg m) ha)
  have hb := h m hmpos
  have hcu := mul_lt_mul_of_pos_right hc hu
  nlinarith

/-- No positive integer pole orders can satisfy both families of the
paper's two-prime ceiling inequalities. This proves the final arithmetic
contradiction; producing such pole orders from an analytic curve is separate. -/
theorem no_positive_pole_orders {p r u v : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) (hu : 0 < u) (hv : 0 < v)
    (hpr : ∀ m : ℕ, 0 < m →
      (m : ℝ)*v ≤ (Nat.ceil ((m : ℝ)*(Real.log p/Real.log r)) : ℝ)*u)
    (hrp : ∀ m : ℕ, 0 < m →
      (m : ℝ)*u ≤ (Nat.ceil ((m : ℝ)*(Real.log r/Real.log p)) : ℝ)*v) : False := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlr : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr.one_lt)
  have hvle := slope_le (div_pos hlp hlr).le (by exact_mod_cast hu) hpr
  have hule := slope_le (div_pos hlr hlp).le (by exact_mod_cast hv) hrp
  have h1 : (v : ℝ)*Real.log r ≤ (u : ℝ)*Real.log p := by
    apply (le_div_iff₀ hlr).mp
    convert hvle using 1
    ring
  have h2 : (u : ℝ)*Real.log p ≤ (v : ℝ)*Real.log r := by
    apply (le_div_iff₀ hlp).mp
    convert hule using 1
    ring
  have he : (r : ℝ)^v = (p : ℝ)^u :=
    Real.log_injOn_pos (pow_pos hr0 v) (pow_pos hp0 u)
      (by simpa only [Real.log_pow] using le_antisymm h1 h2)
  have hen : r^v = p^u := by exact_mod_cast he
  have hc : r.Coprime p := hr.coprime_iff_not_dvd.mpr (by
    intro hd
    rcases hp.eq_one_or_self_of_dvd r hd with hh | hh
    · exact hr.ne_one hh
    · exact hne hh.symm)
  have hind := IndependentBases.independent_of_coprime hr.two_le hp.two_le hc
  exact (Nat.ne_of_gt hv) (hind v u hen).1

#print axioms slope_le
#print axioms no_positive_pole_orders

end FinitenessAllLevelPrimeRigidity
