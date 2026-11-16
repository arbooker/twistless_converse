module

public import MaassEulerInputV1
public import MaassKBesselDecayV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Asymptotics
open scoped Topology

namespace QuantitativeMaass

/-- An individual polynomial growth exponent supplies a natural-power bound
on the positive coefficients; no common exponent across solutions is required. -/
theorem polynomialGrowth_positive_bound {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b) :
    ∃ m : ℕ,∃ C : ℝ,0<C ∧ ∀ n : ℕ,‖b (n+1)‖≤C*((n+1:ℕ):ℝ)^m := by
  obtain ⟨τ,hτ⟩ := hb
  obtain ⟨C,hC,hbound⟩ := bound_of_isBigO_nat_atTop hτ
  obtain ⟨m,hm⟩ := exists_nat_ge τ
  refine ⟨m,C,hC,?_⟩
  intro n
  have hn : 0<((n+1:ℕ):ℝ) := by positivity
  have hh : ‖b (n+1)‖≤C*((n+1:ℕ):ℝ)^τ := by
    simpa only [Real.norm_eq_abs,abs_norm,abs_of_pos (Real.rpow_pos_of_pos hn τ)] using
      hbound (Real.rpow_pos_of_pos hn τ).ne'
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  rw [←Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) hm

/-- Polynomially weighted original coefficients are absolutely summable after
any fixed positive exponential damping. -/
theorem polynomialGrowth_exp_summable {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (j : ℕ) (a : ℝ) (ha : 0<a) :
    Summable (fun n : ℕ => ‖b (n+1)‖*((n+1:ℕ):ℝ)^j*Real.exp (-a*((n+1:ℕ):ℝ))) := by
  obtain ⟨m,C,hC,hbound⟩ := polynomialGrowth_positive_bound hb
  have hs : Summable (fun n : ℕ => ((n+1:ℕ):ℝ)^(m+j)*Real.exp (-a*((n+1:ℕ):ℝ))) :=
    (summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul (m+j) ha)
  apply (hs.mul_left C).of_nonneg_of_le (fun _ => by positivity)
  intro n
  calc
    _ ≤ (C*((n+1:ℕ):ℝ)^m)*((n+1:ℕ):ℝ)^j*Real.exp (-a*((n+1:ℕ):ℝ)) := by
      gcongr
      exact hbound n
    _ = _ := by rw [pow_add]; ring

/-- Actual Bessel moments decay uniformly from any positive argument threshold,
including thresholds below one needed on arbitrary compact subsets of y>0. -/
theorem bessel_moment_decay_from (j : ℕ) (r a x : ℝ) (ha : 0<a) (hax : a≤x) :
    ‖MaassKBessel.moment j r x‖≤Real.exp (a-x)*MaassKBessel.moment j 0 a := by
  have hx : 0<x := ha.trans_le hax
  have hg : IntegrableOn (fun u : ℝ => Real.exp (a-x)*
      (Real.cosh u^j*Real.exp (-a*Real.cosh u))) (Ioi 0) :=
    (MaassKBessel.zero_moment_integrable j ha).const_mul _
  calc
    _ ≤ ∫ u in Ioi (0:ℝ),‖Real.cosh u^j*Real.exp (-x*Real.cosh u)*Real.cos (r*u)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi (0:ℝ),Real.exp (a-x)*(Real.cosh u^j*Real.exp (-a*Real.cosh u)) := by
      apply integral_mono (MaassKBessel.moment_integrable j r hx).norm hg
      intro u
      have he : Real.exp (-x*Real.cosh u)≤Real.exp (a-x)*Real.exp (-a*Real.cosh u) := by
        rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr (Real.one_le_cosh u))]
      simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Real.cosh_pos u).le j),
        abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ Real.cosh u^j*Real.exp (-x*Real.cosh u) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (r*u)) (by positivity : 0≤Real.cosh u^j*Real.exp (-x*Real.cosh u))
        _ ≤ Real.cosh u^j*(Real.exp (a-x)*Real.exp (-a*Real.cosh u)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
        _ = _ := by ring
    _ = _ := by
      rw [integral_const_mul]
      simp only [MaassKBessel.moment,zero_mul,Real.cos_zero,mul_one]

#print axioms polynomialGrowth_positive_bound
#print axioms polynomialGrowth_exp_summable
#print axioms bessel_moment_decay_from

end QuantitativeMaass
