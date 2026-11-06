module

public import SmallLevelTaylorCoefficientMellinV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex Filter Set MeasureTheory FormalMultilinearSeries FinitenessPolynomialSeries
open scoped Topology

theorem taylorCoeff_convergent (k : ℕ) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) {c : ℝ} (hc : 0<c) :
    ∃ K : ℕ, ∀ β : ℝ, ∀ s : ℂ, (K:ℝ)<s.re → ∀ n : ℕ,
      MellinConvergent (fun y => taylorCoeff k a β c y n) s := by
  obtain ⟨K,D,E,κ,hD,hE,hκ,hbound⟩ := deformed_mellin_envelope k ha ha0 hc
  refine ⟨K,?_⟩
  intro β s hs n
  have hw : ContinuousOn (fun y : ℝ => (y:ℂ)^(s-1)) (Ioi 0) := by
    intro y hy
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hy))).continuousWithinAt
  have hb := (mellinEnvelope_integrable K hD hE hκ hs).mul_const (2^n:ℝ)
  unfold MellinConvergent
  simp only [smul_eq_mul]
  apply hb.mono' ((hw.mul (taylorCoeff_continuous k ha β hc n)).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simp only [Pi.mul_apply]
  rw [norm_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (taylorCoeff_bound k a β c y (hbound β y hy) n) (norm_nonneg _)

def taylorTerm (k : ℕ) (a : ℕ → ℂ) (β c r : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  cauchyPowerSeries (deformed k a β c y) 0 (1/2) n (fun _ => ((y/r:ℝ):ℂ)*I)

theorem taylorTerm_eq (k : ℕ) (a : ℕ → ℂ) (β c r : ℝ) (n : ℕ) (y : ℝ) :
    taylorTerm k a β c r n y=(I/(r:ℂ))^n*((y:ℂ)^n*taylorCoeff k a β c y n) := by
  unfold taylorTerm
  rw [apply_eq_pow_smul_coeff]
  change _=(I/(r:ℂ))^n*((y:ℂ)^n*(cauchyPowerSeries (deformed k a β c y) 0 (1/2)).coeff n)
  simp only [smul_eq_mul,Complex.ofReal_div,mul_pow,div_pow]
  ring

theorem taylorTerm_mellin (k : ℕ) (a : ℕ → ℂ) (β c r : ℝ) (n : ℕ) (s : ℂ) :
    mellin (taylorTerm k a β c r n) s=
      (I/(r:ℂ))^n*mellin (fun y => taylorCoeff k a β c y n) (s+(n:ℂ)) := by
  change mellin (fun y => taylorTerm k a β c r n y) s=_
  simp_rw [taylorTerm_eq]
  have hc := mellin_const_smul (fun y : ℝ => (y:ℂ)^n*taylorCoeff k a β c y n) s ((I/(r:ℂ))^n)
  simp only [smul_eq_mul] at hc
  rw [hc]
  congr 1
  simpa only [Complex.cpow_natCast,smul_eq_mul] using
    mellin_cpow_smul (fun y => taylorCoeff k a β c y n) s (n:ℂ)

theorem taylorTerm_convergent (k : ℕ) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) {c : ℝ} (hc : 0<c) :
    ∃ K : ℕ, ∀ β r : ℝ, ∀ s : ℂ, (K:ℝ)<s.re → ∀ n : ℕ,
      MellinConvergent (taylorTerm k a β c r n) s := by
  obtain ⟨K,hK⟩ := taylorCoeff_convergent k ha ha0 hc
  refine ⟨K,?_⟩
  intro β r s hs n
  have hs' : (K:ℝ)<(s+(n:ℂ)).re := by
    simp only [Complex.add_re,Complex.natCast_re]
    exact lt_of_lt_of_le hs (le_add_of_nonneg_right (Nat.cast_nonneg n))
  have h := ((MellinConvergent.cpow_smul).mpr (hK β (s+(n:ℂ)) hs' n)).const_smul ((I/(r:ℂ))^n)
  change MellinConvergent (fun y => taylorTerm k a β c r n y) s
  simpa only [taylorTerm_eq,smul_eq_mul,Complex.cpow_natCast] using h

/-- The actual evaluated Taylor term contributes the shifted additive
transform, including the phase (i/r)^n and the scale c^(s+n). -/
theorem taylorTerm_additive_mellin (k : ℕ) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) {c : ℝ} (hc : 0<c) :
    ∃ B : ℝ, ∀ β r : ℝ, ∀ s : ℂ, B<s.re → ∀ n : ℕ,
      mellin (taylorTerm k a β c r n) s=
        (I/(r:ℂ))^n*Ring.choose (s+(n:ℂ)-(k:ℂ)) n*(c:ℂ)^(s+(n:ℂ))*
          SmallLevelAdditive.transform a β (s+(n:ℂ)) := by
  obtain ⟨B,hB⟩ := taylorCoeff_additive_mellin k ha ha0 hc
  refine ⟨B,?_⟩
  intro β r s hs n
  have hs' : B<(s+(n:ℂ)).re := by
    simp only [Complex.add_re,Complex.natCast_re]
    exact lt_of_lt_of_le hs (le_add_of_nonneg_right (Nat.cast_nonneg n))
  rw [taylorTerm_mellin,hB β (s+(n:ℂ)) hs' n]
  ring

#print axioms taylorCoeff_convergent
#print axioms taylorTerm_mellin
#print axioms taylorTerm_convergent
#print axioms taylorTerm_additive_mellin
end SmallLevelTaylor
