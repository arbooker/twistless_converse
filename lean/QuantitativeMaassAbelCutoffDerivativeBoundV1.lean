module

public import QuantitativeMaassAbelCutoffV1
public import QuantitativeMaassAbelShrinkingSupportV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem smoothTransition_deriv_compact : HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))
  intro q hq
  have hq' : q<0 ∨ 1<q := by
    by_cases h0 : 0≤q
    · right; by_contra hn; exact hq ⟨h0,le_of_not_gt hn⟩
    · exact Or.inl (lt_of_not_ge h0)
  rcases hq' with hq'|hq'
  · have he : Real.smoothTransition=ᶠ[𝓝 q] (fun _ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds hq'] with t ht
      exact Real.smoothTransition.zero_of_nonpos ht.le
    simpa only [deriv_const] using he.deriv_eq
  · have he : Real.smoothTransition=ᶠ[𝓝 q] (fun _ => (1:ℝ)) := by
      filter_upwards [Ioi_mem_nhds hq'] with t ht
      exact Real.smoothTransition.one_of_one_le ht.le
    simpa only [deriv_const] using he.deriv_eq

theorem smoothTransition_deriv_bounded :
    ∃ D : ℝ,0≤D ∧ ∀ q,|deriv Real.smoothTransition q|≤D := by
  have hc := (Real.smoothTransition.contDiff (n:=(⊤:ℕ∞))).continuous_deriv (by simp)
  obtain ⟨D,hD⟩ := smoothTransition_deriv_compact.exists_bound_of_continuous hc
  refine ⟨D,?_,?_⟩
  · exact (norm_nonneg (deriv Real.smoothTransition 0)).trans (hD 0)
  · intro q; simpa only [Real.norm_eq_abs] using hD q

theorem abelCutoffReal_le_one (a q : ℝ) : abelCutoffReal a q≤1 := by
  have h1 := Real.smoothTransition.nonneg (q+1)
  have h2 := Real.smoothTransition.le_one (q+1)
  have h3 := Real.smoothTransition.nonneg ((q-1)/a)
  have h4 := Real.smoothTransition.le_one ((q-1)/a)
  unfold abelCutoffReal
  nlinarith

theorem abelCutoff_norm_le_one (a q : ℝ) : ‖abelCutoff a q‖≤1 := by
  rw [abelCutoff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (abelCutoffReal_nonneg a q)]
  exact abelCutoffReal_le_one a q

theorem abelCutoffReal_deriv_formula (a q : ℝ) :
    deriv (abelCutoffReal a) q=
      deriv Real.smoothTransition (q+1)*(1-Real.smoothTransition ((q-1)/a))-
        Real.smoothTransition (q+1)*(deriv Real.smoothTransition ((q-1)/a)/a) := by
  have hd (t : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
    ((Real.smoothTransition.contDiff (n:=(⊤:ℕ∞))).differentiable (by simp) t).hasDerivAt
  have h1 := (hd (q+1)).comp q ((hasDerivAt_id q).add_const 1)
  have h2 := (hd ((q-1)/a)).comp q (((hasDerivAt_id q).sub_const 1).div_const a)
  have h := (h1.mul ((hasDerivAt_const q (1:ℝ)).sub h2)).deriv
  convert! h using 1
  dsimp [abelCutoffReal,Function.comp_def]
  ring

/-- The concrete cutoff has the expected reciprocal-width derivative bound. -/
theorem abelCutoff_derivative_bound (D : ℝ) (hD : 0≤D)
    (hb : ∀ q,|deriv Real.smoothTransition q|≤D)
    (a : ℝ) (ha : 0<a) (ha1 : a≤1) (q : ℝ) :
    ‖deriv (abelCutoff a) q‖≤2*D/a := by
  rw [abelCutoff_deriv,Complex.norm_real,Real.norm_eq_abs,abelCutoffReal_deriv_formula]
  have h1 := Real.smoothTransition.nonneg (q+1)
  have h2 := Real.smoothTransition.le_one (q+1)
  have h3 := Real.smoothTransition.nonneg ((q-1)/a)
  have h4 := Real.smoothTransition.le_one ((q-1)/a)
  have hd := hb (q+1)
  have he := hb ((q-1)/a)
  have h := abs_sub (deriv Real.smoothTransition (q+1)*(1-Real.smoothTransition ((q-1)/a)))
    (Real.smoothTransition (q+1)*(deriv Real.smoothTransition ((q-1)/a)/a))
  rw [abs_mul,abs_mul,abs_div,abs_of_pos ha,abs_of_nonneg h1,
    abs_of_nonneg (sub_nonneg.mpr h4)] at h
  have hleft : |deriv Real.smoothTransition (q+1)| *(1-Real.smoothTransition ((q-1)/a))≤D := by
    nlinarith [abs_nonneg (deriv Real.smoothTransition (q+1))]
  have hright : Real.smoothTransition (q+1)*(|deriv Real.smoothTransition ((q-1)/a)|/a)≤D/a := by
    exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he ha.le) h1).trans
      (mul_le_of_le_one_left (div_nonneg hD ha.le) h2)
  have hDa : D≤D/a := (le_div_iff₀ ha).mpr (mul_le_of_le_one_right hD ha1)
  rw [mul_div_assoc]
  linarith

#print axioms smoothTransition_deriv_bounded
#print axioms abelCutoff_norm_le_one
#print axioms abelCutoffReal_deriv_formula
#print axioms abelCutoff_derivative_bound

end QuantitativeMaass
