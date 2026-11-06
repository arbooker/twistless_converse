module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import QuantitativeArithmeticCurvedTaylorPoleBoundV1
public import QuantitativeArithmeticDilationLaplaceTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticMellinTransport. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticMellinInversionTransportV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticMellinTransport
open Complex Filter Set MeasureTheory
open scoped Topology

/-- Inversion together with the weight factor sends the weight pole to zero. -/
theorem inverted_mellin (k : ℕ) (g : ℝ → ℂ) (s : ℂ) :
    mellin (fun y : ℝ => (y:ℂ)^(-(k:ℂ))*g y⁻¹) s=mellin g ((k:ℂ)-s) := by
  change mellin (fun y : ℝ => (y:ℂ)^(-(k:ℂ)) • g y⁻¹) s=_
  rw [mellin_cpow_smul,mellin_comp_inv]
  congr 1
  ring

/-- Logarithmic substitution identifies a genuine one-sided Laplace integral
with the Mellin integral truncated at height one. -/
theorem logarithmic_mellin (g : ℝ → ℂ) (s : ℂ) :
    QuantitativeArithmeticDilationLaplace.transform (fun t => g (Real.exp t)) s=
      ∫ y in Ioi (1:ℝ), (y:ℂ)^(s-1)*g y := by
  have he := integral_comp_exp_Ioi (fun y : ℝ => (y:ℂ)^(s-1)*g y) 0
  simp only [Real.exp_zero] at he
  rw [← he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change g (Real.exp t)*Complex.exp (s*(t:ℂ))=
    Real.exp t • (((Real.exp t:ℝ):ℂ)^(s-1)*g (Real.exp t))
  have hn : ((Real.exp t:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
  have hl : Complex.log ((Real.exp t:ℝ):ℂ)=(t:ℂ) := by
    rw [← Complex.ofReal_log (le_of_lt (Real.exp_pos t)),Real.log_exp]
  rw [Complex.cpow_def_of_ne_zero hn,hl]
  rw [Algebra.smul_def]
  change g (Real.exp t)*Complex.exp (s*(t:ℂ))=
    ((Real.exp t:ℝ):ℂ)*(Complex.exp ((t:ℂ)*(s-1))*g (Real.exp t))
  rw [Complex.ofReal_exp]
  rw [← mul_assoc,← Complex.exp_add]
  have hh : (t:ℂ)+(t:ℂ)*(s-1)=s*(t:ℂ) := by ring
  rw [hh,mul_comm]

/-- Reflection preserves pole order because its derivative is nonzero. -/
theorem reflected_pole_bound (k : ℕ) (J : ℂ → ℂ)
    (hJ : ∀ s, MeromorphicAt J s)
    (hJa : ∀ s, s≠(k:ℂ) → AnalyticAt ℂ J s)
    (hJo : (-1:WithTop ℤ)≤meromorphicOrderAt J (k:ℂ)) :
    (∀ s, MeromorphicAt (fun z : ℂ => J ((k:ℂ)-z)) s) ∧
    (∀ s : ℂ, s≠0 → AnalyticAt ℂ (fun z : ℂ => J ((k:ℂ)-z)) s) ∧
    (-1:WithTop ℤ)≤meromorphicOrderAt (fun z : ℂ => J ((k:ℂ)-z)) 0 := by
  have hd (s : ℂ) : HasDerivAt (fun z : ℂ => (k:ℂ)-z) (-1) s :=
    (hasDerivAt_id s).const_sub (k:ℂ)
  refine ⟨fun s => (hJ _).comp_analyticAt (g:=fun z : ℂ => (k:ℂ)-z)
    (analyticAt_const.sub analyticAt_id),?_,?_⟩
  · intro s hs
    have hn : (k:ℂ)-s≠(k:ℂ) := by
      intro hh
      apply hs
      linear_combination -hh
    exact (hJa _ hn).comp (f:=fun z : ℂ => (k:ℂ)-z) (analyticAt_const.sub analyticAt_id)
  · change (-1:WithTop ℤ)≤meromorphicOrderAt (J ∘ (fun z : ℂ => (k:ℂ)-z)) 0
    have ha : AnalyticAt ℂ (fun z : ℂ => (k:ℂ)-z) 0 := by fun_prop
    have hn : deriv (fun z : ℂ => (k:ℂ)-z) 0≠0 := by
      rw [(hd 0).deriv]
      norm_num
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero ha hn,sub_zero]
    exact hJo

#print axioms inverted_mellin
#print axioms logarithmic_mellin
#print axioms reflected_pole_bound
end QuantitativeArithmeticMellinTransport
end
end

/-! ## QuantitativeArithmeticCurvedLaplaceTransportV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticMellinTransport
open Complex Filter Set MeasureTheory
open scoped Topology

theorem inverted_cutoff_integral (k : ℕ) (g : ℝ → ℂ) (s : ℂ) :
    mellin (fun y : ℝ => (y:ℂ)^(-(k:ℂ))*(Iic (1:ℝ)).indicator g y⁻¹) s=
      ∫ y in Ioi (1:ℝ), (y:ℂ)^(s-1)*((y:ℂ)^(-(k:ℂ))*g y⁻¹) := by
  let F : ℝ → ℂ := fun y => (y:ℂ)^(s-1)*((y:ℂ)^(-(k:ℂ))*g y⁻¹)
  have he : mellin (fun y : ℝ => (y:ℂ)^(-(k:ℂ))*(Iic (1:ℝ)).indicator g y⁻¹) s=
      ∫ y in Ioi (0:ℝ), (Ici (1:ℝ)).indicator F y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    change (y:ℂ)^(s-1)*((y:ℂ)^(-(k:ℂ))*(Iic (1:ℝ)).indicator g y⁻¹)=_
    have hi : y⁻¹≤1 ↔ 1≤y := by exact inv_le_one₀ hy
    by_cases h : 1≤y
    · rw [indicator_of_mem (show y⁻¹∈Iic (1:ℝ) from hi.mpr h),
        indicator_of_mem (show y∈Ici (1:ℝ) from h)]
    · rw [indicator_of_notMem (show y⁻¹∉Iic (1:ℝ) from fun h' => h (hi.mp h')),
        indicator_of_notMem (show y∉Ici (1:ℝ) from h)]
      simp only [mul_zero]
  rw [he,setIntegral_indicator measurableSet_Ici]
  have hset : Ioi (0:ℝ) ∩ Ici (1:ℝ)=Ici (1:ℝ) := by
    apply inter_eq_right.mpr
    intro y hy
    exact lt_of_lt_of_le zero_lt_one hy
  rw [hset,integral_Ici_eq_integral_Ioi]

/-- The actual logarithmic ray integral is the reflected curved Mellin
transform; the cutoff is at height one and no asymptotic replacement is used. -/
theorem curved_laplace_identity (k : ℕ) (a : ℕ → ℂ) (β c r : ℝ) (s : ℂ) :
    QuantitativeArithmeticDilationLaplace.transform
      (fun t => ((Real.exp t:ℝ):ℂ)^(-(k:ℂ))*
        QuantitativeArithmeticCurvedTaylor.curved k a β c r (Real.exp t)⁻¹) s=
      mellin (QuantitativeArithmeticCurvedTaylor.truncated k a β c r 1) ((k:ℂ)-s) := by
  rw [logarithmic_mellin (fun y : ℝ => (y:ℂ)^(-(k:ℂ))*
    QuantitativeArithmeticCurvedTaylor.curved k a β c r y⁻¹) s,
    ← inverted_cutoff_integral,inverted_mellin]
  rfl

#print axioms inverted_cutoff_integral
#print axioms curved_laplace_identity
end QuantitativeArithmeticMellinTransport
end
end
