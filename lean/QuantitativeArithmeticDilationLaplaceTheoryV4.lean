module

public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.Indicator
public import QuantitativeArithmeticDilationRectanglesTheoryV4
public import QuantitativeArithmeticDilationRecurrencePropagationV1
public import QuantitativeArithmeticSimplePoleSubtractionV1

/-! Consolidated chapter: QuantitativeArithmeticDilationLaplace. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticDilationLaplaceShiftV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex MeasureTheory Set

theorem integral_Ioi_translate (f : ℝ → ℂ) (c : ℝ) :
    (∫ t in Ioi 0, f (t+c))=∫ t in Ioi c, f t := by
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioi]
  rw [← integral_add_right_eq_self ((Ioi c).indicator f) c]
  congr 1
  funext t
  have hh : c<t+c ↔ 0<t := by constructor <;> intro h <;> linarith
  simp only [indicator_apply,mem_Ioi,hh]

def transform (H : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t in Ioi 0, H t*exp (s*(t:ℂ))

def segment (H : ℝ → ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..c, H t*exp (s*(t:ℂ))

/-- Translation of the one-sided Laplace integral. This is an identity
of the actual convergent integrals, before meromorphic continuation. -/
theorem transform_shift (H : ℝ → ℂ) (s : ℂ) (c : ℝ) (hc : 0≤c)
    (hH : IntegrableOn (fun t : ℝ => H t*exp (s*(t:ℂ))) (Ioi 0)) :
    transform (fun t => H (t+c)) s=
      exp (-s*(c:ℂ))*(transform H s-segment H c s) := by
  have hpoint (t : ℝ) : H (t+c)*exp (s*(t:ℂ))=
      exp (-s*(c:ℂ))*(H (t+c)*exp (s*((t+c:ℝ):ℂ))) := by
    rw [mul_left_comm,← exp_add]
    congr 1
    push_cast
    ring
  have htail : (∫ t in Ioi c, H t*exp (s*(t:ℂ)))=
      transform H s-segment H c s := by
    have hh := intervalIntegral.integral_Ioi_sub_Ioi hH hc
    dsimp [transform,segment]
    linear_combination -hh
  unfold transform
  simp_rw [hpoint]
  rw [integral_const_mul,
    integral_Ioi_translate (fun t : ℝ => H t*exp (s*(t:ℂ))) c,htail]
  rfl

#print axioms integral_Ioi_translate
#print axioms transform_shift
end QuantitativeArithmeticDilationLaplace
end
end

/-! ## QuantitativeArithmeticDilationLaplaceRecurrenceV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex MeasureTheory Set Finset

theorem integrableOn_Ioi_translate {f : ℝ → ℂ} {c : ℝ}
    (hf : IntegrableOn f (Set.Ioi c)) : IntegrableOn (fun t => f (t+c)) (Set.Ioi 0) := by
  have hh := (hf.integrable_indicator measurableSet_Ioi).comp_add_right c
  have he : (fun t : ℝ => (Set.Ioi c).indicator f (t+c))=
      (Set.Ioi 0).indicator (fun t => f (t+c)) := by
    funext t
    have ht : c<t+c ↔ 0<t := by constructor <;> intro h <;> linarith
    simp only [indicator_apply,Set.mem_Ioi,ht]
  rw [he,integrable_indicator_iff measurableSet_Ioi] at hh
  exact hh

theorem integrable_shift (H : ℝ → ℂ) (s : ℂ) (c : ℝ) (hc : 0≤c)
    (hH : IntegrableOn (fun t : ℝ => H t*exp (s*(t:ℂ))) (Set.Ioi 0)) :
    IntegrableOn (fun t : ℝ => H (t+c)*exp (s*(t:ℂ))) (Set.Ioi 0) := by
  have hb := integrableOn_Ioi_translate (hH.mono_set (Ioi_subset_Ioi hc))
  have hs := hb.const_mul (exp (-s*(c:ℂ)))
  have he : (fun t : ℝ => H (t+c)*exp (s*(t:ℂ)))=
      (fun t : ℝ => exp (-s*(c:ℂ))*(H (t+c)*exp (s*((t+c:ℝ):ℂ)))) := by
    funext t
    rw [mul_left_comm,← exp_add]
    congr 1
    push_cast
    ring
  change Integrable _ _
  rw [he]
  exact hs

/-- A finite translation recurrence gives its polynomial-denominator
identity in the initial convergence half-plane. All shifted integrability
is derived from the original half-line integral. -/
theorem recurrence_identity (H : ℝ → ℂ) (s : ℂ) (L : ℝ) (hL : 0≤L)
    (d : ℕ) (a : ℕ → ℂ)
    (hH : IntegrableOn (fun t : ℝ => H t*exp (s*(t:ℂ))) (Set.Ioi 0))
    (hrec : ∀ t : ℝ, ∑ j ∈ range (d+1), a j*H (t+(j:ℝ)*L)=0) :
    (∑ j ∈ range (d+1), a j*exp (-s*((j:ℝ)*L:ℝ)))*transform H s=
      ∑ j ∈ range (d+1), a j*exp (-s*((j:ℝ)*L:ℝ))*segment H ((j:ℝ)*L) s := by
  have hi (j : ℕ) : IntegrableOn
      (fun t : ℝ => a j*H (t+(j:ℝ)*L)*exp (s*(t:ℂ))) (Set.Ioi 0) := by
    change Integrable _ _
    simpa only [mul_assoc] using
      (integrable_shift H s ((j:ℝ)*L) (mul_nonneg (Nat.cast_nonneg j) hL) hH).const_mul (a j)
  have hsum : (∑ j ∈ range (d+1), a j*transform (fun t => H (t+(j:ℝ)*L)) s)=0 := by
    calc
      (∑ j ∈ range (d+1), a j*transform (fun t => H (t+(j:ℝ)*L)) s) =
          ∫ t in Set.Ioi (0:ℝ), ∑ j ∈ range (d+1), a j*H (t+(j:ℝ)*L)*exp (s*(t:ℂ)) := by
        rw [integral_finsetSum _ (fun j _ => hi j)]
        simp only [mul_assoc,integral_const_mul,transform]
      _ = 0 := by simp only [← sum_mul,hrec,zero_mul,integral_zero]
  have hshift (j : ℕ) :=
    transform_shift H s ((j:ℝ)*L) (mul_nonneg (Nat.cast_nonneg j) hL) hH
  simp only [hshift,mul_sub,← mul_assoc,sum_sub_distrib,← sum_mul] at hsum
  exact sub_eq_zero.mp hsum

#print axioms integrable_shift
#print axioms recurrence_identity
end QuantitativeArithmeticDilationLaplace
end
end

/-! ## QuantitativeArithmeticDilationLaplacePolynomialV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex MeasureTheory Set

def recurrencePolynomial (d : ℕ) (a : ℕ → ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (d+1), Polynomial.monomial j (a j)

def numerator (H : ℝ → ℂ) (L : ℝ) (d : ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (d+1), a j*exp (-s*((j:ℝ)*L:ℝ))*segment H ((j:ℝ)*L) s

theorem polynomial_identity (H : ℝ → ℂ) (s : ℂ) (L : ℝ) (hL : 0≤L)
    (d : ℕ) (a : ℕ → ℂ)
    (hH : IntegrableOn (fun t : ℝ => H t*exp (s*(t:ℂ))) (Ioi 0))
    (hrec : ∀ t : ℝ, ∑ j ∈ Finset.range (d+1), a j*H (t+(j:ℝ)*L)=0) :
    (recurrencePolynomial d a).eval (exp (-(L:ℂ)*s))*transform H s=
      numerator H L d a s := by
  have hden : (recurrencePolynomial d a).eval (exp (-(L:ℂ)*s))=
      ∑ j ∈ Finset.range (d+1), a j*exp (-s*((j:ℝ)*L:ℝ)) := by
    simp only [recurrencePolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← exp_nat_mul]
    apply congrArg (fun z : ℂ => a j*exp z)
    push_cast
    ring
  rw [hden]
  exact recurrence_identity H s L hL d a hH hrec

theorem recurrencePolynomial_ne_zero (d : ℕ) (a : ℕ → ℂ) (ha : a 0≠0) :
    recurrencePolynomial d a≠0 := by
  intro h
  have he := congrArg (fun P : Polynomial ℂ => P.coeff 0) h
  simp [recurrencePolynomial,Polynomial.coeff_monomial] at he
  exact ha he

#print axioms polynomial_identity
#print axioms recurrencePolynomial_ne_zero
end QuantitativeArithmeticDilationLaplace
end
end

/-! ## QuantitativeArithmeticDilationLaplaceEntireV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex MeasureTheory Set Filter
open scoped Topology

/-- A finite-interval Laplace integral is entire. Compactness controls the
parameter derivative locally, so no smoothness of H is needed. -/
theorem segment_entire (H : ℝ → ℂ) (hH : Continuous H) (c : ℝ) :
    Differentiable ℂ (segment H c) := by
  intro s
  let F : ℂ → ℝ → ℂ := fun z t => H t * exp (z*(t:ℂ))
  let D : ℂ → ℝ → ℂ := fun z t => H t * (exp (z*(t:ℂ))*(t:ℂ))
  have hF (z : ℂ) : Continuous (F z) := by dsimp [F]; fun_prop
  have hD : Continuous (fun p : ℂ×ℝ => D p.1 p.2) := by dsimp [D]; fun_prop
  obtain ⟨C,hC⟩ := ((isCompact_closedBall s (1:ℝ)).prod
    (isCompact_uIcc : IsCompact (uIcc (0:ℝ) c))).exists_bound_of_continuousOn hD.continuousOn
  have hd (t : ℝ) (z : ℂ) : HasDerivAt (fun z => F z t) (D z t) z := by
    dsimp [F,D]
    convert (((hasDerivAt_id z).mul_const (t:ℂ)).cexp.const_mul (H t)) using 1 <;>
      simp only [id_eq,one_mul]
  have hh := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume)
    (F := F) (F' := D) (bound := fun _ => C) (a := (0:ℝ)) (b := c)
    (Metric.ball_mem_nhds s (by norm_num : (0:ℝ)<1))
    (Filter.Eventually.of_forall (fun z => (hF z).aestronglyMeasurable))
    ((hF s).intervalIntegrable 0 c)
    ((hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t ht z hz =>
      hC (z,t) ⟨Metric.ball_subset_closedBall hz,uIoc_subset_uIcc ht⟩))
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun t _ z _ => hd t z))
  exact hh.2.differentiableAt

theorem numerator_entire (H : ℝ → ℂ) (hH : Continuous H)
    (L : ℝ) (d : ℕ) (a : ℕ → ℂ) : Differentiable ℂ (numerator H L d a) := by
  unfold numerator
  apply Differentiable.fun_sum
  intro j hj
  exact ((differentiable_const (a j)).mul ((differentiable_id.neg.mul_const _).cexp)).mul
    (segment_entire H hH _)

#print axioms segment_entire
#print axioms numerator_entire
end QuantitativeArithmeticDilationLaplace
end
end

/-! ## QuantitativeArithmeticDilationLaplaceStripV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex MeasureTheory Set

theorem segment_norm_le (H : ℝ → ℂ) (c C R : ℝ) (hc : 0≤c) (hR : 0≤R)
    (hH : ∀ t∈Icc 0 c, ‖H t‖≤C) (s : ℂ) (hs : |s.re|≤R) :
    ‖segment H c s‖≤(C*Real.exp (R*c))*c := by
  have hC : 0≤C := (norm_nonneg (H 0)).trans (hH 0 ⟨le_rfl,hc⟩)
  have hb : ∀ t∈Set.uIoc (0:ℝ) c, ‖H t*exp (s*(t:ℂ))‖≤C*Real.exp (R*c) := by
    intro t ht
    rw [uIoc_of_le hc] at ht
    have he : ‖exp (s*(t:ℂ))‖≤Real.exp (R*c) := by
      rw [norm_exp]
      simp only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_right (abs_le.mp hs).2 ht.1.le).trans
        (mul_le_mul_of_nonneg_left ht.2 hR)
    rw [norm_mul]
    exact mul_le_mul (hH t ⟨ht.1.le,ht.2⟩) he (norm_nonneg _) hC
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [segment,sub_zero,abs_of_nonneg hc] using hi

/-- The finite-interval numerator has uniform bounds on every vertical
strip, using only continuity on a compact interval of the original H. -/
theorem numerator_strip_bound (H : ℝ → ℂ) (hH : Continuous H)
    (L : ℝ) (hL : 0≤L) (d : ℕ) (a : ℕ → ℂ) (R : ℝ) (hR : 0≤R) :
    ∃ C₁ : ℝ, ∀ s : ℂ, |s.re|≤R → ‖numerator H L d a s‖≤C₁ := by
  obtain ⟨C,hCbound⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) ((d:ℝ)*L))).exists_bound_of_continuousOn
    hH.continuousOn
  refine ⟨∑ j∈Finset.range (d+1),
    (‖a j‖*Real.exp (R*((j:ℝ)*L)))*((C*Real.exp (R*((j:ℝ)*L)))*((j:ℝ)*L)),?_⟩
  intro s hs
  unfold numerator
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro j hj
  have hjd : (j:ℝ)≤(d:ℝ) := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hjL : 0≤(j:ℝ)*L := mul_nonneg (Nat.cast_nonneg j) hL
  have hseg := segment_norm_le H ((j:ℝ)*L) C R hjL hR
    (fun t ht => hCbound t ⟨ht.1,ht.2.trans (mul_le_mul_of_nonneg_right hjd hL)⟩) s hs
  have he : ‖exp (-s*((j:ℝ)*L:ℝ))‖≤Real.exp (R*((j:ℝ)*L)) := by
    rw [norm_exp]
    simp only [mul_re,neg_re,neg_im,ofReal_re,ofReal_im,mul_zero,sub_zero]
    apply Real.exp_le_exp.mpr
    have hn : -s.re≤R := by have hh := (abs_le.mp hs).1; linarith
    exact mul_le_mul_of_nonneg_right hn hjL
  simp only [norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left he (norm_nonneg _)) hseg
    (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)

#print axioms segment_norm_le
#print axioms numerator_strip_bound
end QuantitativeArithmeticDilationLaplace
end
end

/-! ## QuantitativeArithmeticDilationLaplaceExteriorNumeratorV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex MeasureTheory Set

theorem weighted_segment_norm_le (H : ℝ → ℂ) (c v C : ℝ) (hc : 0≤c)
    (hH : ∀ t∈Icc 0 c, ‖H t‖≤C) (s : ℂ)
    (hs : ∀ t∈Icc 0 c, s.re*(t-v)≤0) :
    ‖exp (-s*(v:ℂ))*segment H c s‖≤C*c := by
  have he : exp (-s*(v:ℂ))*segment H c s=
      ∫ t in (0:ℝ)..c, H t*exp (s*((t-v:ℝ):ℂ)) := by
    rw [segment,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [mul_left_comm,← exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  have hb : ∀ t∈uIoc (0:ℝ) c, ‖H t*exp (s*((t-v:ℝ):ℂ))‖≤C := by
    intro t ht
    rw [uIoc_of_le hc] at ht
    have ht' : t∈Icc 0 c := ⟨ht.1.le,ht.2⟩
    have hexp : ‖exp (s*((t-v:ℝ):ℂ))‖≤1 := by
      rw [norm_exp,Real.exp_le_one_iff]
      simpa only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero] using hs t ht'
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hexp).trans (hH t ht')
  simpa only [sub_zero,abs_of_nonneg hc] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

theorem segment_left_bound (H : ℝ → ℂ) (c C : ℝ) (hc : 0≤c)
    (hH : ∀ t∈Icc 0 c, ‖H t‖≤C) (s : ℂ) (hs : s.re≤0) :
    ‖segment H c s‖≤C*c := by
  simpa only [ofReal_zero,mul_zero,exp_zero,one_mul] using
    weighted_segment_norm_le H c 0 C hc hH s
      (fun t ht => mul_nonpos_of_nonpos_of_nonneg hs (by simpa only [sub_zero] using ht.1))

theorem segment_right_bound (H : ℝ → ℂ) (c C : ℝ) (hc : 0≤c)
    (hH : ∀ t∈Icc 0 c, ‖H t‖≤C) (s : ℂ) (hs : 0≤s.re) :
    ‖exp (-s*(c:ℂ))*segment H c s‖≤C*c :=
  weighted_segment_norm_le H c c C hc hH s
    (fun _t ht => mul_nonpos_of_nonneg_of_nonpos hs (sub_nonpos.mpr ht.2))

/-- The numerator is bounded on the right half-plane; after multiplication
by the highest exponential, it is bounded on the left half-plane. -/
theorem numerator_exterior_bounds (H : ℝ → ℂ) (hH : Continuous H)
    (L : ℝ) (hL : 0≤L) (d : ℕ) (a : ℕ → ℂ) :
    ∃ C : ℝ, 0≤C ∧
      (∀ s : ℂ, 0≤s.re → ‖numerator H L d a s‖≤C) ∧
      (∀ s : ℂ, s.re≤0 →
        ‖exp (s*((d:ℝ)*L:ℝ))*numerator H L d a s‖≤C) := by
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) ((d:ℝ)*L))).exists_bound_of_continuousOn
    hH.continuousOn
  have hB0 : 0≤B := (norm_nonneg (H 0)).trans (hB 0 ⟨le_rfl,by positivity⟩)
  have hjL (j : ℕ) : 0≤(j:ℝ)*L := mul_nonneg (Nat.cast_nonneg j) hL
  have hBj (j : ℕ) (hj : j∈Finset.range (d+1)) :
      ∀ t∈Icc 0 ((j:ℝ)*L), ‖H t‖≤B := by
    have hjd : (j:ℝ)≤(d:ℝ) := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    exact fun t ht => hB t ⟨ht.1,ht.2.trans (mul_le_mul_of_nonneg_right hjd hL)⟩
  refine ⟨∑ j∈Finset.range (d+1), ‖a j‖*(B*((j:ℝ)*L)),by positivity,?_,?_⟩
  · intro s hs
    unfold numerator
    apply le_trans (norm_sum_le _ _)
    apply Finset.sum_le_sum
    intro j hj
    rw [mul_assoc,norm_mul]
    exact mul_le_mul_of_nonneg_left (segment_right_bound H _ B (hjL j) (hBj j hj) s hs)
      (norm_nonneg _)
  · intro s hs
    unfold numerator
    rw [Finset.mul_sum]
    apply le_trans (norm_sum_le _ _)
    apply Finset.sum_le_sum
    intro j hj
    have hjd : (j:ℝ)≤(d:ℝ) := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have he : exp (s*((d:ℝ)*L:ℝ))*(a j*exp (-s*((j:ℝ)*L:ℝ))*segment H ((j:ℝ)*L) s)=
        a j*exp (s*(((d:ℝ)-(j:ℝ))*L:ℝ))*segment H ((j:ℝ)*L) s := by
      have hp : exp (s*((d:ℝ)*L:ℝ))*exp (-s*((j:ℝ)*L:ℝ))=
          exp (s*(((d:ℝ)-(j:ℝ))*L:ℝ)) := by
        rw [← exp_add]
        congr 1
        push_cast
        ring
      calc
        _ = a j*(exp (s*((d:ℝ)*L:ℝ))*exp (-s*((j:ℝ)*L:ℝ)))*
          segment H ((j:ℝ)*L) s := by ring
        _ = _ := by rw [hp]
    rw [he,norm_mul,norm_mul]
    have hx : ‖exp (s*(((d:ℝ)-(j:ℝ))*L:ℝ))‖≤1 := by
      rw [norm_exp,Real.exp_le_one_iff]
      simp only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hs (mul_nonneg (sub_nonneg.mpr hjd) hL)
    exact mul_le_mul (mul_le_of_le_one_right (norm_nonneg _) hx)
      (segment_left_bound H _ B (hjL j) (hBj j hj) s hs)
      (norm_nonneg _) (norm_nonneg _)

#print axioms weighted_segment_norm_le
#print axioms numerator_exterior_bounds
end QuantitativeArithmeticDilationLaplace
end
end

/-! ## QuantitativeArithmeticDilationLaplaceDenominatorV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex Filter
open scoped Topology

theorem denominator_eq_sum (L : ℝ) (d : ℕ) (a : ℕ → ℂ) (s : ℂ) :
    (recurrencePolynomial d a).eval (exp (-(L:ℂ)*s))=
      ∑ j∈Finset.range (d+1), a j*exp (-s*((j:ℝ)*L:ℝ)) := by
  simp only [recurrencePolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← exp_nat_mul]
  apply congrArg (fun z : ℂ => a j*exp z)
  push_cast
  ring

theorem scaled_denominator_eq_sum (L : ℝ) (d : ℕ) (a : ℕ → ℂ) (s : ℂ) :
    exp (s*((d:ℝ)*L:ℝ))*(recurrencePolynomial d a).eval (exp (-(L:ℂ)*s))=
      ∑ j∈Finset.range (d+1), a j*exp (s*(((d:ℝ)-(j:ℝ))*L:ℝ)) := by
  rw [denominator_eq_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_left_comm,← exp_add]
  congr 1
  push_cast
  ring

theorem denominator_tendsto_right (L : ℝ) (hL : 0<L) (d : ℕ) (a : ℕ → ℂ) :
    Tendsto (fun s : ℂ => (recurrencePolynomial d a).eval (exp (-(L:ℂ)*s)))
      (comap Complex.re atTop) (𝓝 (a 0)) := by
  have he : Tendsto (fun s : ℂ => exp (-(L:ℂ)*s))
      (comap Complex.re atTop) (𝓝 0) := by
    apply tendsto_exp_nhds_zero_iff.mpr
    simpa only [mul_re,neg_re,ofReal_re,neg_im,ofReal_im,neg_zero,zero_mul,sub_zero] using
      (tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hL)).mpr
        (tendsto_comap : Tendsto Complex.re (comap Complex.re atTop) atTop)
  have hc : Continuous (fun z : ℂ => (recurrencePolynomial d a).eval z) := by fun_prop
  have hz : (recurrencePolynomial d a).eval 0=a 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simp [recurrencePolynomial,Polynomial.coeff_monomial]
  simpa only [Function.comp_def,hz] using hc.continuousAt.tendsto.comp he

theorem denominator_tendsto_left (L : ℝ) (hL : 0<L) (d : ℕ) (a : ℕ → ℂ) :
    Tendsto (fun s : ℂ => exp (s*((d:ℝ)*L:ℝ))*
      (recurrencePolynomial d a).eval (exp (-(L:ℂ)*s)))
      (comap Complex.re atBot) (𝓝 (a d)) := by
  classical
  have ht (j : ℕ) (hj : j∈Finset.range (d+1)) :
      Tendsto (fun s : ℂ => a j*exp (s*(((d:ℝ)-(j:ℝ))*L:ℝ)))
        (comap Complex.re atBot) (𝓝 (if j=d then a d else 0)) := by
    by_cases h : j=d
    · subst j
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℂ => a d)
        (comap Complex.re atBot) (𝓝 (a d)))
    · have hjd : (j:ℝ)<(d:ℝ) := by
        have hn : j<d := by have hh := Finset.mem_range.mp hj; omega
        exact_mod_cast hn
      have hp : 0<((d:ℝ)-(j:ℝ))*L := mul_pos (sub_pos.mpr hjd) hL
      have he : Tendsto (fun s : ℂ => exp (s*(((d:ℝ)-(j:ℝ))*L:ℝ)))
          (comap Complex.re atBot) (𝓝 0) := by
        apply tendsto_exp_nhds_zero_iff.mpr
        simpa only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero] using
          (tendsto_mul_const_atBot_of_pos hp).mpr
            (tendsto_comap : Tendsto Complex.re (comap Complex.re atBot) atBot)
      simpa only [h,ite_false,mul_zero] using he.const_mul (a j)
  have hh := tendsto_finsetSum (Finset.range (d+1)) ht
  simpa only [← scaled_denominator_eq_sum,Finset.sum_ite_eq',
    Finset.mem_range,Nat.lt_succ_self,ite_true] using hh

/-- Nonzero end coefficients give uniform lower bounds on both exterior
half-planes, after scaling out the largest exponential on the left. -/
theorem denominator_exterior_lower_bounds (L : ℝ) (hL : 0<L) (d : ℕ) (a : ℕ → ℂ)
    (h0 : a 0≠0) (hd : a d≠0) :
    ∃ R : ℝ, 1≤R ∧
      (∀ s : ℂ, R≤s.re → ‖a 0‖/2≤‖(recurrencePolynomial d a).eval (exp (-(L:ℂ)*s))‖) ∧
      (∀ s : ℂ, s.re≤-R → ‖a d‖/2≤‖exp (s*((d:ℝ)*L:ℝ))*
        (recurrencePolynomial d a).eval (exp (-(L:ℂ)*s))‖) := by
  have hr := (denominator_tendsto_right L hL d a).norm.eventually_const_lt
    (half_lt_self (norm_pos_iff.mpr h0))
  have hl := (denominator_tendsto_left L hL d a).norm.eventually_const_lt
    (half_lt_self (norm_pos_iff.mpr hd))
  obtain ⟨r,hr⟩ := eventually_atTop.mp (eventually_comap.mp hr)
  obtain ⟨l,hl⟩ := eventually_atBot.mp (eventually_comap.mp hl)
  refine ⟨max 1 (max r (-l)),le_max_left _ _,?_,?_⟩
  · intro s hs
    exact (hr s.re ((le_max_left r (-l)).trans ((le_max_right 1 _).trans hs)) s rfl).le
  · intro s hs
    have hsl : s.re≤l := by
      have hrl := (le_max_right r (-l)).trans (le_max_right 1 (max r (-l)))
      linarith
    exact (hl s.re hsl s rfl).le

#print axioms denominator_exterior_lower_bounds
end QuantitativeArithmeticDilationLaplace
end
end

/-! ## QuantitativeArithmeticDilationLaplaceBoundedRigidityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex

/-- The full bounded-rectangle step for a continued Laplace transform.
There is no growth hypothesis on its entire pole-subtracted continuation:
the bounds are derived from the actual finite-interval numerator. -/
theorem pole_subtracted_constant (H : ℝ → ℂ) (hH : Continuous H)
    (L : ℝ) (hL : 0<L) (d : ℕ) (a : ℕ → ℂ) (h0 : a 0≠0) (hd : a d≠0)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ)
    (heq : ∀ s : ℂ, s≠0 →
      (recurrencePolynomial d a).eval (exp (-(L:ℂ)*s))*(F s+c/s)=numerator H L d a s) :
    ∀ s : ℂ, F s=F 0 := by
  obtain ⟨R,hR,hr,hl⟩ := denominator_exterior_lower_bounds L hL d a h0 hd
  obtain ⟨C,_hC,hEr,hEl⟩ := numerator_exterior_bounds H hH L hL.le d a
  obtain ⟨C₁,hE⟩ := numerator_strip_bound H hH L hL.le d a R (by linarith)
  have hδ0 : 0<‖a 0‖/2 := half_pos (norm_pos_iff.mpr h0)
  have hδd : 0<‖a d‖/2 := half_pos (norm_pos_iff.mpr hd)
  apply QuantitativeArithmeticDilationRectangles.constant_of_polynomial_denominator hF
    (recurrencePolynomial d a) (recurrencePolynomial_ne_zero d a h0) c L R
    (max (C/(‖a 0‖/2)) (C/(‖a d‖/2))+‖c‖) C₁ hL (by linarith) heq
  · intro s hs
    have hsn : 1≤‖s‖ := hR.trans (hs.trans (abs_re_le_norm s))
    have hs0 : s≠0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hsn)
    have hp : ‖c/s‖≤‖c‖ := by
      rw [norm_div]
      exact div_le_self (norm_nonneg _) hsn
    have hJ : ‖F s+c/s‖≤max (C/(‖a 0‖/2)) (C/(‖a d‖/2)) := by
      rcases le_abs.mp hs with hleft | hright
      · have hb : ‖F s+c/s‖≤C/(‖a 0‖/2) := by
          apply (le_div_iff₀ hδ0).mpr
          calc
            ‖F s+c/s‖*(‖a 0‖/2) ≤
                ‖F s+c/s‖*‖(recurrencePolynomial d a).eval (exp (-(L:ℂ)*s))‖ :=
              mul_le_mul_of_nonneg_left (hr s hleft) (norm_nonneg _)
            _ = ‖numerator H L d a s‖ := by rw [mul_comm,← norm_mul,heq s hs0]
            _ ≤ C := hEr s (by linarith)
        exact hb.trans (le_max_left _ _)
      · have hb : ‖F s+c/s‖≤C/(‖a d‖/2) := by
          apply (le_div_iff₀ hδd).mpr
          calc
            ‖F s+c/s‖*(‖a d‖/2) ≤
                ‖F s+c/s‖*‖exp (s*((d:ℝ)*L:ℝ))*
                  (recurrencePolynomial d a).eval (exp (-(L:ℂ)*s))‖ :=
              mul_le_mul_of_nonneg_left (hl s (by linarith)) (norm_nonneg _)
            _ = ‖exp (s*((d:ℝ)*L:ℝ))*numerator H L d a s‖ := by
              rw [mul_comm,← norm_mul,mul_assoc,heq s hs0]
            _ ≤ C := hEl s (by linarith)
        exact hb.trans (le_max_right _ _)
    calc
      ‖F s‖ = ‖(F s+c/s)-c/s‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖F s+c/s‖+‖c/s‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hJ hp
  · exact hE

#print axioms pole_subtracted_constant
end QuantitativeArithmeticDilationLaplace
end
end

/-! ## QuantitativeArithmeticDilationLaplaceContinuationIdentityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex MeasureTheory Set Filter
open scoped Topology

/-- Multiplication by s removes the sole possible pole before applying
the identity theorem. Only the initial integral identity is assumed. -/
theorem continued_recurrence_identity (H : ℝ → ℂ) (hH : Continuous H)
    (L : ℝ) (hL : 0≤L) (d : ℕ) (a : ℕ → ℂ)
    (hrec : ∀ t : ℝ, ∑ j∈Finset.range (d+1), a j*H (t+(j:ℝ)*L)=0)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) (R : ℝ) (hR : R<0)
    (hconv : ∀ s : ℂ, s.re<R → IntegrableOn (fun t : ℝ => H t*exp (s*(t:ℂ))) (Ioi 0))
    (hinit : ∀ s : ℂ, s.re<R → transform H s=F s+c/s) :
    ∀ s : ℂ, s≠0 →
      (recurrencePolynomial d a).eval (exp (-(L:ℂ)*s))*(F s+c/s)=numerator H L d a s := by
  let D : ℂ → ℂ := fun s => (recurrencePolynomial d a).eval (exp (-(L:ℂ)*s))
  let G : ℂ → ℂ := fun s => D s*(s*F s+c)
  let E : ℂ → ℂ := fun s => s*numerator H L d a s
  have hD : Differentiable ℂ D := by dsimp [D]; fun_prop
  have hG : Differentiable ℂ G :=
    hD.mul ((differentiable_id.mul hF).add (differentiable_const c))
  have hE : Differentiable ℂ E := differentiable_id.mul (numerator_entire H hH L d a)
  have hloc : G =ᶠ[𝓝 ((R-1:ℝ):ℂ)] E := by
    have hnear : ∀ᶠ s in 𝓝 ((R-1:ℝ):ℂ), s.re<R :=
      (continuous_re.tendsto _).eventually (gt_mem_nhds (by simp))
    filter_upwards [hnear] with s hs
    have hs0 : s≠0 := by intro h; simp only [h,zero_re] at hs; linarith
    have he := polynomial_identity H s L hL d a (hconv s hs) hrec
    rw [hinit s hs] at he
    dsimp [G,E,D]
    calc
      _ = s*((recurrencePolynomial d a).eval (exp (-(L:ℂ)*s))*(F s+c/s)) := by
        field_simp
      _ = _ := by rw [he]
  have hall : G=E := (hG.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hE.differentiableOn.analyticOnNhd isOpen_univ) hloc
  intro s hs
  have he := congrFun hall s
  dsimp [G,E,D] at he
  apply (mul_left_cancel₀ hs)
  calc
    s*((recurrencePolynomial d a).eval (exp (-(L:ℂ)*s))*(F s+c/s)) =
        (recurrencePolynomial d a).eval (exp (-(L:ℂ)*s))*(s*F s+c) := by
      field_simp
    _ = _ := he

theorem constant_of_recurrence_continuation (H : ℝ → ℂ) (hH : Continuous H)
    (L : ℝ) (hL : 0<L) (d : ℕ) (a : ℕ → ℂ) (h0 : a 0≠0) (hd : a d≠0)
    (hrec : ∀ t : ℝ, ∑ j∈Finset.range (d+1), a j*H (t+(j:ℝ)*L)=0)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) (R : ℝ) (hR : R<0)
    (hconv : ∀ s : ℂ, s.re<R → IntegrableOn (fun t : ℝ => H t*exp (s*(t:ℂ))) (Ioi 0))
    (hinit : ∀ s : ℂ, s.re<R → transform H s=F s+c/s) :
    ∀ s : ℂ, F s=F 0 :=
  pole_subtracted_constant H hH L hL d a h0 hd F hF c
    (continued_recurrence_identity H hH L hL.le d a hrec F hF c R hR hconv hinit)

#print axioms continued_recurrence_identity
#print axioms constant_of_recurrence_continuation
end QuantitativeArithmeticDilationLaplace
end
end

/-! ## QuantitativeArithmeticDilationLaplaceDecayV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex MeasureTheory Set Filter
open scoped Topology

theorem real_left_sequence (σ : ℝ) :
    Tendsto (fun n : ℕ => σ-(n:ℝ)) atTop atBot := by
  apply tendsto_atBot.mpr
  intro b
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
    (eventually_ge_atTop (σ-b))
  filter_upwards [hn] with n hn
  linarith

/-- Absolute convergence on one line already forces decay far to its left;
no uniform bound on the original function is needed. -/
theorem transform_tendsto_zero (H : ℝ → ℂ) (hH : Continuous H) (σ : ℝ)
    (hconv : IntegrableOn (fun t : ℝ => H t*exp ((σ:ℂ)*(t:ℂ))) (Ioi 0)) :
    Tendsto (fun n : ℕ => transform H ((σ-(n:ℝ):ℝ):ℂ)) atTop (𝓝 0) := by
  let Fn : ℕ → ℝ → ℂ := fun n t => H t*exp (((σ-(n:ℝ):ℝ):ℂ)*(t:ℂ))
  have hmeas (n : ℕ) : AEStronglyMeasurable (Fn n) (volume.restrict (Ioi 0)) := by
    have hc : Continuous (Fn n) := by dsimp [Fn]; fun_prop
    exact hc.aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      ‖Fn n t‖≤‖H t*exp ((σ:ℂ)*(t:ℂ))‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp [Fn]
    simp only [norm_mul,norm_exp,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have hn := Nat.cast_nonneg (α := ℝ) n
    have ht' : 0<t := ht
    nlinarith
  have hl : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      Tendsto (fun n => Fn n t) atTop (𝓝 (0:ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have he : Tendsto (fun n : ℕ => exp (((σ-(n:ℝ):ℝ):ℂ)*(t:ℂ))) atTop (𝓝 0) := by
      apply tendsto_exp_nhds_zero_iff.mpr
      simpa only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero] using
        (tendsto_mul_const_atBot_of_pos (show 0<t from ht)).mpr (real_left_sequence σ)
    simpa only [Fn,mul_zero] using he.const_mul (H t)
  have hi := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0:ℝ))) (f := fun _ => (0:ℂ))
    (fun t => ‖H t*exp ((σ:ℂ)*(t:ℂ))‖) hmeas hconv.norm hb hl
  simpa only [transform,Fn,integral_zero] using hi

theorem polar_tendsto_zero (c : ℂ) (σ : ℝ) :
    Tendsto (fun n : ℕ => c/((σ-(n:ℝ):ℝ):ℂ)) atTop (𝓝 0) := by
  have hi := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_inv_atBot_zero.comp (real_left_sequence σ))
  simpa only [Function.comp_def,ofReal_zero,ofReal_inv,mul_zero,div_eq_mul_inv] using hi.const_mul c

#print axioms transform_tendsto_zero
#print axioms polar_tendsto_zero
end QuantitativeArithmeticDilationLaplace
end
end

/-! ## QuantitativeArithmeticDilationLaplacePurePoleV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex MeasureTheory Set Filter
open scoped Topology

/-- The recurrence, a possible simple pole at zero, and the original
Laplace integral force the entire part of its continuation to vanish. -/
theorem pole_subtracted_zero (H : ℝ → ℂ) (hH : Continuous H)
    (L : ℝ) (hL : 0<L) (d : ℕ) (a : ℕ → ℂ) (h0 : a 0≠0) (hd : a d≠0)
    (hrec : ∀ t : ℝ, ∑ j∈Finset.range (d+1), a j*H (t+(j:ℝ)*L)=0)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) (R : ℝ) (hR : R<0)
    (hconv : ∀ s : ℂ, s.re<R → IntegrableOn (fun t : ℝ => H t*exp (s*(t:ℂ))) (Ioi 0))
    (hinit : ∀ s : ℂ, s.re<R → transform H s=F s+c/s) :
    ∀ s : ℂ, F s=0 := by
  have hconst := constant_of_recurrence_continuation H hH L hL d a h0 hd hrec F hF c R hR hconv hinit
  have hσ : ((R-1:ℝ):ℂ).re<R := by simp
  have hdec := transform_tendsto_zero H hH (R-1) (hconv _ hσ)
  have heq : (fun n : ℕ => transform H (((R-1)-(n:ℝ):ℝ):ℂ))=
      (fun n : ℕ => F 0+c/(((R-1)-(n:ℝ):ℝ):ℂ)) := by
    funext n
    rw [hinit _ (by simp only [ofReal_re]; have hn := Nat.cast_nonneg (α := ℝ) n; linarith),hconst]
  rw [heq] at hdec
  have hlim : Tendsto (fun n : ℕ => F 0+c/(((R-1)-(n:ℝ):ℝ):ℂ)) atTop (𝓝 (F 0)) := by
    simpa only [add_zero] using (tendsto_const_nhds.add (polar_tendsto_zero c (R-1)))
  have hz : F 0=0 := tendsto_nhds_unique hlim hdec
  exact fun s => (hconst s).trans hz

#print axioms pole_subtracted_zero
end QuantitativeArithmeticDilationLaplace
end
end

/-! ## QuantitativeArithmeticDilationLaplaceUniquenessV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex MeasureTheory Set Filter
open scoped Topology FourierTransform

def positiveWeight (H : ℝ → ℂ) (σ : ℝ) : ℝ → ℂ :=
  (Ioi 0).indicator (fun t => H t*exp ((σ:ℂ)*(t:ℂ)))

theorem fourier_positiveWeight (H : ℝ → ℂ) (σ ξ : ℝ) :
    𝓕 (positiveWeight H σ) ξ=transform H ((σ:ℂ)-(2*Real.pi*ξ:ℝ)*I) := by
  rw [Real.fourier_real_eq_integral_exp_smul,transform,← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t∈Ioi (0:ℝ)
  · simp only [positiveWeight,indicator_of_mem ht,smul_eq_mul]
    rw [mul_left_comm,← exp_add]
    congr 1
    push_cast
    ring
  · simp only [positiveWeight,indicator_of_notMem ht,smul_zero]

/-- Uniqueness on a single convergent vertical line, obtained from Fourier
inversion of the zero extension to the negative half-line. -/
theorem zero_of_transform_line (H : ℝ → ℂ) (σ : ℝ)
    (hconv : IntegrableOn (fun t : ℝ => H t*exp ((σ:ℂ)*(t:ℂ))) (Ioi 0))
    (hz : ∀ ξ : ℝ, transform H ((σ:ℂ)-(2*Real.pi*ξ:ℝ)*I)=0)
    {t : ℝ} (ht : 0<t) (hH : ContinuousAt H t) : H t=0 := by
  have hW : Integrable (positiveWeight H σ) := hconv.integrable_indicator measurableSet_Ioi
  have hfour : 𝓕 (positiveWeight H σ)=(0 : ℝ → ℂ) := by
    funext ξ
    exact (fourier_positiveWeight H σ ξ).trans (hz ξ)
  have hfi : Integrable (𝓕 (positiveWeight H σ)) := by rw [hfour]; exact integrable_zero _ _ _
  have hcont : ContinuousAt (positiveWeight H σ) t := by
    have hc : ContinuousAt (fun x : ℝ => H x*exp ((σ:ℂ)*(x:ℂ))) t := by fun_prop
    apply hc.congr
    filter_upwards [Ioi_mem_nhds ht] with x hx
    simp only [positiveWeight,indicator_of_mem hx]
  have he := hW.fourierInv_fourier_eq hfi hcont
  rw [hfour,Real.fourierInv_eq'] at he
  simp only [Pi.zero_apply,smul_zero,integral_zero] at he
  have hv : H t*exp ((σ:ℂ)*(t:ℂ))=0 := by
    simpa only [positiveWeight,Pi.zero_apply,
      indicator_of_mem (show t∈Ioi (0:ℝ) from ht)] using he.symm
  exact (mul_eq_zero.mp hv).resolve_right (exp_ne_zero _)

#print axioms fourier_positiveWeight
#print axioms zero_of_transform_line
end QuantitativeArithmeticDilationLaplace
end
end

/-! ## QuantitativeArithmeticDilationLaplaceRigidityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex MeasureTheory Set

theorem transform_add_const (H : ℝ → ℂ) (c s : ℂ) (hs : s.re<0)
    (hH : IntegrableOn (fun t : ℝ => H t*exp (s*(t:ℂ))) (Ioi 0)) :
    transform (fun t => H t+c) s=transform H s-c/s := by
  unfold transform
  simp_rw [add_mul]
  rw [integral_add hH ((integrableOn_exp_mul_complex_Ioi hs 0).const_mul c),
    integral_const_mul,integral_exp_mul_complex_Ioi hs 0]
  simp only [ofReal_zero,mul_zero,exp_zero,neg_div,one_div]
  ring

/-- Constant-coefficient translation rigidity, with a possible simple
Laplace pole at zero. No vertical growth or spectral-decomposition
hypothesis is imposed. The continuation is written as an entire function
plus its polar part; proving this pole description is a separate input. -/
theorem constant_of_pole_subtracted_continuation (H : ℝ → ℂ) (hH : Continuous H)
    (L : ℝ) (hL : 0<L) (d : ℕ) (a : ℕ → ℂ) (h0 : a 0≠0) (hd : a d≠0)
    (hrec : ∀ t : ℝ, ∑ j∈Finset.range (d+1), a j*H (t+(j:ℝ)*L)=0)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) (R : ℝ) (hR : R<0)
    (hconv : ∀ s : ℂ, s.re<R → IntegrableOn (fun t : ℝ => H t*exp (s*(t:ℂ))) (Ioi 0))
    (hinit : ∀ s : ℂ, s.re<R → transform H s=F s+c/s) :
    (∀ t : ℝ, H t=-c) ∧ (∑ j∈Finset.range (d+1), a j)*c=0 := by
  have hzero := pole_subtracted_zero H hH L hL d a h0 hd hrec F hF c R hR hconv hinit
  let σ := R-1
  have hσ : σ<R := by dsimp [σ]; linarith
  have hσ0 : σ<0 := hσ.trans hR
  have hG : IntegrableOn (fun t : ℝ => (H t+c)*exp ((σ:ℂ)*(t:ℂ))) (Ioi 0) := by
    have hi := (hconv (σ:ℂ) hσ).add
      ((integrableOn_exp_mul_complex_Ioi (a := (σ:ℂ)) hσ0 0).const_mul c)
    change Integrable _ _ at hi ⊢
    convert hi using 1
    ext t
    simp only [Pi.add_apply,add_mul]
  have hz (ξ : ℝ) : transform (fun t => H t+c) ((σ:ℂ)-(2*Real.pi*ξ:ℝ)*I)=0 := by
    let s : ℂ := (σ:ℂ)-(2*Real.pi*ξ:ℝ)*I
    have hsre : s.re=σ := by simp [s,mul_re]
    have hsR : s.re<R := hsre ▸ hσ
    change transform (fun t => H t+c) s=0
    rw [transform_add_const H c s (hsre ▸ hσ0) (hconv s hsR),hinit s hsR,hzero,zero_add,sub_self]
  have hpos (t : ℝ) (ht : 0<t) : H t=-c := by
    have he := zero_of_transform_line (fun t => H t+c) σ hG hz ht
      ((hH.add continuous_const).continuousAt)
    exact add_eq_zero_iff_eq_neg.mp he
  have hclosed : IsClosed {t : ℝ | H t=-c} := isClosed_eq hH continuous_const
  have hnonneg : ∀ t : ℝ, 0≤t → H t=-c := by
    intro t ht
    apply closure_minimal (s := Ioi (0:ℝ)) (fun x hx => hpos x hx) hclosed
    simpa only [closure_Ioi,mem_Ici] using ht
  obtain ⟨hall,hc⟩ := QuantitativeArithmeticDilationRecurrence.constant_of_nonneg
    hL d a h0 (-c) hrec hnonneg
  exact ⟨hall,by simpa only [mul_neg,neg_eq_zero] using hc⟩

#print axioms constant_of_pole_subtracted_continuation
end QuantitativeArithmeticDilationLaplace
end
end

/-! ## QuantitativeArithmeticDilationMeromorphicRigidityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex MeasureTheory Set

/-- The one-sided Laplace pole criterion for a translation recurrence.
This states the analytic endgame directly in terms of the meromorphic
continuation, without an assumed entire remainder or growth bounds on J. -/
theorem constant_of_meromorphic_continuation (H : ℝ → ℂ) (hH : Continuous H)
    (L : ℝ) (hL : 0<L) (d : ℕ) (a : ℕ → ℂ) (h0 : a 0≠0) (hd : a d≠0)
    (hrec : ∀ t : ℝ, ∑ j∈Finset.range (d+1), a j*H (t+(j:ℝ)*L)=0)
    (J : ℂ → ℂ) (hJ0 : MeromorphicAt J 0)
    (hJa : ∀ z : ℂ, z≠0 → AnalyticAt ℂ J z)
    (hord : (-1:WithTop ℤ)≤meromorphicOrderAt J 0)
    (R : ℝ) (hR : R<0)
    (hconv : ∀ s : ℂ, s.re<R → IntegrableOn (fun t : ℝ => H t*exp (s*(t:ℂ))) (Ioi 0))
    (hinit : ∀ s : ℂ, s.re<R → transform H s=J s) :
    ∃ C : ℂ, (∀ t : ℝ, H t=C) ∧ (∑ j∈Finset.range (d+1), a j)*C=0 := by
  obtain ⟨c,F,hF,hJF⟩ := QuantitativeArithmeticSimplePoleSubtraction.exists_entire_remainder J hJ0 hJa hord
  have hi (s : ℂ) (hs : s.re<R) : transform H s=F s+c/s := by
    have hs0 : s≠0 := by intro hh; simp only [hh,zero_re] at hs; linarith
    exact (hinit s hs).trans (hJF s hs0)
  obtain ⟨he,hc⟩ := constant_of_pole_subtracted_continuation H hH L hL d a h0 hd hrec
    F hF c R hR hconv hi
  exact ⟨-c,he,by rw [mul_neg,hc,neg_zero]⟩

theorem zero_of_meromorphic_continuation (H : ℝ → ℂ) (hH : Continuous H)
    (L : ℝ) (hL : 0<L) (d : ℕ) (a : ℕ → ℂ) (h0 : a 0≠0) (hd : a d≠0)
    (hone : (∑ j∈Finset.range (d+1), a j)≠0)
    (hrec : ∀ t : ℝ, ∑ j∈Finset.range (d+1), a j*H (t+(j:ℝ)*L)=0)
    (J : ℂ → ℂ) (hJ0 : MeromorphicAt J 0)
    (hJa : ∀ z : ℂ, z≠0 → AnalyticAt ℂ J z)
    (hord : (-1:WithTop ℤ)≤meromorphicOrderAt J 0)
    (R : ℝ) (hR : R<0)
    (hconv : ∀ s : ℂ, s.re<R → IntegrableOn (fun t : ℝ => H t*exp (s*(t:ℂ))) (Ioi 0))
    (hinit : ∀ s : ℂ, s.re<R → transform H s=J s) :
    ∀ t : ℝ, H t=0 := by
  obtain ⟨C,he,hc⟩ := constant_of_meromorphic_continuation H hH L hL d a h0 hd hrec
    J hJ0 hJa hord R hR hconv hinit
  have hz : C=0 := (mul_eq_zero.mp hc).resolve_left hone
  exact fun t => (he t).trans hz

#print axioms constant_of_meromorphic_continuation
#print axioms zero_of_meromorphic_continuation
end QuantitativeArithmeticDilationLaplace
end
end

/-! ## QuantitativeArithmeticDilationGrowthRigidityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationLaplace
open Complex MeasureTheory Set

theorem exponential_growth_integrable (H : ℝ → ℂ) (hH : Continuous H) (C B : ℝ)
    (hg : ∀ t : ℝ, 0≤t → ‖H t‖≤C*Real.exp (B*t))
    (s : ℂ) (hs : s.re < -B) :
    IntegrableOn (fun t : ℝ => H t*exp (s*(t:ℂ))) (Ioi 0) := by
  have he : IntegrableOn (fun t : ℝ => C*Real.exp ((B+s.re)*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : B+s.re<0) 0).const_mul C
  have hm : AEStronglyMeasurable (fun t : ℝ => H t*exp (s*(t:ℂ)))
      (volume.restrict (Ioi 0)) := by
    have hc : Continuous (fun t : ℝ => H t*exp (s*(t:ℂ))) := by fun_prop
    exact hc.aestronglyMeasurable
  apply he.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : 0<t := ht
  simp only [norm_mul,norm_exp,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
  calc
    ‖H t‖*Real.exp (s.re*t) ≤ (C*Real.exp (B*t))*Real.exp (s.re*t) :=
      mul_le_mul_of_nonneg_right (hg t ht'.le) (Real.exp_pos _).le
    _ = C*Real.exp ((B+s.re)*t) := by rw [mul_assoc,← Real.exp_add,add_mul]

/-- The dilation/Laplace lemma under the literal exponential-growth
hypothesis: convergence is proved, rather than added to the assumptions. -/
theorem constant_of_exponential_growth (H : ℝ → ℂ) (hH : Continuous H) (C B : ℝ)
    (hg : ∀ t : ℝ, 0≤t → ‖H t‖≤C*Real.exp (B*t))
    (L : ℝ) (hL : 0<L) (d : ℕ) (a : ℕ → ℂ) (h0 : a 0≠0) (hd : a d≠0)
    (hrec : ∀ t : ℝ, ∑ j∈Finset.range (d+1), a j*H (t+(j:ℝ)*L)=0)
    (J : ℂ → ℂ) (hJ0 : MeromorphicAt J 0)
    (hJa : ∀ z : ℂ, z≠0 → AnalyticAt ℂ J z)
    (hord : (-1:WithTop ℤ)≤meromorphicOrderAt J 0)
    (R : ℝ) (hinit : ∀ s : ℂ, s.re<R → transform H s=J s) :
    ∃ K : ℂ, (∀ t : ℝ, H t=K) ∧ (∑ j∈Finset.range (d+1), a j)*K=0 := by
  let A : ℝ := min (-1) (min R (-B))
  have hA0 : A<0 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hAR : A≤R := (min_le_right _ _).trans (min_le_left _ _)
  have hAB : A≤-B := (min_le_right _ _).trans (min_le_right _ _)
  exact constant_of_meromorphic_continuation H hH L hL d a h0 hd hrec J hJ0 hJa hord A hA0
    (fun s hs => exponential_growth_integrable H hH C B hg s (hs.trans_le hAB))
    (fun s hs => hinit s (hs.trans_le hAR))

#print axioms exponential_growth_integrable
#print axioms constant_of_exponential_growth
end QuantitativeArithmeticDilationLaplace
end
end
