module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic

/-! Consolidated chapter: QuantitativeArithmeticDilationRectangles. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticDilationRectanglesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationRectangles
open Complex Set Filter Metric Bornology
open scoped Topology

/-- Bounds on the two exterior half-planes and arbitrarily high and low
horizontal segments suffice; no a priori growth in the intervening strip is
required. This is the maximum-modulus step in the dilation/Laplace argument. -/
theorem bound_from_rectangles {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (R C : ℝ) (hR : 0<R)
    (hout : ∀ z : ℂ, R≤|z.re| → ‖F z‖≤C)
    (hhor : ∀ y : ℝ, ∃ a b : ℝ, a<y ∧ y<b ∧
      ∀ z : ℂ, |z.re|≤R → (z.im=a ∨ z.im=b) → ‖F z‖≤C) :
    ∀ z : ℂ, ‖F z‖≤C := by
  intro z
  by_cases hz : R≤|z.re|
  · exact hout z hz
  have hz' : |z.re|<R := lt_of_not_ge hz
  obtain ⟨a,b,ha,hb,hboundary⟩ := hhor z.im
  have hab : a<b := lt_trans ha hb
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    ((isBounded_Ioo (-R) R).reProdIm (isBounded_Ioo a b)) hF.diffContOnCl
  · intro w hw
    rw [frontier_reProdIm,closure_Ioo (neg_lt_self hR).ne,frontier_Ioo hab,
      closure_Ioo hab.ne,frontier_Ioo (neg_lt_self hR)] at hw
    rcases hw with hw | hw
    · exact hboundary w (abs_le.mpr hw.1) hw.2
    · apply hout w
      rcases hw.1 with h | h
      · rw [h,abs_neg,abs_of_pos hR]
      · rw [h,abs_of_pos hR]
  · rw [closure_reProdIm,closure_Ioo (neg_lt_self hR).ne,closure_Ioo hab.ne]
    exact ⟨abs_le.mp hz'.le,ha.le,hb.le⟩

theorem constant_from_rectangles {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (R C : ℝ) (hR : 0<R)
    (hout : ∀ z : ℂ, R≤|z.re| → ‖F z‖≤C)
    (hhor : ∀ y : ℝ, ∃ a b : ℝ, a<y ∧ y<b ∧
      ∀ z : ℂ, |z.re|≤R → (z.im=a ∨ z.im=b) → ‖F z‖≤C) :
    ∀ z : ℂ, F z=F 0 := by
  have hbound := bound_from_rectangles hF R C hR hout hhor
  have hbounded : Bornology.IsBounded (Set.range F) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C,?_⟩
    rintro w ⟨z,rfl⟩
    exact hbound z
  exact fun z => hF.apply_eq_apply_of_bounded hbounded z 0

#print axioms bound_from_rectangles
#print axioms constant_from_rectangles
end QuantitativeArithmeticDilationRectangles
end
end

/-! ## QuantitativeArithmeticDilationPeriodicDenominatorV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationRectangles
open Complex Set

/-- A periodic denominator only needs a lower bound on one horizontal
segment. Its translates supply the expanding rectangle boundaries. -/
theorem constant_of_periodic_denominator {F D E : ℂ → ℂ}
    (hF : Differentiable ℂ F) (R T t C₀ C₁ δ : ℝ)
    (hR : 0<R) (hT : 0<T) (hδ : 0<δ)
    (hperiodic : Function.Periodic D ((T:ℂ)*I))
    (heq : ∀ z, D z*F z=E z)
    (hout : ∀ z : ℂ, R≤|z.re| → ‖F z‖≤C₀)
    (hE : ∀ z : ℂ, |z.re|≤R → ‖E z‖≤C₁)
    (hD : ∀ z : ℂ, |z.re|≤R → z.im=t → δ≤‖D z‖) :
    ∀ z : ℂ, F z=F 0 := by
  apply constant_from_rectangles hF R (max C₀ (C₁/δ)) hR
  · intro z hz
    exact le_trans (hout z hz) (le_max_left _ _)
  · intro y
    obtain ⟨a,ha⟩ := exists_int_lt ((y-t)/T)
    obtain ⟨b,hb⟩ := exists_int_gt ((y-t)/T)
    refine ⟨t+(a:ℝ)*T,t+(b:ℝ)*T,?_,?_,?_⟩
    · have hh := (lt_div_iff₀ hT).mp ha
      linarith
    · have hh := (div_lt_iff₀ hT).mp hb
      linarith
    · intro z hz hi
      have hline (n : ℤ) (hn : z.im=t+(n:ℝ)*T) : ‖F z‖≤C₁/δ := by
        let w : ℂ := z-(n:ℂ)*((T:ℂ)*I)
        have hwre : w.re=z.re := by simp [w,mul_re,mul_im]
        have hwim : w.im=t := by simp [w,mul_re,mul_im,hn]
        have hd : δ≤‖D z‖ := by
          have hh := hD w (by simpa only [hwre] using hz) hwim
          simpa only [w,hperiodic.sub_int_mul_eq] using hh
        apply (le_div_iff₀ hδ).mpr
        calc
          ‖F z‖*δ ≤ ‖F z‖*‖D z‖ := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
          _ = ‖E z‖ := by rw [mul_comm,← norm_mul,heq]
          _ ≤ C₁ := hE z hz
      apply le_trans _ (le_max_right _ _)
      rcases hi with hi | hi
      · exact hline a hi
      · exact hline b hi

#print axioms constant_of_periodic_denominator
end QuantitativeArithmeticDilationRectangles
end
end

/-! ## QuantitativeArithmeticDilationPolarRectanglesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationRectangles
open Complex Set

/-- The rectangle argument after subtracting a possible simple pole.
No vertical growth condition on the continued transform is assumed:
the periodic denominator controls horizontal segments away from zero. -/
theorem constant_of_polar_periodic_denominator {F D E : ℂ → ℂ}
    (hF : Differentiable ℂ F) (c : ℂ) (R T t C₀ C₁ δ : ℝ)
    (hR : 0<R) (hT : 0<T) (hδ : 0<δ)
    (hperiodic : Function.Periodic D ((T:ℂ)*I))
    (heq : ∀ z : ℂ, z≠0 → D z*(F z+c/z)=E z)
    (hout : ∀ z : ℂ, R≤|z.re| → ‖F z‖≤C₀)
    (hE : ∀ z : ℂ, |z.re|≤R → ‖E z‖≤C₁)
    (hD : ∀ z : ℂ, |z.re|≤R → z.im=t → δ≤‖D z‖) :
    ∀ z : ℂ, F z=F 0 := by
  apply constant_from_rectangles hF R (max C₀ (C₁/δ+‖c‖)) hR
  · intro z hz
    exact le_trans (hout z hz) (le_max_left _ _)
  · intro y
    obtain ⟨a,ha⟩ := exists_int_lt ((min y (-1)-t)/T)
    obtain ⟨b,hb⟩ := exists_int_gt ((max y 1-t)/T)
    have ha' : t+(a:ℝ)*T<min y (-1) := by
      have hh := (lt_div_iff₀ hT).mp ha
      linarith
    have hb' : max y 1<t+(b:ℝ)*T := by
      have hh := (div_lt_iff₀ hT).mp hb
      linarith
    refine ⟨t+(a:ℝ)*T,t+(b:ℝ)*T,lt_of_lt_of_le ha' (min_le_left _ _),
      lt_of_le_of_lt (le_max_left _ _) hb',?_⟩
    intro z hz hi
    have hline (n : ℤ) (hn : z.im=t+(n:ℝ)*T) (hi1 : 1≤|z.im|) :
        ‖F z‖≤C₁/δ+‖c‖ := by
      let w : ℂ := z-(n:ℂ)*((T:ℂ)*I)
      have hwre : w.re=z.re := by simp [w,mul_re,mul_im]
      have hwim : w.im=t := by simp [w,mul_re,mul_im,hn]
      have hd : δ≤‖D z‖ := by
        have hh := hD w (by simpa only [hwre] using hz) hwim
        simpa only [w,hperiodic.sub_int_mul_eq] using hh
      have hnz : 1≤‖z‖ := hi1.trans (abs_im_le_norm z)
      have hz0 : z≠0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hnz)
      have hmain : ‖F z+c/z‖≤C₁/δ := by
        apply (le_div_iff₀ hδ).mpr
        calc
          ‖F z+c/z‖*δ ≤ ‖F z+c/z‖*‖D z‖ :=
            mul_le_mul_of_nonneg_left hd (norm_nonneg _)
          _ = ‖E z‖ := by rw [mul_comm,← norm_mul,heq z hz0]
          _ ≤ C₁ := hE z hz
      have hpolar : ‖c/z‖≤‖c‖ := by
        rw [norm_div]
        exact div_le_self (norm_nonneg _) hnz
      calc
        ‖F z‖ = ‖(F z+c/z)-c/z‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖F z+c/z‖+‖c/z‖ := norm_sub_le _ _
        _ ≤ C₁/δ+‖c‖ := add_le_add hmain hpolar
    apply le_trans _ (le_max_right _ _)
    rcases hi with hi | hi
    · apply hline a hi
      have hh := lt_of_lt_of_le ha' (min_le_right y (-1))
      have haabs := neg_le_abs z.im
      linarith
    · apply hline b hi
      have hh := lt_of_le_of_lt (le_max_right y 1) hb'
      have hbabs := le_abs_self z.im
      linarith

#print axioms constant_of_polar_periodic_denominator
end QuantitativeArithmeticDilationRectangles
end
end

/-! ## QuantitativeArithmeticDilationPolynomialLineV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationRectangles
open Complex Set

theorem polynomial_exponential_periodic (P : Polynomial ℂ) (L : ℝ) (hL : L≠0) :
    Function.Periodic (fun z : ℂ => P.eval (exp (-(L:ℂ)*z)))
      (((2*Real.pi/L:ℝ):ℂ)*I) := by
  intro z
  apply congrArg P.eval
  have he : -(L:ℂ)*(z+((2*Real.pi/L:ℝ):ℂ)*I)=
      -(L:ℂ)*z-(2*Real.pi:ℂ)*I := by
    have hLc : (L:ℂ)≠0 := by exact_mod_cast hL
    push_cast
    field_simp [hLc]
    ring
  rw [he]
  exact exp_periodic.sub_eq _

/-- A nonzero polynomial in an exponential has a horizontal line avoiding
all its zeros, with a uniform positive lower bound on any fixed strip. -/
theorem polynomial_exponential_horizontal_lower_bound (P : Polynomial ℂ)
    (hP : P≠0) (L R : ℝ) (hL : 0<L) :
    ∃ t δ : ℝ, 0<δ ∧ ∀ z : ℂ, |z.re|≤R → z.im=t →
      δ≤‖P.eval (exp (-(L:ℂ)*z))‖ := by
  obtain ⟨θ,hθ,havoid⟩ :=
    (Ioo_infinite (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos])).exists_notMem_finset
      (P.roots.toFinset.image Complex.arg)
  let t : ℝ := -θ/L
  have hnonzero (z : ℂ) (hz : z.im=t) : P.eval (exp (-(L:ℂ)*z))≠0 := by
    intro hzero
    have him : (-(L:ℂ)*z).im=θ := by
      simp [mul_im,hz,t]
      field_simp [ne_of_gt hL]
    have harg : (exp (-(L:ℂ)*z)).arg=θ := by
      rw [arg_exp,him]
      apply (toIocMod_eq_self Real.two_pi_pos).mpr
      exact ⟨hθ.1,by linarith [hθ.2]⟩
    apply havoid
    apply Finset.mem_image.mpr
    refine ⟨exp (-(L:ℂ)*z),?_,harg⟩
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr hzero)
  let g : ℝ → ℝ := fun x => ‖P.eval (exp (-(L:ℂ)*((x:ℂ)+(t:ℂ)*I)))‖
  have hg : Continuous g := by dsimp [g]; fun_prop
  obtain ⟨δ,hδ,hbound⟩ :=
    (isCompact_Icc : IsCompact (Icc (-R) R)).exists_forall_le' hg.continuousOn
      (fun x _ => norm_pos_iff.mpr (hnonzero ((x:ℂ)+(t:ℂ)*I) (by simp)))
  refine ⟨t,δ,hδ,?_⟩
  intro z hz ht
  have hzform : (z.re:ℂ)+(t:ℂ)*I=z := by
    apply Complex.ext <;> simp [ht]
  have hh := hbound z.re (abs_le.mp hz)
  simpa only [g,hzform] using hh

#print axioms polynomial_exponential_periodic
#print axioms polynomial_exponential_horizontal_lower_bound
end QuantitativeArithmeticDilationRectangles
end
end

/-! ## QuantitativeArithmeticDilationPolynomialRigidityV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationRectangles
open Complex

/-- The maximum-modulus part of the constant-coefficient dilation argument,
with the existence of a suitable horizontal boundary proved from the
polynomial denominator, rather than supplied as an extra hypothesis. -/
theorem constant_of_polynomial_denominator {F E : ℂ → ℂ}
    (hF : Differentiable ℂ F) (P : Polynomial ℂ) (hP : P≠0)
    (c : ℂ) (L R C₀ C₁ : ℝ) (hL : 0<L) (hR : 0<R)
    (heq : ∀ z : ℂ, z≠0 → P.eval (exp (-(L:ℂ)*z))*(F z+c/z)=E z)
    (hout : ∀ z : ℂ, R≤|z.re| → ‖F z‖≤C₀)
    (hE : ∀ z : ℂ, |z.re|≤R → ‖E z‖≤C₁) :
    ∀ z : ℂ, F z=F 0 := by
  obtain ⟨t,δ,hδ,hD⟩ := polynomial_exponential_horizontal_lower_bound P hP L R hL
  exact constant_of_polar_periodic_denominator hF c R (2*Real.pi/L) t C₀ C₁ δ
    hR (by positivity) hδ (polynomial_exponential_periodic P L (ne_of_gt hL))
    heq hout hE hD

#print axioms constant_of_polynomial_denominator
end QuantitativeArithmeticDilationRectangles
end
end
