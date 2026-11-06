module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.SpecialFunctions.Choose
public import SmallLevelTaylorRowCoefficientsV1
public import SmallLevelTaylorRowNormalizationV1

/-! Consolidated chapter: QuantitativeArithmeticTaylorLayerNormalization. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticTaylorLayerNormalizationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTaylorLayerNormalization
open Complex

/-- The lower-layer rescaling used in the full Taylor syzygy. -/
def scale (α : ℂ) (j : ℕ) : ℂ := I^j*(j.factorial:ℂ)*Ring.choose α j

@[simp] theorem scale_zero (α : ℂ) : scale α 0=1 := by
  simp [scale]

theorem scale_add (α : ℂ) (i n : ℕ) :
    scale α (i+n)=I^n*(n.factorial:ℂ)*Ring.choose (α-(i:ℂ)) n*scale α i := by
  have hc := Ring.choose_smul_choose α (Nat.le_add_right i n)
  simp only [nsmul_eq_mul,Nat.add_sub_cancel_left] at hc
  have hf : ((i+n).factorial:ℂ)=
      ((i+n).choose i:ℂ)*(i.factorial:ℂ)*(n.factorial:ℂ) := by
    have hh := (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i n)).symm
    simp only [Nat.add_sub_cancel_left] at hh
    exact_mod_cast hh
  unfold scale
  rw [pow_add,hf]
  calc
    _=I^i*I^n*(i.factorial:ℂ)*(n.factorial:ℂ)*
      (((i+n).choose i:ℂ)*Ring.choose α (i+n)) := by ring
    _=_ := by rw [hc]; ring

theorem scale_succ (α : ℂ) (j : ℕ) :
    scale α (j+1)=I*(α-(j:ℂ))*scale α j := by
  simpa using scale_add α j 1

theorem scale_analytic (j : ℕ) (α : ℂ) : AnalyticAt ℂ (fun z => scale z j) α := by
  induction j with
  | zero => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) α)
  | succ j ih =>
    simp_rw [scale_succ]
    exact (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).mul ih

theorem scale_nonzero_of_re_neg (α : ℂ) (hα : α.re<0) (j : ℕ) : scale α j≠0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [scale_succ]
    apply mul_ne_zero (mul_ne_zero I_ne_zero _) ih
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.natCast_re,Complex.zero_re] at hr
    have hj : (0:ℝ)≤j := Nat.cast_nonneg j
    linarith

/-- Dividing the row at layer i+n by its scale turns the n-step Taylor
coefficient into 1/n!, including the complex phase. -/
theorem normalized_coefficient (α : ℂ) (i n : ℕ) (h : scale α (i+n)≠0) :
    (I^n*Ring.choose (α-(i:ℂ)) n*scale α i)/scale α (i+n)=
      (1:ℂ)/(n.factorial:ℂ) := by
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply (div_eq_div_iff h hn).mpr
  rw [scale_add]
  ring

/-- At the remaining level27 resonance and weight at least four, all
lower-layer rescalings are analytic units. -/
theorem resonance_scale_nonzero (m : ℕ) (hm : 1<m) (j : ℕ) :
    scale (1-(m:ℂ)) j≠0 := by
  apply scale_nonzero_of_re_neg
  simp only [Complex.sub_re,Complex.one_re,Complex.natCast_re]
  have hh : (1:ℝ)<m := by exact_mod_cast hm
  linarith

#print axioms scale_add
#print axioms scale_analytic
#print axioms normalized_coefficient
#print axioms resonance_scale_nonzero
end QuantitativeArithmeticTaylorLayerNormalization
end
end

/-! ## QuantitativeArithmeticTaylorLayerScalarV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTaylorLayerNormalization
open Complex

theorem taylor_coefficient_identity (k i n : ℕ) (L r : ℝ) (η s : ℂ) :
    SmallLevelTaylor.taylorRowScalar k L r η n (s-((i+n:ℕ):ℂ))*
        scale (s-(k:ℂ)) i*(n.factorial:ℂ)=
      SmallLevelTaylor.taylorRowScalar k L r η 0 (s-((i+n:ℕ):ℂ))*
        ((L:ℂ)*(r:ℂ))^n*scale (s-(k:ℂ)) (i+n) := by
  unfold SmallLevelTaylor.taylorRowScalar
  simp only [pow_zero,Nat.cast_zero,add_zero,Ring.choose_zero_right,mul_one]
  rw [show s-((i+n:ℕ):ℂ)+(n:ℂ)-(k:ℂ)=(s-(k:ℂ))-(i:ℂ) by push_cast; ring]
  rw [scale_add]
  simp only [mul_pow]
  ring

theorem normalized_taylor_coefficient (k i n : ℕ) (L r : ℝ) (η s : ℂ)
    (h : scale (s-(k:ℂ)) (i+n)≠0) :
    SmallLevelTaylor.taylorRowScalar k L r η n (s-((i+n:ℕ):ℂ))*
        scale (s-(k:ℂ)) i/scale (s-(k:ℂ)) (i+n)=
      SmallLevelTaylor.taylorRowScalar k L r η 0 (s-((i+n:ℕ):ℂ))*
        ((L:ℂ)*(r:ℂ))^n/(n.factorial:ℂ) := by
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  exact (div_eq_div_iff h hn).mpr (taylor_coefficient_identity k i n L r η s)

theorem layer_scale_analytic (k j : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fun z => scale (z-(k:ℂ)) j) s :=
  (scale_analytic j (s-(k:ℂ))).comp (f:=fun z : ℂ => z-(k:ℂ))
    (analyticAt_id.sub analyticAt_const)

theorem original_resonance_scale_nonzero (m : ℕ) (hm : 1<m) (j : ℕ) :
    scale (((m:ℂ)+1)-((2*m:ℕ):ℂ)) j≠0 := by
  rw [show ((m:ℂ)+1)-((2*m:ℕ):ℂ)=1-(m:ℂ) by push_cast; ring]
  exact resonance_scale_nonzero m hm j

#print axioms normalized_taylor_coefficient
#print axioms layer_scale_analytic
#print axioms original_resonance_scale_nonzero
end QuantitativeArithmeticTaylorLayerNormalization
end
end

/-! ## QuantitativeArithmeticTaylorLayerUnitV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTaylorLayerNormalization
open Complex

/-- The finitely many layer denominators are also units on a sufficiently
far right initial half-plane. This does not assert uniformity over all orders. -/
theorem scale_nonzero_of_nat_lt_re (α : ℂ) (j : ℕ) (hj : (j:ℝ)<α.re) :
    scale α j≠0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [scale_succ]
    apply mul_ne_zero (mul_ne_zero I_ne_zero _) (ih (by exact lt_trans (by norm_num) hj))
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.sub_re,Complex.natCast_re,Complex.zero_re] at hr
    have hsucc : (j:ℝ)<(j+1:ℕ) := by exact_mod_cast Nat.lt_succ_self j
    linarith

theorem layer_scale_nonzero_on_initial_halfplane (k j : ℕ) (s : ℂ)
    (hs : (k:ℝ)+(j:ℝ)<s.re) : scale (s-(k:ℂ)) j≠0 := by
  apply scale_nonzero_of_nat_lt_re
  simp only [Complex.sub_re,Complex.natCast_re]
  linarith

theorem inverse_layer_scale_meromorphic (k j : ℕ) (s : ℂ) :
    MeromorphicAt (fun z : ℂ => (scale (z-(k:ℂ)) j)⁻¹) s :=
  (layer_scale_analytic k j s).meromorphicAt.inv

theorem inverse_layer_scale_analytic (k j : ℕ) (s : ℂ)
    (hs : scale (s-(k:ℂ)) j≠0) :
    AnalyticAt ℂ (fun z : ℂ => (scale (z-(k:ℂ)) j)⁻¹) s :=
  (layer_scale_analytic k j s).inv hs

#print axioms layer_scale_nonzero_on_initial_halfplane
#print axioms inverse_layer_scale_meromorphic
#print axioms inverse_layer_scale_analytic
end QuantitativeArithmeticTaylorLayerNormalization
end
end

/-! ## QuantitativeArithmeticTaylorLayerTermV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticTaylorLayerNormalization

/-- Lower Taylor layers are normalized only as functions on their initial
half-plane; this definition asserts no continuation of the individual twist. -/
def layerValue (F : ℂ→ℂ) (k d : ℕ) (s : ℂ) : ℂ :=
  F (s-(d:ℂ))/scale (s-(k:ℂ)) d

/-- The actual n-th Taylor term after dividing the source row by its layer
scale. This is the physical meaning of the factorial coefficients in the
four-layer sparse certificate. -/
theorem normalized_taylor_term (F : ℂ→ℂ) (k i n : ℕ) (L r : ℝ) (η s : ℂ)
    (hi : scale (s-(k:ℂ)) i≠0) (hin : scale (s-(k:ℂ)) (i+n)≠0) :
    SmallLevelTaylor.taylorRowScalar k L r η n (s-((i+n:ℕ):ℂ))*
        F (s-(i:ℂ))/scale (s-(k:ℂ)) (i+n)=
      (SmallLevelTaylor.taylorRowScalar k L r η 0 (s-((i+n:ℕ):ℂ))*
        ((L:ℂ)*(r:ℂ))^n/(n.factorial:ℂ))*layerValue F k i s := by
  rw [←normalized_taylor_coefficient k i n L r η s hin]
  unfold layerValue
  field_simp [hi]

@[simp] theorem layerValue_zero (F : ℂ→ℂ) (k : ℕ) (s : ℂ) :
    layerValue F k 0 s=F s := by simp [layerValue]

#print axioms normalized_taylor_term
end QuantitativeArithmeticTaylorLayerNormalization
end
end

/-! ## QuantitativeArithmeticTaylorLayerPhaseV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticTaylorLayerNormalization
open Complex

theorem normalized_phase_coefficient (α r : ℂ) (i n : ℕ)
    (h : scale α (i+n)≠0) :
    ((I*r)^n*Ring.choose (α-(i:ℂ)) n*scale α i)/scale α (i+n)=
      r^n/(n.factorial:ℂ) := by
  calc
    _=r^n*((I^n*Ring.choose (α-(i:ℂ)) n*scale α i)/scale α (i+n)) := by rw [mul_pow]; ring
    _=_ := by rw [normalized_coefficient α i n h]; ring

theorem normalized_phase_term (F : ℂ→ℂ) (k i n : ℕ) (M r s : ℂ)
    (hi : scale (s-(k:ℂ)) i≠0) (hin : scale (s-(k:ℂ)) (i+n)≠0) :
    (M*(I*r)^n*Ring.choose (s-(k:ℂ)-(i:ℂ)) n)*F (s-(i:ℂ))/scale (s-(k:ℂ)) (i+n)=
      (M*r^n/(n.factorial:ℂ))*layerValue F k i s := by
  have h := normalized_phase_coefficient (s-(k:ℂ)) r i n hin
  calc
    _=M*(((I*r)^n*Ring.choose (s-(k:ℂ)-(i:ℂ)) n*scale (s-(k:ℂ)) i)/scale (s-(k:ℂ)) (i+n))*
        (F (s-(i:ℂ))/scale (s-(k:ℂ)) i) := by field_simp [hi]
    _=_ := by rw [h]; unfold layerValue; ring

#print axioms normalized_phase_term
end QuantitativeArithmeticTaylorLayerNormalization
end
end
