module

public import Mathlib.Analysis.Analytic.Order
public import QuantitativeArithmeticAnalyticGermTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticQuadraticGermOrder. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticQuadraticGermOrderV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticQuadraticGermOrder

/-- A quadratic in a local analytic coordinate has zero order at most two.
The coefficients are fixed throughout the germ. -/
theorem quadratic_order {X : ℂ → ℂ} {s : ℂ}
    (hX : AnalyticAt ℂ X s) (hd : deriv X s ≠ 0) (a : ℂ) :
    meromorphicOrderAt (fun z => a*X z+(X z)^2-1) s=0 ∨
    meromorphicOrderAt (fun z => a*X z+(X z)^2-1) s=1 ∨
    meromorphicOrderAt (fun z => a*X z+(X z)^2-1) s=2 := by
  have hD : AnalyticAt ℂ (fun z => a*X z+(X z)^2-1) s :=
    (analyticAt_const.mul hX |>.add (hX.pow 2)).sub analyticAt_const
  by_cases hz : a*X s+(X s)^2-1=0
  · have he : (fun z => a*X z+(X z)^2-1) =
        (fun z => X z-X s)*(fun z => X z+X s+a) := by
      funext z
      simp only [Pi.mul_apply]
      linear_combination hz
    have hU : AnalyticAt ℂ (fun z => X z-X s) s := hX.sub analyticAt_const
    have hoU : meromorphicOrderAt (fun z => X z-X s) s=1 := by
      rw [hU.meromorphicOrderAt_eq, hX.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd]
      rfl
    have hV : AnalyticAt ℂ (fun z => X z+X s+a) s :=
      (hX.add analyticAt_const).add analyticAt_const
    rw [he,meromorphicOrderAt_mul hU.meromorphicAt hV.meromorphicAt,hoU]
    by_cases hv : X s+X s+a=0
    · have heV : (fun z => X z+X s+a)=(fun z => X z-X s) := by
        funext z
        linear_combination hv
      rw [heV,hoU]
      norm_num
    · have hoV : meromorphicOrderAt (fun z => X z+X s+a) s=0 := by
        rw [hV.meromorphicOrderAt_eq,hV.analyticOrderAt_eq_zero.mpr hv]
        rfl
      simp [hoV]
  · left
    rw [hD.meromorphicOrderAt_eq,hD.analyticOrderAt_eq_zero.mpr hz]
    rfl

#print axioms quadratic_order
end QuantitativeArithmeticQuadraticGermOrder
end
end

/-! ## QuantitativeArithmeticQuadraticPoleBoundV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticQuadraticGermOrder
open QuantitativeArithmeticAnalyticGerm

theorem pole_order_ge_neg_two {X F : ℂ → ℂ} {s : ℂ}
    (hX : AnalyticAt ℂ X s) (hd : deriv X s ≠ 0) (a : ℂ)
    (hF : MeromorphicAt F s)
    (hprod : HasAnalyticGerm (fun z => (a*X z+(X z)^2-1)*F z) s) :
    (-2 : WithTop ℤ) ≤ meromorphicOrderAt F s := by
  have hD : AnalyticAt ℂ (fun z => a*X z+(X z)^2-1) s :=
    (analyticAt_const.mul hX |>.add (hX.pow 2)).sub analyticAt_const
  have hsum := hprod.order_nonneg
  change 0 ≤ meromorphicOrderAt ((fun z => a*X z+(X z)^2-1)*F) s at hsum
  rw [meromorphicOrderAt_mul hD.meromorphicAt hF] at hsum
  have hsmall : meromorphicOrderAt (fun z => a*X z+(X z)^2-1) s ≤
      ((2:ℤ) : WithTop ℤ) := by
    rcases quadratic_order hX hd a with h0|h1|h2 <;> simp_all
  have hn : (0 : WithTop ℤ) ≤ ((2:ℤ) : WithTop ℤ)+meromorphicOrderAt F s :=
    le_trans hsum (add_le_add hsmall le_rfl)
  cases ho : meromorphicOrderAt F s with
  | top => simp
  | coe n =>
    rw [ho] at hn
    have hn' : (0 : ℤ)≤2+n := by exact_mod_cast hn
    change ((-2 : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ)
    norm_cast
    omega

#print axioms pole_order_ge_neg_two
end QuantitativeArithmeticQuadraticGermOrder
end
end

/-! ## QuantitativeArithmeticQuadraticSimpleGermV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticQuadraticGermOrder
open QuantitativeArithmeticAnalyticGerm

theorem quadratic_simple_order {X : ℂ → ℂ} {s : ℂ}
    (hX : AnalyticAt ℂ X s) (hd : deriv X s≠0) (a : ℂ)
    (hsq : (X s)^2≠ -1) :
    meromorphicOrderAt (fun z => a*X z+(X z)^2-1) s=0 ∨
    meromorphicOrderAt (fun z => a*X z+(X z)^2-1) s=1 := by
  have hD : AnalyticAt ℂ (fun z => a*X z+(X z)^2-1) s :=
    (analyticAt_const.mul hX |>.add (hX.pow 2)).sub analyticAt_const
  by_cases hz : a*X s+(X s)^2-1=0
  · right
    have hv : X s+X s+a≠0 := by
      intro hh
      apply hsq
      linear_combination X s*hh-hz
    have he : (fun z => a*X z+(X z)^2-1) =
        (fun z => X z-X s)*(fun z => X z+X s+a) := by
      funext z
      simp only [Pi.mul_apply]
      linear_combination hz
    have hU : AnalyticAt ℂ (fun z => X z-X s) s := hX.sub analyticAt_const
    have hV : AnalyticAt ℂ (fun z => X z+X s+a) s :=
      (hX.add analyticAt_const).add analyticAt_const
    rw [he,meromorphicOrderAt_mul hU.meromorphicAt hV.meromorphicAt,
      hU.meromorphicOrderAt_eq,hV.meromorphicOrderAt_eq,
      hX.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd,
      hV.analyticOrderAt_eq_zero.mpr hv]
    rfl
  · left
    rw [hD.meromorphicOrderAt_eq,hD.analyticOrderAt_eq_zero.mpr hz]
    rfl

theorem pole_order_ge_neg_one {X F : ℂ → ℂ} {s : ℂ}
    (hX : AnalyticAt ℂ X s) (hd : deriv X s≠0) (a : ℂ)
    (hsq : (X s)^2≠ -1) (hF : MeromorphicAt F s)
    (hprod : HasAnalyticGerm (fun z => (a*X z+(X z)^2-1)*F z) s) :
    (-1 : WithTop ℤ)≤meromorphicOrderAt F s := by
  have hD : AnalyticAt ℂ (fun z => a*X z+(X z)^2-1) s :=
    (analyticAt_const.mul hX |>.add (hX.pow 2)).sub analyticAt_const
  have hsum := hprod.order_nonneg
  change 0≤meromorphicOrderAt ((fun z => a*X z+(X z)^2-1)*F) s at hsum
  rw [meromorphicOrderAt_mul hD.meromorphicAt hF] at hsum
  have hb : meromorphicOrderAt (fun z => a*X z+(X z)^2-1) s≤((1:ℤ):WithTop ℤ) := by
    rcases quadratic_simple_order hX hd a hsq with h0|h1 <;> simp_all
  have hn : (0:WithTop ℤ)≤((1:ℤ):WithTop ℤ)+meromorphicOrderAt F s :=
    le_trans hsum (add_le_add hb le_rfl)
  cases ho : meromorphicOrderAt F s with
  | top => simp
  | coe n =>
    rw [ho] at hn
    have hn' : (0:ℤ)≤1+n := by exact_mod_cast hn
    change ((-1:ℤ):WithTop ℤ)≤(n:WithTop ℤ)
    norm_cast
    omega

#print axioms quadratic_simple_order
#print axioms pole_order_ge_neg_one
end QuantitativeArithmeticQuadraticGermOrder
end
end
