module

public import QuantitativeArithmeticLevelNineteenConverseV4
public import Mathlib.Analysis.Analytic.Order

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteen
open Complex Filter
open scoped Topology

private def expQuadratic (ell a b : ℂ) (s : ℂ) : ℂ :=
  1+a*exp (ell*s)+b*exp (2*ell*s)

private theorem expQuadratic_deriv (ell a b s : ℂ) :
    deriv (expQuadratic ell a b) s=a*ell*exp (ell*s)+2*b*ell*exp (2*ell*s) := by
  have h1 := (((hasDerivAt_id s).const_mul ell).cexp).const_mul a
  have h2 := (((hasDerivAt_id s).const_mul (2*ell)).cexp).const_mul b
  have h := ((hasDerivAt_const s (1:ℂ)).add h1).add h2
  have hd := h.deriv
  change deriv (expQuadratic ell a b) s=_ at hd
  rw [hd]
  dsimp
  ring

private theorem expQuadratic_deriv2 (ell a b s : ℂ) :
    deriv (deriv (expQuadratic ell a b)) s=
      a*ell^2*exp (ell*s)+4*b*ell^2*exp (2*ell*s) := by
  have he : deriv (expQuadratic ell a b)=
      (fun z => a*ell*exp (ell*z)+2*b*ell*exp (2*ell*z)) := funext (expQuadratic_deriv ell a b)
  rw [he]
  have h1 := (((hasDerivAt_id s).const_mul ell).cexp).const_mul (a*ell)
  have h2 := (((hasDerivAt_id s).const_mul (2*ell)).cexp).const_mul (2*b*ell)
  have hd := (h1.add h2).deriv
  change deriv (fun z => a*ell*exp (ell*z)+2*b*ell*exp (2*ell*z)) s=_ at hd
  rw [hd]
  dsimp
  ring

/-- A quadratic exponential with constant term1 has zeros of order at most2,
including when one or both of its other coefficients vanish. -/
private theorem expQuadratic_order (ell a b s : ℂ) (hell : ell≠0) :
    analyticOrderAt (expQuadratic ell a b) s≤2 := by
  have hf : AnalyticAt ℂ (expQuadratic ell a b) s := by unfold expQuadratic; fun_prop
  by_cases h0 : expQuadratic ell a b s=0
  · by_cases h1 : deriv (expQuadratic ell a b) s=0
    · have h2 : deriv (deriv (expQuadratic ell a b)) s≠0 := by
        intro h2
        rw [expQuadratic_deriv] at h1
        rw [expQuadratic_deriv2] at h2
        unfold expQuadratic at h0
        have he : 2*ell^2=0 := by linear_combination 2*ell^2*h0-3*ell*h1+h2
        exact (mul_ne_zero (by norm_num) (pow_ne_zero _ hell)) he
      have ho := hf.deriv.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h1 h2
      have hr := hf.analyticOrderAt_deriv_add_one
      simp only [h0,sub_zero,ho] at hr
      rw [← hr]
      norm_num
    · rw [hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h0 h1]
      norm_num
  · rw [hf.analyticOrderAt_eq_zero.mpr h0]
    exact zero_le

/-- Every zero of the actual level19 continuation denominator has order at
most2, uniformly in its unrestricted complex Hecke parameter. -/
theorem denominator_order_le_two (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    analyticOrderAt (denominator k f) s≤2 := by
  let a : ℂ := (((2:ℝ)^(((k:ℝ)+1)/2):ℝ):ℂ)*f 2
  have he : denominator k f=expQuadratic (-Complex.log 2) a ((2:ℂ)^k) := by
    funext z
    unfold denominator oppositeScalar heckeScalar expQuadratic
    rw [← scaleTwo_eq]
    have hp : scaleTwo k z=(2:ℂ)^k*(2:ℂ)^(-2*z) := by
      unfold scaleTwo
      rw [← Complex.cpow_natCast,← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
      congr 1
      ring
    rw [hp]
    simp only [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
    dsimp [a]
    rw [show Complex.log 2*(-z)= -Complex.log 2*z by ring,
      show Complex.log 2*(-2*z)=2*(-Complex.log 2)*z by ring]
    ring
  rw [he]
  apply expQuadratic_order
  have hlog : Complex.log (2:ℂ)≠0 := by
    intro hh
    have hh' := congrArg Complex.re hh
    norm_num [Complex.log_re] at hh'
  exact neg_ne_zero.mpr hlog

/-- The actual meromorphic quadratic continuation can have only simple or
double poles. The statement is formulated for its unique punctured germs,
so it applies directly to the original continuation already constructed. -/
theorem quadratic_order_ge_neg_two (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f)
    (G : ℂ → ℂ)
    (hgerm : ∀ x, G=ᶠ[𝓝[≠] x] (fun s => numerator m f s/denominator (2*m) f s))
    (s : ℂ) : (-2:WithTop ℤ)≤meromorphicOrderAt G s := by
  have ha := (original_numerator_entire m hm hf).analyticAt s
  have hd := (denominator_entire (2*m) f).analyticAt s
  have hbound := denominator_order_le_two (2*m) f s
  have hfinite : analyticOrderAt (denominator (2*m) f) s≠⊤ := by
    intro htop
    rw [htop] at hbound
    exact (not_le_of_gt (ENat.natCast_lt_top 2)) hbound
  obtain ⟨n,hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hn2 : n≤2 := by exact_mod_cast (hn ▸ hbound)
  rw [meromorphicOrderAt_congr (hgerm s)]
  change (-2:WithTop ℤ)≤meromorphicOrderAt (numerator m f / denominator (2*m) f) s
  rw [meromorphicOrderAt_div ha.meromorphicAt hd.meromorphicAt,hd.meromorphicOrderAt_eq,← hn]
  simp only [ENat.map_natCast]
  have hnonneg := ha.meromorphicOrderAt_nonneg
  cases he : meromorphicOrderAt (numerator m f) s with
  | top => simp
  | coe t =>
    rw [he] at hnonneg
    have ht : (0:ℤ)≤t := by exact_mod_cast hnonneg
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
    change ((-2:ℤ):WithTop ℤ)≤((t-(n:ℤ):ℤ):WithTop ℤ)
    exact_mod_cast (show (-2:ℤ)≤t-(n:ℤ) by omega)

#print axioms denominator_order_le_two
#print axioms quadratic_order_ge_neg_two
end QuantitativeArithmeticSmallLevelNineteen
