module

public import QuantitativeMaassAbelCutoffDerivativeBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A cutoff equal to one on [1,1+a] and supported below 1+2a. -/
def abelBoundaryCutoff (a q : ℝ) : ℂ := abelCutoff a (q-a)

theorem abelBoundaryCutoff_smooth (a : ℝ) : ContDiff ℝ ∞ (abelBoundaryCutoff a) :=
  (abelCutoff_smooth a).comp (contDiff_id.sub contDiff_const)

theorem abelBoundaryCutoff_support (a : ℝ) (ha : 0<a) :
    Function.support (abelBoundaryCutoff a)⊆Iic (1+2*a) := by
  intro q hq
  have h := abelCutoff_support a ha hq
  change q-a≤1+a at h
  change q≤1+2*a
  linarith

theorem abelBoundaryCutoff_one (a : ℝ) (ha : 0<a) (ha1 : a≤1)
    (q : ℝ) (hq : 1≤q) (hqa : q≤1+a) : abelBoundaryCutoff a q=1 := by
  have hleft : 1≤q-a+1 := by linarith
  have hright : (q-a-1)/a≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
  simp only [abelBoundaryCutoff,abelCutoff,abelCutoffReal,
    Real.smoothTransition.one_of_one_le hleft,Real.smoothTransition.zero_of_nonpos hright,
    sub_zero,one_mul,Complex.ofReal_one]

theorem abelBoundaryCutoff_deriv (a q : ℝ) :
    deriv (abelBoundaryCutoff a) q=deriv (abelCutoff a) (q-a) := by
  have hi : HasDerivAt (fun u : ℝ => u-a) 1 q := (hasDerivAt_id q).sub_const a
  change deriv (fun u => abelCutoff a (u-a)) q=deriv (abelCutoff a) (q-a)
  simpa only [one_smul,Function.comp_def] using
    (((abelCutoff_smooth a).differentiable (by simp) (q-a)).hasDerivAt.scomp q hi).deriv

def abelBoundaryPart (F : ℝ → ℂ) (a q : ℝ) : ℂ := F q*abelBoundaryCutoff a q

theorem abelBoundaryPart_smooth (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (a : ℝ) :
    ContDiff ℝ ∞ (abelBoundaryPart F a) := hF.mul (abelBoundaryCutoff_smooth a)

theorem abelBoundaryPart_compact (F : ℝ → ℂ) (hc : HasCompactSupport F) (a : ℝ) :
    HasCompactSupport (abelBoundaryPart F a) := hc.mul_right

theorem abelBoundaryPart_support_source (F : ℝ → ℂ) (a B : ℝ)
    (hs : Function.support F⊆Iic B) : Function.support (abelBoundaryPart F a)⊆Iic B := by
  intro q hq
  apply hs
  intro hz
  exact hq (by simp only [abelBoundaryPart,hz,zero_mul])

theorem abelBoundaryPart_support (F : ℝ → ℂ) (a : ℝ) (ha : 0<a) :
    Function.support (abelBoundaryPart F a)⊆Iic (1+2*a) := by
  intro q hq
  apply abelBoundaryCutoff_support a ha
  intro hz
  exact hq (by simp only [abelBoundaryPart,hz,mul_zero])

/-- The removed endpoint piece has an explicit reciprocal-width derivative
bound derived from the fixed test and the actual smooth cutoff. -/
theorem abelBoundaryPart_derivative_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (A B D : ℝ) (hA : 0≤A) (hB : 0≤B) (hD : 0≤D)
    (hFA : ∀ q,‖deriv F q‖≤A) (hFB : ∀ q,‖F q‖≤B)
    (hTD : ∀ q,|deriv Real.smoothTransition q|≤D)
    (a : ℝ) (ha : 0<a) (ha1 : a≤1) (q : ℝ) :
    ‖deriv (abelBoundaryPart F a) q‖≤(A+2*B*D)/a := by
  have he : deriv (abelBoundaryPart F a) q=
      deriv F q*abelBoundaryCutoff a q+F q*deriv (abelBoundaryCutoff a) q :=
    deriv_mul (hF.differentiable (by simp) q) ((abelBoundaryCutoff_smooth a).differentiable (by simp) q)
  rw [he]
  have hc : ‖abelBoundaryCutoff a q‖≤1 := abelCutoff_norm_le_one a (q-a)
  have hd : ‖deriv (abelBoundaryCutoff a) q‖≤2*D/a := by
    rw [abelBoundaryCutoff_deriv]
    exact abelCutoff_derivative_bound D hD hTD a ha ha1 (q-a)
  have hfirst : ‖deriv F q*abelBoundaryCutoff a q‖≤A := by
    rw [norm_mul]
    exact (mul_le_mul (hFA q) hc (norm_nonneg _) hA).trans_eq (mul_one A)
  have hsecond : ‖F q*deriv (abelBoundaryCutoff a) q‖≤B*(2*D/a) := by
    rw [norm_mul]
    exact mul_le_mul (hFB q) hd (norm_nonneg _) hB
  have hAa : A≤A/a := (le_div_iff₀ ha).mpr (mul_le_of_le_one_right hA ha1)
  calc
    _ ≤ A+B*(2*D/a) := (norm_add_le _ _).trans (add_le_add hfirst hsecond)
    _ ≤ A/a+B*(2*D/a) := by linarith
    _ = _ := by ring

#print axioms abelBoundaryCutoff_one
#print axioms abelBoundaryPart_support
#print axioms abelBoundaryPart_derivative_bound

end QuantitativeMaass
