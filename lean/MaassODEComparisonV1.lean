module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

set_option autoImplicit false

@[expose] public section

open Set Filter
open scoped Topology

namespace MaassODEComparison

/-- An increasing function on a terminal interval which tends to zero
is nonpositive. This is an auxiliary fact, not a Maass hypothesis. -/
theorem nonpos_of_monotoneOn_tendsto {g : ℝ → ℝ} {b x : ℝ}
    (hg : MonotoneOn g (Ici b)) (hlim : Tendsto g atTop (𝓝 0)) (hx : b ≤ x) :
    g x ≤ 0 := by
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop x] with y hy
  exact hg hx (hx.trans hy) hy

/-- The ODE comparison step, before its instantiation with the actual
Bessel integral. The ODE, differentiability and boundary condition are
explicit inputs; this lemma alone is NOT the Maass theorem. -/
theorem exponential_comparison
    (v v₁ v₂ : ℝ → ℝ) (b a : ℝ)
    (hd : ∀ x ∈ Ici b, HasDerivAt v (v₁ x) x)
    (hd₁ : ∀ x ∈ Ici b, HasDerivAt v₁ (v₂ x) x)
    (hode : ∀ x ∈ Ici b, a ^ 2 * v x ≤ v₂ x)
    (hlim : Tendsto (fun x => Real.exp (-a * x) * (v₁ x + a * v x))
      atTop (𝓝 0))
    {x y : ℝ} (hx : b ≤ x) (hxy : x ≤ y) :
    v y ≤ Real.exp (-a * (y - x)) * v x := by
  let g : ℝ → ℝ := fun z => Real.exp (-a * z) * (v₁ z + a * v z)
  have hg (z : ℝ) (hz : z ∈ Ici b) : HasDerivAt g
      (Real.exp (-a * z) * (v₂ z - a ^ 2 * v z)) z := by
    convert (((hasDerivAt_id z).const_mul (-a)).exp.mul
      ((hd₁ z hz).add ((hd z hz).const_mul a))) using 1
    all_goals try funext w
    all_goals dsimp [g]
    all_goals ring
  have hmono : MonotoneOn g (Ici b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici b)
    · exact fun z hz => (hg z hz).continuousAt.continuousWithinAt
    · exact fun z hz => (hg z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [(hg z (interior_subset hz)).deriv]
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hode z (interior_subset hz)))
  have hfirst (z : ℝ) (hz : z ∈ Ici b) : v₁ z + a * v z ≤ 0 := by
    have hg0 := nonpos_of_monotoneOn_tendsto hmono hlim hz
    change Real.exp (-a * z) * (v₁ z + a * v z) ≤ 0 at hg0
    nlinarith [Real.exp_pos (-a * z)]
  let f : ℝ → ℝ := fun z => Real.exp (a * z) * v z
  have hf (z : ℝ) (hz : z ∈ Ici b) : HasDerivAt f
      (Real.exp (a * z) * (v₁ z + a * v z)) z := by
    convert (((hasDerivAt_id z).const_mul a).exp.mul (hd z hz)) using 1
    all_goals try funext w
    all_goals dsimp [f]
    all_goals ring
  have hanti : AntitoneOn f (Ici b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici b)
    · exact fun z hz => (hf z hz).continuousAt.continuousWithinAt
    · exact fun z hz => (hf z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [(hf z (interior_subset hz)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hfirst z (interior_subset hz))
  have h := mul_le_mul_of_nonneg_left (hanti hx (hx.trans hxy) hxy)
    (Real.exp_pos (-a * y)).le
  have hcancel : Real.exp (-a * y) * Real.exp (a * y) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hcombine : Real.exp (-a * y) * Real.exp (a * x) = Real.exp (-a * (y-x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [f, ← mul_assoc, hcancel, one_mul, hcombine] using h

#print axioms exponential_comparison

end MaassODEComparison
