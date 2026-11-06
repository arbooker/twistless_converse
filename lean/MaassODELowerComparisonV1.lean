module

public import MaassODEComparisonV1

set_option autoImplicit false

@[expose] public section

open Set Filter
open scoped Topology

namespace MaassODEComparison

/-- The complementary lower comparison. All differential and infinity
conditions are explicit: this is not yet an instantiation with Bessel K. -/
theorem exponential_lower_comparison
    (v v₁ v₂ : ℝ → ℝ) (b a : ℝ)
    (hd : ∀ x ∈ Ici b, HasDerivAt v (v₁ x) x)
    (hd₁ : ∀ x ∈ Ici b, HasDerivAt v₁ (v₂ x) x)
    (hode : ∀ x ∈ Ici b, v₂ x ≤ a ^ 2 * v x)
    (hlim : Tendsto (fun x => Real.exp (-a * x) * (v₁ x + a * v x))
      atTop (𝓝 0))
    {x y : ℝ} (hx : b ≤ x) (hxy : x ≤ y) :
    Real.exp (-a * (y - x)) * v x ≤ v y := by
  have hdneg : ∀ z ∈ Ici b, HasDerivAt (fun w => -v w) (-v₁ z) z := by
    intro z hz
    exact (hd z hz).neg
  have hd₁neg : ∀ z ∈ Ici b, HasDerivAt (fun w => -v₁ w) (-v₂ z) z := by
    intro z hz
    exact (hd₁ z hz).neg
  have hodeneg : ∀ z ∈ Ici b, a^2 * (-v z) ≤ -v₂ z := by
    intro z hz
    nlinarith [hode z hz]
  have hlimneg : Tendsto (fun z => Real.exp (-a*z) * (-v₁ z + a * (-v z)))
      atTop (𝓝 0) := by
    convert hlim.neg using 1
    · funext z
      ring
    · simp
  have h := exponential_comparison (fun z => -v z) (fun z => -v₁ z)
    (fun z => -v₂ z) b a hdneg hd₁neg hodeneg hlimneg hx hxy
  nlinarith

/-- Weak form of the w.tex inequality from a nonnegative potential and
nonnegative solution. Positivity for a particular Bessel solution must be
proved separately, and is not concealed inside this conclusion. -/
theorem w_lower_comparison
    (v v₁ v₂ : ℝ → ℝ) (b lam : ℝ) (hlam : 0 ≤ lam)
    (hd : ∀ x ∈ Ici b, HasDerivAt v (v₁ x) x)
    (hd₁ : ∀ x ∈ Ici b, HasDerivAt v₁ (v₂ x) x)
    (hpos : ∀ x ∈ Ici b, 0 ≤ v x)
    (hode : ∀ x ∈ Ici b, v₂ x = (1 - lam / x^2) * v x)
    (hlim : Tendsto (fun x => Real.exp (-x) * (v₁ x + v x)) atTop (𝓝 0))
    {x y : ℝ} (hx : b ≤ x) (hxy : x ≤ y) :
    Real.exp (-(y-x)) * v x ≤ v y := by
  have hle : ∀ z ∈ Ici b, v₂ z ≤ (1 : ℝ)^2 * v z := by
    intro z hz
    rw [hode z hz]
    have hh := mul_nonneg (div_nonneg hlam (sq_nonneg z)) (hpos z hz)
    nlinarith
  have hlim' : Tendsto (fun z => Real.exp (-(1:ℝ)*z) * (v₁ z + 1*v z))
      atTop (𝓝 0) := by simpa using hlim
  simpa using exponential_lower_comparison v v₁ v₂ b 1 hd hd₁ hle hlim' hx hxy

#print axioms exponential_lower_comparison
#print axioms w_lower_comparison

end MaassODEComparison
