module

public import MaassOriginalAxisV1
public import FinitenessOriginalEulerFamilyV1

set_option autoImplicit false

@[expose] public section

namespace MaassOriginal

open FinitenessOriginalInput

/-- Complex Euler-product input with the Maass gamma factors. The spectral
parameter includes the principal and exceptional branches. Only the untwisted
functional equation is an input; twisted equations must be derived. -/
structure IsEulerSolution (N : ℕ) (p : MaassSpectral.Parameter) (δ : ℕ)
    (f : ℕ → ℂ) : Prop extends EulerData N f where
  parity : δ=0 ∨ δ=1
  continuation : ∃ ε : ℂ, (ε=1 ∨ ε = -1) ∧ Continuation (N:ℝ) p δ f ε

def EulerS (N : ℕ) (p : MaassSpectral.Parameter) (δ : ℕ) : Set (ℕ → ℂ) :=
  {f | IsEulerSolution N p δ f}

theorem IsEulerSolution.polynomialGrowth {N : ℕ} {p : MaassSpectral.Parameter}
    {δ : ℕ} {f : ℕ → ℂ} (hf : IsEulerSolution N p δ f) : PolynomialGrowth f := by
  obtain ⟨τ,_,hτ⟩ := hf.growth
  exact ⟨τ,hτ.norm_left⟩

/-- The independence argument is shared with holomorphic Euler products. -/
theorem euler_independent (N : ℕ) (p : MaassSpectral.Parameter) (δ : ℕ) :
    LinearIndependent ℂ (fun f : EulerS N p δ => f.val) := by
  classical
  apply FinitenessEulerFamily.independent _ (fun l => if l ∣ N then 0 else 1)
  · intro f
    exact f.property.zero
  · intro f
    exact (FinitenessEulerIdentification.euler_arithmetic f.property.toEulerData).1
  · intro f a b hc
    exact (FinitenessEulerIdentification.euler_arithmetic f.property.toEulerData).2.1 a b hc
  · intro f l hl j
    exact (FinitenessEulerIdentification.euler_arithmetic f.property.toEulerData).2.2 l hl j
  · intro f g h
    exact Subtype.ext h

#print axioms euler_independent

end MaassOriginal
