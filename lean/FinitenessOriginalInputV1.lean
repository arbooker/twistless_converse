module

public import FinitenessDirichletInversionV1
public import FinitenessGrowthNormalizationV1
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

@[expose] public section

set_option autoImplicit false

namespace FinitenessOriginalInput

open Complex Filter Asymptotics Set

/-- Eventual finite order, allowing a REAL exponent and an arbitrary
exceptional compact disk. No global bound or common order is imposed. -/
def FiniteOrder (F : ℂ → ℂ) : Prop :=
  ∃ (A ρ R : ℝ), 0 ≤ A ∧ 0 ≤ R ∧
    ∀ z : ℂ, R ≤ ‖z‖ → ‖F z‖ ≤ Real.exp (A*(1+‖z‖)^ρ)

/-- All sequences are indexed by Nat with coefficient zero at index zero;
the actual Dirichlet series uses exactly the positive indices. -/
noncomputable def L (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (f (n+1) : ℂ)*((n+1 : ℕ):ℂ)^(-s)

noncomputable def gammaC (s : ℂ) : ℂ :=
  2*((2*Real.pi : ℝ):ℂ)^(-s)*Gamma s

noncomputable def completed (N k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  (N : ℂ)^((s-1/2)/2)*gammaC (s+((k : ℂ)-1)/2)*L f s

noncomputable def localFactor (N : ℕ) (f : ℕ → ℂ) (p : ℕ) (s : ℂ) : ℂ :=
  (1-(f p : ℂ)*(p : ℂ)^(-s)+(if p ∣ N then (0:ℂ) else 1)*(p : ℂ)^(-2*s))⁻¹

/-- The Euler product itself, not a substitute hypothesis of coefficient
multiplicativity or Hecke recurrences. It holds on some right half-plane. -/
def EulerProduct (N : ℕ) (f : ℕ → ℂ) : Prop :=
  ∃ c : ℝ, ∀ s : ℂ, c < s.re →
    HasProd (fun p : {p : ℕ // p.Prime} => localFactor N f p.val s) (L f s)

def BadPrimeConditions (N : ℕ) (f : ℕ → ℂ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N →
    f p ^ 2 = if p^2 ∣ N then 0 else (p : ℂ)⁻¹

def Continuation (N k : ℕ) (f : ℕ → ℂ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ FiniteOrder F ∧
    (∃ c : ℝ, ∀ s : ℂ, c < s.re → F s=completed N k f s) ∧
    ∃ ε : ℂ, (ε=1 ∨ ε = -1) ∧ ∀ s : ℂ, F s=(ε : ℂ)*F (1-s)

/-- Common complex Euler-product input for the holomorphic and Maass cases.
The growth exponent belongs to the sequence, not to the whole family. -/
structure EulerData (N : ℕ) (f : ℕ → ℂ) : Prop where
  zero : f 0=0
  growth : ∃ σ : ℝ, 0 < σ ∧ f =O[atTop] (fun n : ℕ => (n : ℝ)^σ)
  euler : EulerProduct N f
  bad : BadPrimeConditions N f

/-- The revised holomorphic solution predicate. No Ramanujan-twist FE,
modularity, coefficient integrality, or common growth exponent is assumed. -/
structure IsSolution (N k : ℕ) (f : ℕ → ℂ) : Prop extends EulerData N f where
  continuation : Continuation N k f

def S (N k : ℕ) : Set (ℕ → ℂ) := {f | IsSolution N k f}

end FinitenessOriginalInput
