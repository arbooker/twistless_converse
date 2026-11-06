module
public import QuantitativeArithmeticEntireQuotientV1
public import Mathlib.Order.Filter.Finite
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticFiniteAnalyticWitness
open Complex Filter Set
open scoped Topology
/-- Finitely many entire functions, none identically zero, are simultaneously
nonzero somewhere. No quantitative separation of their zeros is asserted. -/
theorem common_nonzero {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (ha : ∀ i z, AnalyticAt ℂ (f i) z)
    (hw : ∀ i, ∃ z, f i z ≠ 0) : ∃ z, ∀ i, f i z ≠ 0 := by
  have hall : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ i, f i z ≠ 0 :=
    Filter.eventually_all.mpr (fun i =>
      QuantitativeArithmeticEntireQuotient.nonzero_germ (f i) (ha i) (hw i) 0)
  exact hall.exists
#print axioms common_nonzero
end QuantitativeArithmeticFiniteAnalyticWitness
