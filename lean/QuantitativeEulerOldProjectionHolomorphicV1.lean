module

public import AsymptoticClassicalTraceAdjointV1
public import AsymptoticClassicalFrickeIsometryV1
public import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

/-!
The weight-k cusp realization below is the closed subspace of raw quotient
L² consisting of the actual functions sqrt(y^k) f(z). It is not the scalar
invariant AutomorphicSpace: the normalized slash action retains its phase.
All-prime classical newness requires both traces at every prime dividing N;
no identification with just the repeated-two local kernel is asserted here.
-/

namespace QuantitativeEulerOldProjectionHolomorphic

open UpperHalfPlane MeasureTheory AsymptoticClassicalCusp AsymptoticClassicalPetersson
open scoped InnerProduct

variable (N : ℕ) [NeZero N] (k : ℤ)

/-- Actual weight-k cusp functions in quotient L², with their Petersson norm. -/
def weightedEmbedding : CuspForm (level N) k →ₗᵢ[ℂ] Lp ℂ 2 (quotientMeasure N) where
  toLinearMap := embedding N k
  norm_map' _ := rfl

def space : Submodule ℂ (Lp ℂ 2 (quotientMeasure N)) := (embedding N k).range

instance space_finite : FiniteDimensional ℂ (space N k) :=
  LinearMap.finiteDimensional_range (embedding N k)

instance space_complete : CompleteSpace (space N k) := FiniteDimensional.complete ℂ _

theorem space_closed : IsClosed (space N k : Set (Lp ℂ 2 (quotientMeasure N))) :=
  Submodule.closed_of_finiteDimensional _

/-- A surjective isometry onto the actual weighted cusp subspace. -/
def realization : CuspForm (level N) k ≃ₗᵢ[ℂ] space N k :=
  (weightedEmbedding N k).equivRange

theorem realization_coeFn (f : CuspForm (level N) k) :
    ((realization N k f : space N k) : Lp ℂ 2 (quotientMeasure N)) =ᵐ[quotientMeasure N]
      weighted k f := embedding_coeFn N k f

variable (M : ℕ) [NeZero M] (hMN : M ∣ N)

/-- The literal lower-level inclusion, realized between the weighted
quotient Hilbert spaces. Its underlying cusp functions are unchanged. -/
def inclusion : space M k →L[ℂ] space N k :=
  (realization N k).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((restrict k (level_antitone hMN)).toContinuousLinearMap).comp
      (realization M k).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem inclusion_realization (f : CuspForm (level M) k) :
    inclusion N k M hMN (realization M k f) =
      realization N k (restrict k (level_antitone hMN) f) := by
  simp [inclusion]

/-- Hilbert adjoint of the actual weighted finite-cover inclusion. -/
def trace : space N k →L[ℂ] space M k := (inclusion N k M hMN).adjoint

/-- The actual classical arithmetic trace equals the finite-cover Hilbert
adjoint after weighted realization. This is a theorem, not a bridge premise. -/
theorem trace_realization (f : CuspForm (level N) k) :
    trace N k M hMN (realization N k f) =
      realization M k (arithmeticTrace (level N) (level M) k f) := by
  apply ext_inner_right ℂ
  intro v
  obtain ⟨g, rfl⟩ := (realization M k).surjective v
  rw [trace, ContinuousLinearMap.adjoint_inner_left, inclusion_realization,
    (realization N k).inner_map_map, (realization M k).inner_map_map]
  exact (trace_adjoint N M k hMN f g).symm

#print axioms realization
#print axioms space_closed
#print axioms trace_realization
end QuantitativeEulerOldProjectionHolomorphic
