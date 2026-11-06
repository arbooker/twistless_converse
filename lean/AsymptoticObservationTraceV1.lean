module

public import AsymptoticDiagonalTraceV1

set_option autoImplicit false

@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap InnerProductSpace AsymptoticDiagonalTrace
open scoped InnerProduct

variable {G H J ι : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- Summability of the reconstruction Gram diagonal implies that the
compressed observation operator has a finite diagonal trace. -/
theorem compression_trace_summable (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (b : HilbertBasis ι ℂ H)
    (hgram : Summable (fun i => ‖R.adjoint (U.starProjection (b i))‖^2)) :
    Summable (fun i => (⟪compression R L hR U (b i),b i⟫_ℂ).re) :=
  Summable.of_nonneg_of_le
    (fun i => (compression_positive R L hR U).re_inner_nonneg_left (b i))
    (fun i => compression_re_inner_le_gram R L hR U (b i)) hgram

/-- The observation trace has the common Gram majorant, independently of
which fixed observation stack is imposed. -/
theorem compression_trace_le_gram (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (b : HilbertBasis ι ℂ H)
    (hgram : Summable (fun i => ‖R.adjoint (U.starProjection (b i))‖^2)) :
    trace b (compression R L hR U) ≤ ∑' i,‖R.adjoint (U.starProjection (b i))‖^2 :=
  (compression_trace_summable R L hR U b hgram).tsum_le_tsum
    (fun i => compression_re_inner_le_gram R L hR U (b i)) hgram

/-- The supplement's dimension-to-trace inequality, derived for a linear
space of reconstructed holomorphic solutions satisfying the observations. -/
theorem reconstructed_finrank_le_trace (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g, ‖g‖≤‖R g‖) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (b : HilbertBasis ι ℂ H) (W : Submodule ℂ H) [FiniteDimensional ℂ W]
    (hWU : W≤U) (hreconstruct : ∀ w∈W, ∃ g, R g=w)
    (hobs : ∀ w∈W,L w=0)
    (hgram : Summable (fun i => ‖R.adjoint (U.starProjection (b i))‖^2)) :
    (Module.finrank ℂ W:ℝ)≤trace b (compression R L hR U) := by
  apply finrank_le_trace b _ (compression_positive R L hR U) W _
    (compression_trace_summable R L hR U b hgram)
  intro w hw
  obtain ⟨g,rfl⟩ := hreconstruct w hw
  exact compression_fixes R L hR U (hobs _ hw) (hWU hw)

#print axioms compression_trace_summable
#print axioms compression_trace_le_gram
#print axioms reconstructed_finrank_le_trace

end AsymptoticObservation
