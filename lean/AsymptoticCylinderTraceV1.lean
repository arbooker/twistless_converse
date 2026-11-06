module

public import AsymptoticCylinderFourierV1
public import AsymptoticHolomorphicTraceV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinder

open AsymptoticFourierNorm AsymptoticObservation AsymptoticDiagonalTrace InnerProductSpace
open scoped InnerProduct

variable {G J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- The common Gram majorant for a bounded reconstruction into the
stronger cylinder space, with no radial estimate left as a premise. -/
theorem reconstructed_fourier_gram (R₀ : G →L[ℂ] Space) (m t : ℕ) {scale ε : ℝ}
    (hs : 0<scale) (hε : 0<ε) (n : ℕ) :
    ‖((inclusion hε).comp R₀).adjoint
      ((fourierBasis m t hs hε n : holomorphicSpace m t hs hε):Space)‖^2 ≤
      ‖R₀‖^2*modeRatio m t scale ε (n+1) := by
  have hh := gram_bound_of_weighted_factorization R₀ (inclusion hε)
    (fun n => unitMode m t n hs hε) m t (scale:=scale) (ε:=ε) (by
      intro n
      rw [inclusion_adjoint_unitMode_norm_sq,modeRatio,ite_eq_right (by omega : n+1≠0)])
  simpa only [fourierBasis_apply,modeInSpace] using hh n

/-- Every observation stack has finite compressed trace, bounded by O(k)
in the concrete positive-mode cylinder space. The constant is independent
of the observation stack. The geometric reconstruction is the remaining
input R₀, together with its terminal lower bound. -/
theorem observation_trace_bound (R₀ : G →L[ℂ] Space) (L : Space →L[ℂ] J)
    (m t : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε)
    (hR : ∀ g,‖g‖≤‖(inclusion hε).comp R₀ g‖) :
    let U := holomorphicSpace m t hs hε
    let b := fourierBasis m t hs hε
    let Q := holomorphicOperator ((inclusion hε).comp R₀) L hR U
    Summable (fun n => (⟪Q (b n),b n⟫_ℂ).re) ∧
      trace b Q≤‖R₀‖^2*(1+majorantConstant t scale ε)*(m+2:ℕ) :=
  holomorphic_trace_bound ((inclusion hε).comp R₀) L hR
    (holomorphicSpace m t hs hε) (fourierBasis m t hs hε) m t hs hε (sq_nonneg _)
    (reconstructed_fourier_gram R₀ m t hs hε)

/-- The dimension-to-trace estimate with the cylinder, Fourier basis and
summability all constructed. Only reconstruction and the known equations
are required of the finite-dimensional solution space. -/
theorem solution_finrank_le_trace (R₀ : G →L[ℂ] Space) (L : Space →L[ℂ] J)
    (m t : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε)
    (hR : ∀ g,‖g‖≤‖(inclusion hε).comp R₀ g‖)
    (W : Submodule ℂ (holomorphicSpace m t hs hε)) [FiniteDimensional ℂ W]
    (hreconstruct : ∀ w∈W,∃ g,(inclusion hε).comp R₀ g=(w:Space))
    (hobs : ∀ w∈W,L (w:Space)=0) :
    (Module.finrank ℂ W:ℝ)≤trace (fourierBasis m t hs hε)
      (holomorphicOperator ((inclusion hε).comp R₀) L hR (holomorphicSpace m t hs hε)) :=
  holomorphic_finrank_le_trace ((inclusion hε).comp R₀) L hR
    (holomorphicSpace m t hs hε) (fourierBasis m t hs hε) W m t hs hε (sq_nonneg _)
    (reconstructed_fourier_gram R₀ m t hs hε) hreconstruct hobs

#print axioms reconstructed_fourier_gram
#print axioms observation_trace_bound
#print axioms solution_finrank_le_trace

end AsymptoticCylinder
