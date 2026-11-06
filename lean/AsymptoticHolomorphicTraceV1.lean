module

public import AsymptoticObservationTraceV1
public import AsymptoticFourierMajorantV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap InnerProductSpace AsymptoticDiagonalTrace AsymptoticFourierNorm
open scoped InnerProduct BigOperators

variable {G H J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- The compression acting on the holomorphic subspace itself, so its
diagonal can be taken in the positive-frequency Fourier basis. -/
noncomputable def holomorphicOperator (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (U : Submodule ℂ H) [CompleteSpace U] : U →L[ℂ] U :=
  U.subtypeL.adjoint.comp ((operator R L hR).comp U.subtypeL)

theorem holomorphicOperator_positive (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (U : Submodule ℂ H) [CompleteSpace U] :
    (holomorphicOperator R L hR U).IsPositive :=
  (operator_positive R L hR).adjoint_conj U.subtypeL

theorem holomorphicOperator_inner (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (U : Submodule ℂ H) [CompleteSpace U] (u : U) :
    ⟪holomorphicOperator R L hR U u,u⟫_ℂ=⟪operator R L hR (u:H),(u:H)⟫_ℂ :=
  U.subtypeL.adjoint_inner_left u _

theorem holomorphicOperator_fixes (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (U : Submodule ℂ H) [CompleteSpace U] (u : U)
    (hreconstruct : ∃ g,R g=(u:H)) (hobs : L (u:H)=0) :
    holomorphicOperator R L hR U u=u := by
  obtain ⟨g,hg⟩ := hreconstruct
  have he : operator R L hR (u:H)=(u:H) := by
    rw [← hg]
    exact operator_fixes R L hR (by rwa [hg])
  change U.subtypeL.adjoint (operator R L hR (u:H))=u
  rw [he,U.adjoint_subtypeL]
  exact U.orthogonalProjectionOnto_mem_subspace_eq_self u

/-- The actual radial majorant now supplies the finite trace, uniformly
for every observation stack. The Gram estimate is the remaining weighted
adjoint-pairing input. -/
theorem holomorphic_trace_bound (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (U : Submodule ℂ H) [CompleteSpace U]
    (b : HilbertBasis ℕ ℂ U) (m t : ℕ) {scale ε C : ℝ}
    (hs : 0<scale) (hε : 0<ε) (hC : 0≤C)
    (hgram : ∀ n,‖R.adjoint ((b n:U):H)‖^2≤C*modeRatio m t scale ε (n+1)) :
    Summable (fun n => (⟪holomorphicOperator R L hR U (b n),b n⟫_ℂ).re) ∧
      trace b (holomorphicOperator R L hR U)≤C*(1+majorantConstant t scale ε)*(m+2:ℕ) := by
  have hh := positive_modeRatio_summable_bound m t hs hε
  have hmajor := hh.1.mul_left C
  have hnonneg : ∀ n,0≤(⟪holomorphicOperator R L hR U (b n),b n⟫_ℂ).re :=
    fun n => (holomorphicOperator_positive R L hR U).re_inner_nonneg_left (b n)
  have hle : ∀ n,(⟪holomorphicOperator R L hR U (b n),b n⟫_ℂ).re≤C*modeRatio m t scale ε (n+1) := by
    intro n
    rw [holomorphicOperator_inner]
    exact (operator_re_inner_le_gram R L hR _).trans (hgram n)
  have hsum := Summable.of_nonneg_of_le hnonneg hle hmajor
  refine ⟨hsum,(hsum.tsum_le_tsum hle hmajor).trans ?_⟩
  rw [tsum_mul_left]
  calc
    C*(∑' n,modeRatio m t scale ε (n+1)) ≤ C*((1+majorantConstant t scale ε)*(m+2:ℕ)) :=
      mul_le_mul_of_nonneg_left hh.2 hC
    _ = _ := by ring

/-- The finite-dimensional solution space is bounded by the constructed
holomorphic trace, using the proved radial-integral summability. -/
theorem holomorphic_finrank_le_trace (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (U : Submodule ℂ H) [CompleteSpace U]
    (b : HilbertBasis ℕ ℂ U) (W : Submodule ℂ U) [FiniteDimensional ℂ W]
    (m t : ℕ) {scale ε C : ℝ} (hs : 0<scale) (hε : 0<ε) (hC : 0≤C)
    (hgram : ∀ n,‖R.adjoint ((b n:U):H)‖^2≤C*modeRatio m t scale ε (n+1))
    (hreconstruct : ∀ w∈W,∃ g,R g=(w:H)) (hobs : ∀ w∈W,L (w:H)=0) :
    (Module.finrank ℂ W:ℝ)≤trace b (holomorphicOperator R L hR U) :=
  finrank_le_trace b _ (holomorphicOperator_positive R L hR U) W
    (fun w hw => holomorphicOperator_fixes R L hR U w (hreconstruct w hw) (hobs w hw))
    (holomorphic_trace_bound R L hR U b m t hs hε hC hgram).1

/-- The weighted adjoint estimate follows from a bounded extension into
the stronger weighted space and the radial norm of the inclusion adjoint. -/
theorem gram_bound_of_weighted_factorization {H₀ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
    (R₀ : G →L[ℂ] H₀) (inclusion : H₀ →L[ℂ] H) (b : ℕ → H)
    (m t : ℕ) {scale ε : ℝ}
    (hinclusion : ∀ n,‖inclusion.adjoint (b n)‖^2≤modeRatio m t scale ε (n+1)) :
    ∀ n,‖(inclusion.comp R₀).adjoint (b n)‖^2≤‖R₀‖^2*modeRatio m t scale ε (n+1) := by
  intro n
  rw [adjoint_comp,comp_apply]
  calc
    ‖R₀.adjoint (inclusion.adjoint (b n))‖^2 ≤
        (‖R₀.adjoint‖*‖inclusion.adjoint (b n)‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (R₀.adjoint.le_opNorm _) 2
    _ = ‖R₀‖^2*‖inclusion.adjoint (b n)‖^2 := by rw [mul_pow,adjoint.norm_map]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hinclusion n) (sq_nonneg _)

#print axioms gram_bound_of_weighted_factorization
#print axioms holomorphic_trace_bound
#print axioms holomorphic_finrank_le_trace

end AsymptoticObservation
