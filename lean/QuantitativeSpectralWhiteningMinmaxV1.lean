module

public import QuantitativeSpectralMinmaxV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralWhiteningMinmax

open ContinuousLinearMap InnerProductSpace QuantitativeSpectralCut
open QuantitativeSpectralCutRegularity AsymptoticRegularTrace MeasureTheory
open scoped InnerProduct lp ENNReal

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem whitening_high_injective (A Q J : H →L[ℂ] H) (hfactor : A.comp J = Q)
    {a b k : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k) (hJ : ‖J‖ ≤ k) (hab : a*k^2 < b)
    {v : H} (hv : v ∈ highAt (Q.adjoint.comp Q) b)
    (hz : (highAt (A.adjoint.comp A) a).starProjection (J v) = 0) : v = 0 := by
  have hmem : J v ∈ (highAt (A.adjoint.comp A) a)ᗮ := by
    rw [← Submodule.ker_starProjection]
    exact hz
  have hlow : J v ∈ lowAt (A.adjoint.comp A) a := by
    simpa only [highAt, high, lowAt, Submodule.orthogonal_orthogonal] using hmem
  have hsa (T : H →L[ℂ] H) : IsSelfAdjoint (T.adjoint.comp T) := by
    rw [isSelfAdjoint_iff']
    simp only [adjoint_comp, adjoint_adjoint]
  have hl := quadratic_le_on_lowAt _ (hsa A) a hlow
  have hh := quadratic_ge_on_highAt _ (hsa Q) b hv
  have hquad (T : H →L[ℂ] H) (w : H) :
      (⟪(T.adjoint.comp T) w, w⟫_ℂ).re = ‖T w‖^2 := by
    rw [comp_apply, adjoint_inner_left]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (T w)).symm
  rw [hquad] at hl hh
  have hf : A (J v) = Q v := congrArg (fun T : H →L[ℂ] H => T v) hfactor
  rw [hf] at hl
  have hj : ‖J v‖ ≤ k*‖v‖ := (J.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hJ (norm_nonneg v))
  have hj2 : ‖J v‖^2 ≤ k^2*‖v‖^2 := by
    have hs := sq_le_sq₀ (norm_nonneg (J v)) (mul_nonneg hk (norm_nonneg v))
    simpa only [mul_pow] using hs.mpr hj
  have hu := hl.trans (mul_le_mul_of_nonneg_left hj2 ha)
  have he : a*(k^2*‖v‖^2) = (a*k^2)*‖v‖^2 := by ring
  rw [he] at hu
  have hn : ‖v‖^2 ≤ 0 := le_of_not_gt (fun hpos =>
    (not_lt_of_ge (hh.trans hu)) (mul_lt_mul_of_pos_right hab hpos))
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg v]
end Hilbert

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- Tracial singular-value comparison through an explicitly bounded whitening
map. Regularity and the exact factorization are the only map hypotheses. -/
theorem whitening_high_trace (μ : Measure α)
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (A Q J : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmA : ∀ g h, Measurable (fun x => matrix (A x) g h)) (hcA : Covariant A)
    (hmQ : ∀ g h, Measurable (fun x => matrix (Q x) g h)) (hcQ : Covariant Q)
    (hmJ : ∀ g h, Measurable (fun x => matrix (J x) g h)) (hcJ : Covariant J)
    (M N : ℝ) (hM : ∀ x, ‖A x‖ ≤ M) (hN : ∀ x, ‖Q x‖ ≤ N)
    (hfactor : ∀ x, (A x).comp (J x) = Q x)
    {a b k : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k) (hJ : ∀ x, ‖J x‖ ≤ k) (hab : a*k^2 < b) :
    trace μ (fun x => (highAt ((Q x).adjoint.comp (Q x)) b).starProjection) ≤
      trace μ (fun x => (highAt ((A x).adjoint.comp (A x)) a).starProjection) := by
  have hsa (T : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) : IsSelfAdjoint (T.adjoint.comp T) := by
    rw [isSelfAdjoint_iff']
    simp only [adjoint_comp, adjoint_adjoint]
  have hnorm (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : ℝ) (hC : ∀ x, ‖T x‖ ≤ C) (x : α) :
      ‖(T x).adjoint.comp (T x)‖ ≤ C^2 := by
    rw [norm_adjoint_comp_self]
    nlinarith [hC x, norm_nonneg (T x)]
  have hrA := highAt_regular (fun x => (A x).adjoint.comp (A x))
    (matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hmA) hmA)
    (covariant_comp _ _ (covariant_adjoint _ hcA) hcA) (fun x => hsa (A x))
    (M^2) (hnorm A M hM) a
  have hrQ := highAt_regular (fun x => (Q x).adjoint.comp (Q x))
    (matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hmQ) hmQ)
    (covariant_comp _ _ (covariant_adjoint _ hcQ) hcQ) (fun x => hsa (Q x))
    (N^2) (hnorm Q N hN) b
  apply trace_le_of_injective_map μ hmp _ _ hrQ.1 hrQ.2
    (fun x => (highAt ((A x).adjoint.comp (A x)) a).starProjection.comp (J x))
    (matrix_comp_measurable _ _ hrA.1 hmJ) (covariant_comp _ _ hrA.2 hcJ) k
  · intro x
    exact (opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_right
      (highAt ((A x).adjoint.comp (A x)) a).starProjection_norm_le (norm_nonneg (J x))).trans
        (by simpa only [one_mul] using hJ x))
  · intro x v hv hz
    exact whitening_high_injective (A x) (Q x) (J x) (hfactor x) ha hk (hJ x) hab hv hz
  · intro x v _
    exact (highAt ((A x).adjoint.comp (A x)) a).starProjection_apply_mem (J x v)

#print axioms whitening_high_injective
#print axioms whitening_high_trace

end QuantitativeSpectralWhiteningMinmax
