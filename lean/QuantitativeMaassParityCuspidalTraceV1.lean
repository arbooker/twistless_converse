module

public import QuantitativeMaassTimeFilteredTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace ENNReal SchwartzMap

namespace QuantitativeMaass

/-- The genuine all-cusp space is mapped onto itself by geometric reflection. -/
theorem reflectionIsometry_map_localCuspidalSpace (N : ℕ) (hN : 0<N) :
    (localCuspidalSpace N hN).map (reflectionIsometry N).toLinearMap=localCuspidalSpace N hN := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact reflectionIsometry_mem_localCuspidalSpace N hN w hw
  · intro hv
    exact ⟨reflectionIsometry N v,reflectionIsometry_mem_localCuspidalSpace N hN v hv,
      reflectionIsometry_involutive N v⟩

/-- The actual orthogonal cusp projection commutes with geometric reflection. -/
theorem reflectionIsometry_localCuspidalProjection_commute (N : ℕ) (hN : 0<N) :
    Commute (reflectionIsometry N).toContinuousLinearMap (localCuspidalProjection N hN) := by
  have he := reflectionIsometry_map_localCuspidalSpace N hN
  have : ((localCuspidalSpace N hN).map (reflectionIsometry N).toLinearMap).HasOrthogonalProjection := by
    rw [he]
    infer_instance
  apply ContinuousLinearMap.ext
  intro v
  have hh := (reflectionIsometry N).map_starProjection (localCuspidalSpace N hN) v
  change reflectionIsometry N ((localCuspidalSpace N hN).starProjection v)=
    (localCuspidalSpace N hN).starProjection (reflectionIsometry N v)
  simpa only [he] using hh

/-- Thus taking an actual cusp projection preserves either reflection parity. -/
theorem parityProjection_localCuspidalProjection_commute (N : ℕ) (hN : 0<N) (σ : ℝ) :
    Commute (parityProjection N σ) (localCuspidalProjection N hN) :=
  parityProjection_commute N σ _ (reflectionIsometry_localCuspidalProjection_commute N hN)

/-- A self-adjoint compression has the expected literal quadratic form. -/
theorem parityCompression_quadratic (N : ℕ) (σ : ℝ)
    (D : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (v : AutomorphicSpace N) :
    inner ℂ ((parityProjection N σ * D * parityProjection N σ) v) v=
      inner ℂ (D (parityProjection N σ v)) (parityProjection N σ v) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (parityProjection_selfAdjoint N σ) _ _

/-- The original-time positive trace on a fixed parity uses the actual LV
polynomial and actual Abel columns. No geometric lower estimate is assumed. -/
theorem timeWavePacket_parity_actualLV_trace {ι : Type*} [Countable ι]
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (a c : ℤ) (hac : (p:ℤ)*a+(N:ℤ)*c=1) (d : ℕ)
    (b : HilbertBasis ι ℂ (AutomorphicSpace N)) (σ : ℝ)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    let L := actualLVFilter N p hN hpN a c hac d
    let P := parityProjection N σ
    let A := Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)
    (∑' i,ENNReal.ofReal ((inner ℂ (L (P (A (b i)))) (P (A (b i)))).re))=
      ∫⁻ x,ENNReal.ofReal ((inner ℂ (L (P (timeAbelColumn N f hc he R hR hs x)))
        (P (timeAbelColumn N f hc he R hR hs x))).re) ∂quotientMeasure N := by
  let L := actualLVFilter N p hN hpN a c hac d
  let P := parityProjection N σ
  have hpos : 0≤P*L*P := by
    have hh := star_left_conjugate_nonneg (actualLVFilter_order N p hN hpN a c hac d).1 P
    change 0≤star P*L*P at hh
    have hp : star P=P := (parityProjection_selfAdjoint N σ).star_eq
    rwa [hp] at hh
  have hh := timeWavePacket_positive_kernel_trace N f hc he hr R hR hs b (P*L*P) hpos
  simp only [P,parityCompression_quadratic] at hh
  exact hh

/-- Actual parity cuspidal energy dominates the original-time geometric LV
trace. Finiteness and a quantitative asymptotic require further estimates. -/
theorem timeWavePacket_parity_actualLV_trace_le_cuspidal {ι : Type*} [Countable ι]
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a c : ℤ) (hac : (p:ℤ)*a+(N:ℤ)*c=1) (d : ℕ)
    (b : HilbertBasis ι ℂ (AutomorphicSpace N)) (σ : ℝ)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    (∫⁻ x,ENNReal.ofReal ((inner ℂ
      (actualLVFilter N p hN hpN a c hac d (parityProjection N σ (timeAbelColumn N f hc he R hR hs x)))
      (parityProjection N σ (timeAbelColumn N f hc he R hR hs x))).re) ∂quotientMeasure N)≤
    ∑' i,ENNReal.ofReal (‖localCuspidalProjection N hN (parityProjection N σ
      (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc) (b i)))‖^2) := by
  rw [← timeWavePacket_parity_actualLV_trace N p hN hpN a c hac d b σ f hc he hr R hR hs]
  apply ENNReal.tsum_le_tsum
  intro i
  exact ENNReal.ofReal_le_ofReal (actualLVFilter_quadratic_bounds N p hN hpN hNp hpres a c hac d _).2

#print axioms reflectionIsometry_map_localCuspidalSpace
#print axioms reflectionIsometry_localCuspidalProjection_commute
#print axioms parityProjection_localCuspidalProjection_commute
#print axioms parityCompression_quadratic
#print axioms timeWavePacket_parity_actualLV_trace
#print axioms timeWavePacket_parity_actualLV_trace_le_cuspidal

end QuantitativeMaass
