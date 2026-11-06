module

public import AsymptoticCylinderCutTraceErrorV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderObservation

open UpperHalfPlane Set Filter FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticReconstructedCount
open AsymptoticCompactObservationCount (Row)
open scoped Topology

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Removing the low-height cutoff changes the normalized actual
holomorphic traces by a quantity tending to zero uniformly in both
weight and sector. The auxiliary Fourier cutoff is chosen first,
then the height cutoff; no large-weight trace limit is assumed. -/
theorem cutHolomorphicTrace_tendstoUniformly (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℕ → ℝ)
    (hY0 : ∀ n,0≤Y n) (hYε : ∀ n,Y n≤(parameters A P).ε) (hY : Tendsto Y atTop (𝓝 0)) :
    TendstoUniformly
      (fun n (he : ℕ × Sector N) => cutHolomorphicTrace A hN P r s hs he.1 he.2 (Y n) (hYε n)/(2*he.1+2:ℕ))
      (fun he : ℕ × Sector N => holomorphicTrace A hN P r s hs he.1 he.2/(2*he.1+2:ℕ)) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  obtain ⟨B,hB⟩ := exists_nat_gt (max 1 (2*traceTailConstant A P/δ))
  have hBr : (0:ℝ)<B := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    ((le_max_left _ _).trans hB.le)
  have hBn : 0<B := by exact_mod_cast hBr
  have ht : traceTailConstant A P/(B:ℝ)<δ/2 := by
    apply (div_lt_iff₀ hBr).mpr
    have hh : 2*traceTailConstant A P/δ<(B:ℝ) := (le_max_right _ _).trans_lt hB
    have hh' := (div_lt_iff₀ hδ).mp hh
    nlinarith
  have hd : Tendsto (fun n => (B:ℝ)*cutErrorBound A hN P r s hs (Y n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (cutErrorBound_tendsto_zero A hN P r s hs Y hY).const_mul (B:ℝ)
  apply ((tendsto_order.mp hd).2 (δ/2) (half_pos hδ)).mono
  intro n hn he
  have hk : (0:ℝ)<(2*he.1+2:ℕ) := by positivity
  rw [dist_eq_norm,← sub_div,norm_div,Real.norm_of_nonneg hk.le]
  apply (cutHolomorphicTrace_normalized_error A hN P r s hs he.1 he.2 (Y n) (hY0 n) (hYε n) B hBn).trans_lt
  linarith

#print axioms cutHolomorphicTrace_tendstoUniformly

end AsymptoticCylinderObservation
