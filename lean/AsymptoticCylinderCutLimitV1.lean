module

public import AsymptoticCylinderCutPositiveV1
public import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderObservation

open UpperHalfPlane Set ContinuousLinearMap Filter FinitenessCertificate FinitenessGlobalHeight
open AsymptoticSectorSigns AsymptoticReconstructedCount
open AsymptoticCompactObservationCount (Row)
open scoped Topology

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem cutErrorBound_tendsto_zero (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℕ → ℝ) (hY : Tendsto Y atTop (𝓝 0)) :
    Tendsto (fun n => cutErrorBound A hN P r s hs (Y n)) atTop (𝓝 0) := by
  let BR := 1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P)
  let BL := observationsBound A hN P r s hs
  change Tendsto (fun n => (BR+BR)*(1+BR*BR*(1+BL^2))*(Y n/(parameters A P).ε*BR)) atTop (𝓝 0)
  simpa only [zero_div,zero_mul,mul_zero] using
    ((hY.div_const (parameters A P).ε).mul_const BR).const_mul ((BR+BR)*(1+BR*BR*(1+BL^2)))

/-- Cutoff removal is uniform over all holomorphic weights and sectors
for the actual fixed compact observation family. -/
theorem cutPositive_tendstoUniformly (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℕ → ℝ)
    (hY0 : ∀ n,0≤Y n) (hYε : ∀ n,Y n≤(parameters A P).ε) (hY : Tendsto Y atTop (𝓝 0)) :
    TendstoUniformly
      (fun n (he : ℕ × Sector N) => cutPositive A hN P r s hs he.1 he.2 (Y n) (hYε n))
      (fun he : ℕ × Sector N => positive A hN P r s hs he.1 he.2) atTop := by
  have hd := cutErrorBound_tendsto_zero A hN P r s hs Y hY
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  apply ((tendsto_order.mp hd).2 δ hδ).mono
  intro n hn he
  rw [dist_eq_norm]
  exact (cutPositive_error A hN P r s hs he.1 he.2 (Y n) (hY0 n) (hYε n)).trans_lt hn

#print axioms cutErrorBound_tendsto_zero
#print axioms cutPositive_tendstoUniformly

end AsymptoticCylinderObservation
