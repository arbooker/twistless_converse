module

public import AsymptoticRegularCutInverseV1
public import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace Filter
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction
open scoped Topology

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The actual cutoff reconstruction converges in operator norm uniformly
in both the sector and the orbit root. -/
theorem cutFull_tendstoUniformly (hN : 0<N) (P : Parameters A)
    (Y : ℕ → ℝ) (hY0 : ∀ n,0≤Y n) (hY : Tendsto Y atTop (𝓝 0)) :
    TendstoUniformly
      (fun n (ez : Sector N × ℍ) => cutFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier ez.1) (Y n) ez.2)
      (fun ez : Sector N × ℍ => includedFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier ez.1) ez.2) atTop := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let BR := 1+2*AsymptoticCertificateOperators.terminalConstant A P'
  have hd : Tendsto (fun n => Y n/P'.ε*BR) atTop (𝓝 0) := by
    simpa only [zero_div,zero_mul] using (hY.div_const P'.ε).mul_const BR
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  apply ((tendsto_order.mp hd).2 δ hδ).mono
  intro n hn ez
  rw [dist_eq_norm]
  exact (cutFull_error A hN P' (multiplier ez.1) (fun q _ => multiplier_norm ez.1 q) (Y n) (hY0 n) ez.2
    (parameters_contraction A hN P (multiplier ez.1) (fun q _ => multiplier_norm ez.1 q) ez.2)).trans_lt hn

variable {ι : Type*} [Fintype ι]

theorem cutErrorBound_tendsto_zero (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℕ → ℝ) (hY : Tendsto Y atTop (𝓝 0)) :
    Tendsto (fun n => cutErrorBound A hN P r s hs (Y n)) atTop (𝓝 0) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let BR := 1+2*AsymptoticCertificateOperators.terminalConstant A P'
  let BL := observationsBound hN r s hs P'.epsilon_pos (P'.s+4)
  change Tendsto (fun n => (2*BR)*(1+BL^2)*(Y n/P'.ε*BR)) atTop (𝓝 0)
  simpa only [zero_div,zero_mul,mul_zero] using
    ((hY.div_const P'.ε).mul_const BR).const_mul ((2*BR)*(1+BL^2))

theorem cutNormal_tendstoUniformly (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℕ → ℝ)
    (hY0 : ∀ n,0≤Y n) (hY : Tendsto Y atTop (𝓝 0)) :
    TendstoUniformly (fun n (ez : Sector N × ℍ) => cutNormal A hN P r s hs ez.1 (Y n) ez.2)
      (fun ez : Sector N × ℍ => wholeNormal A hN P r s hs ez.1 ez.2) atTop := by
  have hd := cutErrorBound_tendsto_zero A hN P r s hs Y hY
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  apply ((tendsto_order.mp hd).2 δ hδ).mono
  intro n hn ez
  rw [dist_eq_norm]
  exact (cutNormal_error A hN P r s hs ez.1 (Y n) (hY0 n) ez.2).trans_lt hn

theorem cutInverse_tendstoUniformly (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℕ → ℝ)
    (hY0 : ∀ n,0≤Y n) (hYε : ∀ n,Y n≤(AsymptoticReconstructedCount.parameters A P).ε)
    (hY : Tendsto Y atTop (𝓝 0)) :
    TendstoUniformly (fun n (ez : Sector N × ℍ) => cutInverse A hN P r s hs ez.1 (Y n) ez.2)
      (fun ez : Sector N × ℍ => wholeInverse A hN P r s hs ez.1 ez.2) atTop := by
  have hd := cutErrorBound_tendsto_zero A hN P r s hs Y hY
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  apply ((tendsto_order.mp hd).2 δ hδ).mono
  intro n hn ez
  rw [dist_eq_norm]
  exact (cutInverse_error A hN P r s hs ez.1 (Y n) (hY0 n) (hYε n) ez.2).trans_lt hn

#print axioms cutFull_tendstoUniformly
#print axioms cutErrorBound_tendsto_zero
#print axioms cutNormal_tendstoUniformly
#print axioms cutInverse_tendstoUniformly

end AsymptoticRegularObservation
