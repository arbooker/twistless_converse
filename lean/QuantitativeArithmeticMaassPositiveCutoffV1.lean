module

public import QuantitativeArithmeticPositiveCutoffV1
public import QuantitativeMaassWindowRawColumnV1
public import QuantitativeMaassWindowMajorantV1
public import QuantitativeMaassLVCuspidalProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open QuantitativeMaass AsymptoticClassicalPetersson
open scoped InnerProductSpace ENNReal SchwartzMap FourierTransform

namespace QuantitativeArithmeticMaassPositiveCutoff

variable (N : ℕ) [NeZero N] (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
  (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
  (R : ℝ) (hR : 0 < R) (a b : ℝ)

/-- Projecting the actual packet column preserves its coefficient energy
on every vector fixed by the self-adjoint projection. No global diagonal
integrability is used. -/
theorem projected_packet_coefficient_energy
    (P : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hP : P.toLinearMap.IsSymmetric) (v : AutomorphicSpace N) (hv : P v = v) :
    (∫⁻ z, ENNReal.ofReal (‖inner ℂ v
      (P (windowAbelColumn N K he hc R hR a b z))‖^2) ∂quotientMeasure N) =
      ENNReal.ofReal (‖windowWavePacket N K hc R hR a b v‖^2) := by
  have hp (z : ℍ) : inner ℂ v (P (windowAbelColumn N K he hc R hR a b z)) =
      inner ℂ v (windowAbelColumn N K he hc R hR a b z) := by
    have h : inner ℂ (P v) (windowAbelColumn N K he hc R hR a b z) =
        inner ℂ v (P (windowAbelColumn N K he hc R hR a b z)) := hP _ _
    rw [hv] at h
    exact h.symm
  simp_rw [hp, norm_inner_symm v]
  change _ = ENNReal.ofReal (‖(windowWavePacket N K hc R hR a b v).val‖^2)
  rw [QuantitativeArithmeticMaassCuspBand.lp_norm_square_lintegral]
  apply lintegral_congr_ae
  filter_upwards [windowAbelColumn_packet_coeFn N K he hc R hR a b v] with z hz
  rw [hz]

/-- An actual enlarged-window packet gives an explicit normalization of
the finite even Hecke moment. The right side consists of literal projected
column energies on the core and its complement. -/
theorem enlarged_window_eigenmoment_cutoff {ι : Type*} [Fintype ι]
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1)
    (δ : ℝ) (hδ : 0 < δ) (ha : 0 < a - δ) (k : ℕ)
    (htail : (∫ u, |u|^k * K u) / (R*δ)^k ≤ 1)
    (P : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hP : P.toLinearMap.IsSymmetric)
    (T : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hT : T.toLinearMap.IsSymmetric)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hPv : ∀ i, P (v i) = v i) (r t : ι → ℝ)
    (hr : ∀ i, r i ∈ Icc a b)
    (hgraph : ∀ i, FriedrichsGraph N (v i) (((1/4+(r i)^2 : ℝ) : ℂ) • v i))
    (heigen : ∀ i, T (v i) = (t i : ℂ) • v i)
    (d : ℕ) (S : Set ℍ) (hS : MeasurableSet S) :
    ENNReal.ofReal ((1-(∫ u, |u|^k * K u)/(R*δ)^k)^2) *
        ∑ i, ENNReal.ofReal ((t i)^(2*d)) ≤
      (∫⁻ z in S, ENNReal.ofReal (‖(T^d)
        (P (windowAbelColumn N K he hc R hR (a-δ) (b+δ) z))‖^2) ∂quotientMeasure N) +
      ENNReal.ofReal (‖T‖^(2*d)) *
        ∫⁻ z in Sᶜ, ENNReal.ofReal (‖P
          (windowAbelColumn N K he hc R hR (a-δ) (b+δ) z)‖^2) ∂quotientMeasure N := by
  apply QuantitativeArithmeticPositiveCutoff.finite_eigenmoment_cutoff
    (quotientMeasure N) _
    ((P.continuous.comp (windowAbelColumn_continuous N K he hc R hR (a-δ) (b+δ))).stronglyMeasurable)
    T hT v hv t heigen d _ ?_ S hS
  intro i
  simp only [Function.comp_apply]
  rw [projected_packet_coefficient_energy N K he hc R hR (a-δ) (b+δ) P hP (v i) (hPv i)]
  apply ENNReal.ofReal_le_ofReal
  exact enlarged_windowWavePacket_eigen_lower N K hK hm he hc R hR a b δ (r i)
    hδ ha (hr i) k htail (v i) (hv.norm_eq_one i) (hgraph i)

/-- The preceding coefficient identity applies to the actual closed cusp
space without any presumed spectral trace formula. -/
theorem cuspidal_packet_coefficient_energy (hN : 0 < N)
    (v : AutomorphicSpace N) (hv : v ∈ localCuspidalSpace N hN) :
    (∫⁻ z, ENNReal.ofReal (‖inner ℂ v
      (localCuspidalProjection N hN (windowAbelColumn N K he hc R hR a b z))‖^2)
      ∂quotientMeasure N) = ENNReal.ofReal (‖windowWavePacket N K hc R hR a b v‖^2) := by
  apply projected_packet_coefficient_energy N K he hc R hR a b
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (localCuspidalProjection_selfAdjoint N hN)
  · exact Submodule.starProjection_eq_self_iff.mpr hv

#print axioms projected_packet_coefficient_energy
#print axioms enlarged_window_eigenmoment_cutoff
#print axioms cuspidal_packet_coefficient_energy

end QuantitativeArithmeticMaassPositiveCutoff
