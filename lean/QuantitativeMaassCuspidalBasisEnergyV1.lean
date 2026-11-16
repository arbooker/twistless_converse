module

public import QuantitativeMaassCoshGlobalEnergyV1
public import QuantitativeMaassLVKernelTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal ContDiff

namespace QuantitativeMaass

/-- Parseval and nonnegative Tonelli compare a full-space basis with a
closed-subspace basis. Neither side is assumed finite. -/
theorem projected_energy_two_bases {H ι κ : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : Submodule ℂ H) [CompleteSpace S]
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ S) (K : H →L[ℂ] H) :
    (∑' i,ENNReal.ofReal (‖S.starProjection (K (b i))‖^2))=
      ∑' j,ENNReal.ofReal (‖K.adjoint (c j:H)‖^2) := by
  have hp (x : H) : ‖S.starProjection x‖=‖S.orthogonalProjectionOnto x‖ := rfl
  calc
    _ = ∑' i,∑' j,ENNReal.ofReal (‖inner ℂ (K (b i)) (c j:H)‖^2) := by
      apply tsum_congr
      intro i
      rw [hp,extendedParseval c]
      simp only [S.inner_orthogonalProjectionOnto_eq_of_mem_right]
    _ = ∑' j,∑' i,ENNReal.ofReal (‖inner ℂ (K (b i)) (c j:H)‖^2) := ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro j
      rw [extendedParseval b]
      apply tsum_congr
      intro i
      rw [←K.adjoint_inner_right,norm_inner_symm]

/-- A genuine cuspidal eigenbasis makes the full-space projected energy
finite. Eigenbasis construction is an explicit input supplied separately;
there is no trace-finiteness or quantitative counting premise. -/
theorem cosh_projected_energy_finite_of_cusp_basis {ι κ : Type*}
    (N : ℕ) (hN : 0<N) (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (c : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (he : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (c j:AutomorphicSpace N) ((e j:ℂ) • (c j:AutomorphicSpace N)))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hr : ∀ q,star (F q)=F q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∑' i,ENNReal.ofReal (‖localCuspidalProjection N hN
      (coshWavePacket N F hF R hR hs (b i))‖^2))<(∞:ℝ≥0∞) := by
  have hK : IsSelfAdjoint (coshWavePacket N F hF R hR hs) :=
    Wave.shiftedQuotientWavePacket_isSelfAdjoint N (coshTimeTest F)
      (coshTimeTest_waveWeight F hF R hR hs) (fun t => hr (Real.cosh t))
  have ho : Orthonormal ℂ (fun j => (c j:AutomorphicSpace N)) :=
    c.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  have hsum := cuspidal_cosh_packet_square_summable N hN (fun j => (c j:AutomorphicSpace N))
    ho (fun j => (c j).property) e he hgraph F hF R hR hs
  change (∑' i,ENNReal.ofReal (‖(localCuspidalSpace N hN).starProjection
    (coshWavePacket N F hF R hR hs (b i))‖^2))<(∞:ℝ≥0∞)
  rw [projected_energy_two_bases (localCuspidalSpace N hN) b c,hK.adjoint_eq]
  exact hsum.tsum_ofReal_lt_top

/-- The literal geometric LV integral is finite once the separately
constructed genuine cusp eigenbasis is supplied. The quantitative LV
main term and error estimate are still separate theorems. -/
theorem actualLVFilter_kernel_trace_finite_of_cusp_basis {ι κ : Type*} [Countable ι]
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a d : ℤ) (had : (p:ℤ)*a+(N:ℤ)*d=1) (k : ℕ)
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (c : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ) (he : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (c j:AutomorphicSpace N) ((e j:ℂ) • (c j:AutomorphicSpace N)))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∫⁻ x,ENNReal.ofReal ((inner ℂ
      (actualLVFilter N p hN hpN a d had k
        (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
          x R hR (abelProfile_support F _ hs))))
      (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
        x R hR (abelProfile_support F _ hs)))).re) ∂quotientMeasure N)<(∞:ℝ≥0∞) := by
  exact (actualLVFilter_kernel_trace_le_cuspidal N p hN hpN hNp hpres a d had k b
    F hF hc hr R hR hs).trans_lt
    (cosh_projected_energy_finite_of_cusp_basis N hN b c e he hgraph F hF hr R hR hs)

#print axioms projected_energy_two_bases
#print axioms cosh_projected_energy_finite_of_cusp_basis
#print axioms actualLVFilter_kernel_trace_finite_of_cusp_basis

end QuantitativeMaass
