module

public import QuantitativeMaassCuspidalBasisEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal ContDiff InnerProductSpace

namespace QuantitativeMaass

/-- A positive bounded operator and its positive square root have the same
closed subspace support. This uses the quadratic form, not a spectral basis. -/
theorem positive_sqrt_mem_of_range {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : Submodule ℂ H) [CompleteSpace S]
    (D : H →L[ℂ] H) (hD : 0≤D) (hDS : ∀ x,D x∈S) (x : H) :
    CFC.sqrt D x∈S := by
  have hroot : IsSelfAdjoint (CFC.sqrt D) :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg D)).isSelfAdjoint
  have hz (v : H) (hv : v∈Sᗮ) : CFC.sqrt D v=0 := by
    have hq := positive_sqrt_norm_square D hD v
    rw [(S.mem_orthogonal v).mp hv (D v) (hDS v)] at hq
    have hn : ‖CFC.sqrt D v‖=0 := by
      have hp := norm_nonneg (CFC.sqrt D v)
      simp only [Complex.zero_re] at hq
      nlinarith
    exact norm_eq_zero.mp hn
  rw [←S.orthogonal_orthogonal]
  apply (Sᗮ.mem_orthogonal _).mpr
  intro v hv
  rw [←hroot.adjoint_eq,(CFC.sqrt D).adjoint_inner_right,hz v hv,inner_zero_left]

/-- Positive smoothing supported on a closed invariant subspace has the
same diagonal sum on a full-space basis and a subspace basis. All sums are
nonnegative extended-real sums, so no convergence is assumed. -/
theorem positive_smoothed_trace_two_bases {H ι κ : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : Submodule ℂ H) [CompleteSpace S]
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ S)
    (K D : H →L[ℂ] H) (hK : IsSelfAdjoint K) (hD : 0≤D)
    (hKS : ∀ x∈S,K x∈S) (hDS : ∀ x,D x∈S) :
    (∑' i,ENNReal.ofReal ((inner ℂ (D (K (b i))) (K (b i))).re))=
      ∑' j,ENNReal.ofReal ((inner ℂ (D (K (c j:H))) (K (c j:H))).re) := by
  have hroot : IsSelfAdjoint (CFC.sqrt D) :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg D)).isSelfAdjoint
  have hproj (x : H) : S.starProjection (K (CFC.sqrt D x))=
      K (CFC.sqrt D x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (hKS _ (positive_sqrt_mem_of_range S D hD hDS x))
  have hb := projected_energy_two_bases S b c (K.comp (CFC.sqrt D))
  simp only [hproj,ContinuousLinearMap.adjoint_comp,hroot.adjoint_eq,hK.adjoint_eq,
    ContinuousLinearMap.comp_apply,positive_sqrt_norm_square D hD] at hb
  rw [positive_smoothed_energy b K D hK hD]
  exact hb

/-- The actual projected cosh energy is precisely the scalar spectral sum,
including exceptional energies below one quarter. A genuine cusp eigenbasis
is an explicit input; its construction is a separate theorem. -/
theorem cosh_projected_energy_eq_spectral {ι κ : Type*}
    (N : ℕ) (hN : 0<N) (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (c : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (he : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (c j:AutomorphicSpace N) ((e j:ℂ) • (c j:AutomorphicSpace N)))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hr : ∀ q,star (F q)=F q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∑' i,ENNReal.ofReal (‖localCuspidalProjection N hN
      (coshWavePacket N F hF R hR hs (b i))‖^2))=
      ∑' j,ENNReal.ofReal (‖smoothPacketMultiplier (coshTimeTest F) (e j)‖^2) := by
  have hK : IsSelfAdjoint (coshWavePacket N F hF R hR hs) :=
    Wave.shiftedQuotientWavePacket_isSelfAdjoint N (coshTimeTest F)
      (coshTimeTest_waveWeight F hF R hR hs) (fun t => hr (Real.cosh t))
  have ho : Orthonormal ℂ (fun j => (c j:AutomorphicSpace N)) :=
    c.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  change (∑' i,ENNReal.ofReal (‖(localCuspidalSpace N hN).starProjection
    (coshWavePacket N F hF R hR hs (b i))‖^2))=_
  rw [projected_energy_two_bases (localCuspidalSpace N hN) b c,hK.adjoint_eq]
  apply tsum_congr
  intro j
  change ENNReal.ofReal (‖Wave.shiftedQuotientWavePacket N (coshTimeTest F)
    (coshTimeTest_waveWeight F hF R hR hs) (c j:AutomorphicSpace N)‖^2)=_
  rw [Wave.shiftedQuotientWavePacket_eigen N (coshTimeTest F) _ (he j) (hgraph j),
    norm_smul,ho.norm_eq_one j,mul_one]
  rfl

/-- The literal LV kernel integral equals the actual cuspidal diagonal sum.
No Hecke eigenbasis, trace formula, or trace-finiteness premise is used. -/
theorem actualLVFilter_kernel_trace_eq_cusp_basis {ι κ : Type*} [Countable ι]
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a d : ℤ) (had : (p:ℤ)*a+(N:ℤ)*d=1) (k : ℕ)
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (c : HilbertBasis κ ℂ (localCuspidalSpace N hN))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∫⁻ x,ENNReal.ofReal ((inner ℂ
      (actualLVFilter N p hN hpN a d had k
        (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
          x R hR (abelProfile_support F _ hs))))
      (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
        x R hR (abelProfile_support F _ hs)))).re) ∂quotientMeasure N)=
      ∑' j,ENNReal.ofReal ((inner ℂ
        (actualLVFilter N p hN hpN a d had k (coshWavePacket N F hF R hR hs (c j:AutomorphicSpace N)))
        (coshWavePacket N F hF R hR hs (c j:AutomorphicSpace N))).re) := by
  rw [←coshWavePacket_positive_kernel_trace N b (actualLVFilter N p hN hpN a d had k)
    (actualLVFilter_order N p hN hpN a d had k).1 F hF hc hr R hR hs]
  apply positive_smoothed_trace_two_bases (localCuspidalSpace N hN) b c
  · exact Wave.shiftedQuotientWavePacket_isSelfAdjoint N (coshTimeTest F)
      (coshTimeTest_waveWeight F hF R hR hs) (fun t => hr (Real.cosh t))
  · exact (actualLVFilter_order N p hN hpN a d had k).1
  · intro x hx
    exact shiftedQuotientWavePacket_mem_localCuspidalSpace N hN _ _ x hx
  · exact actualLVFilter_mem_localCuspidalSpace N p hN hpN hNp hpres a d had k

#print axioms positive_sqrt_mem_of_range
#print axioms positive_smoothed_trace_two_bases
#print axioms cosh_projected_energy_eq_spectral
#print axioms actualLVFilter_kernel_trace_eq_cusp_basis

end QuantitativeMaass
