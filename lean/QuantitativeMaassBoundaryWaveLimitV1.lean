module

public import QuantitativeMaassCoshWavePacketV1
public import QuantitativeMaassPositiveTimeApproximationV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem arcosh_boundary_radius_tendsto {ι : Type*} (l : Filter ι) (a : ι → ℝ)
    (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => Real.arcosh (1+2*a i)) l (𝓝 0) := by
  have ht : Tendsto (fun i => 1+2*a i) l (𝓝 1) := by
    simpa only [mul_zero,add_zero] using (ha0.const_mul 2).const_add 1
  have hwithin : Tendsto (fun i => 1+2*a i) l (𝓝[Ici 1] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall (fun i => by
      change 1≤1+2*a i; have h := ha i; linarith)⟩
  have h := (Real.continuousOn_arcosh 1 (by simp)).tendsto.comp hwithin
  have hz : Real.arcosh 1=0 := by simpa only [Real.cosh_zero] using Real.arcosh_cosh (le_refl (0:ℝ))
  simpa only [hz,Function.comp_def] using h

/-- The actual spectral packet of the discarded endpoint part tends to zero
in operator norm, with the exceptional-spectrum weight fully controlled. -/
theorem boundaryWavePacket_tendsto {ι : Type*} (l : Filter ι)
    (N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => boundaryWavePacket N F hF R hR hs (a i)) l (𝓝 0) := by
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hF.continuous
  have hB0 : 0≤B := (norm_nonneg (F 0)).trans (hB 0)
  apply (tendsto_zero_iff_norm_tendsto_zero
    (f:=fun i => boundaryWavePacket N F hF R hR hs (a i))).mpr
  have ht := arcosh_boundary_radius_tendsto l a ha ha0
  have hb : Tendsto (fun i => (B*Real.cosh (Real.arcosh (1+2*a i)/2))*
      (2*Real.arcosh (1+2*a i))) l (𝓝 0) := by
    have h := ((Real.continuous_cosh.tendsto _).comp (ht.div_const 2)).const_mul B
    simpa only [zero_div,Real.cosh_zero,mul_one,mul_zero,Function.comp_def] using h.mul (ht.const_mul 2)
  exact squeeze_zero (fun i => norm_nonneg (boundaryWavePacket N F hF R hR hs (a i)))
    (fun i => boundaryWavePacket_norm N F hF R hR hs B hB0 hB (a i) (ha i)) hb

def puncturedWavePacket (N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (a : ℝ) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  coshWavePacket N (fun q => F q-abelBoundaryPart F a q)
    (hF.sub (abelBoundaryPart_smooth F hF a)) R hR
    (support_sub_Iic F (abelBoundaryPart F a) _ hs (abelBoundaryPart_support_source F a _ hs))

theorem puncturedWavePacket_eq_sub (N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (a : ℝ) :
    puncturedWavePacket N F hF R hR hs a=
      coshWavePacket N F hF R hR hs-boundaryWavePacket N F hF R hR hs a :=
  coshWavePacket_sub N F (abelBoundaryPart F a) hF (abelBoundaryPart_smooth F hF a)
    R hR hs (abelBoundaryPart_support_source F a _ hs)

/-- The same cutoff approximation converges on the spectral side. -/
theorem puncturedWavePacket_tendsto {ι : Type*} (l : Filter ι)
    (N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => puncturedWavePacket N F hF R hR hs (a i)) l
      (𝓝 (coshWavePacket N F hF R hR hs)) := by
  apply (tendsto_iff_norm_sub_tendsto_zero
    (f:=fun i => puncturedWavePacket N F hF R hR hs (a i))
    (b:=coshWavePacket N F hF R hR hs)).mpr
  have he (i : ι) : ‖puncturedWavePacket N F hF R hR hs (a i)-coshWavePacket N F hF R hR hs‖=
      ‖boundaryWavePacket N F hF R hR hs (a i)‖ := by
    rw [puncturedWavePacket_eq_sub]
    have hh : (coshWavePacket N F hF R hR hs-boundaryWavePacket N F hF R hR hs (a i))-
        coshWavePacket N F hF R hR hs= -boundaryWavePacket N F hF R hR hs (a i) := by abel
    rw [hh]
    exact norm_neg (boundaryWavePacket N F hF R hR hs (a i))
  simp_rw [he]
  exact (tendsto_zero_iff_norm_tendsto_zero
    (f:=fun i => boundaryWavePacket N F hF R hR hs (a i))).mp
      (boundaryWavePacket_tendsto l N F hF hc R hR hs a ha ha0)

#print axioms arcosh_boundary_radius_tendsto
#print axioms boundaryWavePacket_tendsto
#print axioms puncturedWavePacket_tendsto

end QuantitativeMaass
