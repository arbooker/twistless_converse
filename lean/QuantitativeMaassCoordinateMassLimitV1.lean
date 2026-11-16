module

public import QuantitativeMaassCoordinateEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

namespace QuantitativeMaass
open MaassDifferential

/-- For positive-coordinate seeds with common compact upper support, strong
coordinate mass convergence implies strong hyperbolic mass convergence. -/
theorem compact_upper_mass_tendsto (K : Set ℍ) (hK : IsCompact K)
    (u : ℕ → Point → ℂ) (f : Point → ℂ)
    (hu : ∀ n,Continuous (u n)) (hf : Continuous f)
    (huc : ∀ n,HasCompactSupport (u n)) (hfc : HasCompactSupport f)
    (hup : ∀ n,tsupport (u n)⊆{Z : Point | 0<Z.2})
    (hfp : tsupport f⊆{Z : Point | 0<Z.2})
    (hus : ∀ n,tsupport (upperFunction (u n))⊆K)
    (hfs : tsupport (upperFunction f)⊆K)
    (he : Tendsto (fun n => ∫ Z,‖u n Z-f Z‖^2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z : ℍ,‖upperFunction (u n) z-upperFunction f z‖^2)
      atTop (𝓝 0) := by
  obtain ⟨r,hr,hrK⟩ := hK.exists_forall_le' continuous_im.continuousOn (fun z _ => z.im_pos)
  have hb (n : ℕ) :
      (∫ z : ℍ,‖upperFunction (u n) z-upperFunction f z‖^2)
        ≤(r^2)⁻¹*(∫ Z,‖u n Z-f Z‖^2) := by
    have hp : tsupport (u n-f)⊆{Z : Point | 0<Z.2} :=
      (tsupport_sub (u n) f).trans (union_subset (hup n) hfp)
    have hs : tsupport (upperFunction (u n-f))⊆K :=
      (tsupport_sub (upperFunction (u n)) (upperFunction f)).trans (union_subset (hus n) hfs)
    apply upper_mass_integral_le_cartesian (u n-f) ((hu n).sub hf) ((huc n).sub hfc) hr
    intro Z hZ
    have hz := hp (subset_tsupport _ hZ)
    let z : ℍ := ⟨⟨Z.1,Z.2⟩,hz⟩
    exact hrK z (hs (subset_tsupport _ hZ))
  apply squeeze_zero (fun n => integral_nonneg (fun z => sq_nonneg _)) hb
  simpa only [mul_zero] using he.const_mul ((r^2)⁻¹)

#print axioms compact_upper_mass_tendsto

end QuantitativeMaass
