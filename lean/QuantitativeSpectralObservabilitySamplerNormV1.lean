module

public import QuantitativeSpectralObservabilityDecodedV1
public import QuantitativeSpectralIdentityFoldV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open Matrix UpperHalfPlane Set ContinuousLinearMap
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open QuantitativeHolomorphic QuantitativeSpectralCoverUnweight
open QuantitativeSpectralModularCoordinate
open QuantitativeSpectralObservabilityDecoded QuantitativeSpectralObservabilitySampling
open scoped MatrixGroups

theorem wide_modular_norm_upper (g : SL(2,ℤ)) {B H : ℝ} (hB : 0≤B)
    (hg : MatrixEntryBound g.val B) (z : ℍ) (hre : |z.re|≤2)
    (hlo : (1:ℝ)/4≤z.im) (hhi : z.im≤H) :
    ‖((g • z : ℍ):ℂ)‖≤4*B*(H+3) := by
  have hz : ‖(z:ℂ)‖≤H+2 := by
    have h := Complex.norm_le_abs_re_add_abs_im (z:ℂ)
    change ‖(z:ℂ)‖≤|z.re|+|z.im| at h
    rw [abs_of_pos z.im_pos] at h
    linarith
  have hn : ‖(g 0 0:ℂ)*(z:ℂ)+(g 0 1:ℂ)‖≤B*(H+3) := by
    calc
      _ ≤ ‖(g 0 0:ℂ)*(z:ℂ)‖+‖(g 0 1:ℂ)‖ := norm_add_le _ _
      _ = |(g 0 0:ℝ)| *‖(z:ℂ)‖+|(g 0 1:ℝ)| := by
        rw [norm_mul,Complex.norm_intCast,Complex.norm_intCast]
      _ ≤ B*(H+2)+B := add_le_add (mul_le_mul (hg 0 0) hz (norm_nonneg _) hB) (hg 0 1)
      _ = _ := by ring
  rw [ModularGroup.sl_moeb,coe_smul_of_det_pos (by simp)]
  change ‖((g 0 0:ℂ)*(z:ℂ)+(g 0 1:ℂ))/denom g z‖≤_
  rw [norm_div]
  have hd := denom_lower g z hlo
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) hd)).mpr
  have hH : 0≤H+3 := by linarith [z.im_pos]
  have hb : 0≤B*(H+3) := mul_nonneg hB hH
  nlinarith

theorem wideCompactCover_re_bound (N : ℕ) (hN : 0<N) (H : ℝ)
    {z : ℍ} (hz : z∈wideCompactCover N H) :
    |z.re|≤4*coverBound N hN*(H+3) := by
  obtain ⟨q,w,hw,rfl⟩ := mem_iUnion.mp hz
  dsimp only at *
  rw [←map_inv,integralLabel_action]
  apply (Complex.abs_re_le_norm _).trans
  exact wide_modular_norm_upper q.out⁻¹ (by linarith [coverBound_one_le N hN])
    (coverBound_entry N hN q) w (abs_le.mpr ⟨by linarith [hw.1],hw.2.1⟩)
    hw.2.2.1 hw.2.2.2

/-- Every factor of the actual wide periodic sampler has an explicit
polynomial norm bound, including the folding multiplicity. -/
theorem sampling_polynomial_norm (N : ℕ) (hN : 0<N) (H : ℝ) (hH : 0≤H)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    ‖sampling N hN H hε t x‖≤
      samplingBound N hN H ε t*(8*coverBound N hN*(H+3)+5) := by
  have hC : 0≤4*coverBound N hN*(H+3) := by
    have hb := coverBound_one_le N hN
    positivity
  have hn := QuantitativeSpectralIdentityFold.compact_identity_norm
    (wideCompactCover_compact N hN H) hε t hC
    (fun w hw => wideCompactCover_re_bound N hN H hw) x
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul (sampler_norm N hN H hε t x) hn (norm_nonneg _)
    (samplingBound_nonneg N hN H ε t)).trans_eq
  congr 1
  ring

#print axioms wideCompactCover_re_bound
#print axioms sampling_polynomial_norm

end QuantitativeSpectralObservability
