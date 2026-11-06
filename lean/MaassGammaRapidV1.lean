module

public import MaassParityMellinV1
public import FinitenessBoundaryDecayV1

set_option autoImplicit false

@[expose] public section

open Complex FinitenessBoundaryDecay

namespace MaassMellin

theorem gamma_affine_rapid (ν : ℂ) {c : ℝ} (hc : 0<(c+ν.re)/2) :
    Rapid (fun s => Gamma ((s+ν)/2)) c := by
  have hg : Rapid Gamma ((c+ν.re)/2) := by
    simpa only [ofReal_zero, add_zero] using (gamma_shift (α := 0) (by simpa using hc))
  intro n
  obtain ⟨C0,h0⟩ := hg 0
  obtain ⟨Cn,hn⟩ := hg n
  refine ⟨2^(n-1)*((2:ℝ)^n*Cn+‖ν‖^n*C0), ?_⟩
  intro z hz
  let w := (z+ν)/2
  have hw : w.re=(c+ν.re)/2 := by simp only [w, div_ofNat_re, add_re, hz]
  have hn0 : ‖Gamma w‖≤C0 := by simpa only [pow_zero, one_mul] using h0 w hw
  have hnn := hn w hw
  have he : z=(2:ℂ)*w-ν := by dsimp [w]; ring
  have hzbound : ‖z‖≤2*‖w‖+‖ν‖ := by
    calc
      ‖z‖ = ‖(2:ℂ)*w-ν‖ := congrArg norm he
      _ ≤ ‖(2:ℂ)*w‖+‖ν‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul]; norm_num
  have hp : ‖z‖^n≤2^(n-1)*((2*‖w‖)^n+‖ν‖^n) :=
    (pow_le_pow_left₀ (norm_nonneg _) hzbound n).trans
      (add_pow_le (by positivity) (norm_nonneg _) n)
  calc
    ‖z‖^n*‖Gamma w‖ ≤ (2^(n-1)*((2*‖w‖)^n+‖ν‖^n))*‖Gamma w‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = 2^(n-1)*((2:ℝ)^n*(‖w‖^n*‖Gamma w‖)+‖ν‖^n*‖Gamma w‖) := by
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hnn (by positivity))
        (mul_le_mul_of_nonneg_left hn0 (by positivity))) (by positivity)

theorem realGammaPair_rapid {ν : ℂ} {c : ℝ} (hc : |ν.re|<c) :
    Rapid (realGammaPair ν) c := by
  have ha : 0<(c+ν.re)/2 := by linarith [neg_abs_le ν.re]
  have hb : 0<(c-ν.re)/2 := by linarith [le_abs_self ν.re]
  have hk : 0≤(Real.pi)^(-c)*Real.Gamma ((c-ν.re)/2) :=
    mul_nonneg (Real.rpow_pos_of_pos Real.pi_pos _).le (Real.Gamma_pos_of_pos hb).le
  apply of_norm_le (gamma_affine_rapid ν ha) hk
  intro z hz
  have hpi : (Real.pi:ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : realGammaPair ν z = (Real.pi:ℂ)^(-z)*Gamma ((z+ν)/2)*Gamma ((z-ν)/2) := by
    have hp : (Real.pi:ℂ)^(-(z+ν)/2)*(Real.pi:ℂ)^(-(z-ν)/2) = (Real.pi:ℂ)^(-z) := by
      rw [← cpow_add _ _ hpi]
      congr 1
      ring
    unfold realGammaPair Gammaℝ
    calc
      _ = ((Real.pi:ℂ)^(-(z+ν)/2)*(Real.pi:ℂ)^(-(z-ν)/2))*Gamma ((z+ν)/2)*Gamma ((z-ν)/2) := by ring
      _ = _ := by rw [hp]
  have hg := FinitenessGammaDecay.norm_le_real (s := (z-ν)/2)
    (by simpa only [div_ofNat_re, sub_re, hz] using hb)
  simp only [div_ofNat_re, sub_re, hz] at hg
  rw [he, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos Real.pi_pos, neg_re, hz]
  nlinarith [mul_le_mul_of_nonneg_left hg
    (mul_nonneg (Real.rpow_pos_of_pos Real.pi_pos (-c)).le (norm_nonneg (Gamma ((z+ν)/2))))]

#print axioms gamma_affine_rapid
#print axioms realGammaPair_rapid

end MaassMellin
