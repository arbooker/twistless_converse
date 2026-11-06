module

public import MaassInverseMellinV1
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option autoImplicit false

@[expose] public section

open MeasureTheory Complex

namespace MaassMellin

noncomputable def realGammaPair (ν s : ℂ) : ℂ := Gammaℝ (s+ν)*Gammaℝ (s-ν)

theorem gammaPair_normalization (ν s : ℂ) :
    realGammaPair ν s = 4 * ((2*Real.pi:ℝ):ℂ)^(-s) * gammaPair ν s := by
  have hpi : (Real.pi:ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp : (Real.pi:ℂ)^(-(s+ν)/2) * (Real.pi:ℂ)^(-(s-ν)/2) = (Real.pi:ℂ)^(-s) := by
    rw [← cpow_add _ _ hpi]
    congr 1
    ring
  have ht : (2:ℂ)^(-s)*(2:ℂ)^(s-2) = (1/4:ℂ) := by
    rw [← cpow_add _ _ (two_ne_zero : (2:ℂ)≠0), show -s+(s-2)=-(2:ℂ) by ring,
      cpow_neg]
    norm_num
  have hm : ((2*Real.pi:ℝ):ℂ)^(-s) = (2:ℂ)^(-s)*(Real.pi:ℂ)^(-s) := by
    simpa only [ofReal_mul, ofReal_ofNat] using
      mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤2) Real.pi_pos.le (-s)
  dsimp only [realGammaPair, Gammaℝ, gammaPair]
  rw [hm]
  calc
    _ = ((Real.pi:ℂ)^(-(s+ν)/2)*(Real.pi:ℂ)^(-(s-ν)/2)) *
        (Gamma ((s+ν)/2)*Gamma ((s-ν)/2)) := by ring
    _ = (Real.pi:ℂ)^(-s)*(Gamma ((s+ν)/2)*Gamma ((s-ν)/2)) := by rw [hp]
    _ = _ := by
      calc
        _ = (4*((2:ℂ)^(-s)*(2:ℂ)^(s-2))) * (Real.pi:ℂ)^(-s) *
            (Gamma ((s+ν)/2)*Gamma ((s-ν)/2)) := by rw [ht]; ring
        _ = _ := by ring

/-- For parity zero/one these are precisely the two archimedean kernels.
The transform identity also holds for every natural shift. -/
noncomputable def parityKernel (p : MaassSpectral.Parameter) (δ : ℕ) (y : ℝ) : ℂ :=
  4*((y:ℂ)^δ*(MaassSpectral.K p (2*Real.pi*y):ℂ))

theorem parity_mellin_convergent (p : MaassSpectral.Parameter) (δ : ℕ)
    {s : ℂ} (hs : 1<s.re) : MellinConvergent (parityKernel p δ) s := by
  have hshift : 1<(s+(δ:ℂ)).re := by
    simp only [add_re, natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) δ]
  have hscale := (MellinConvergent.comp_mul_left
    (by positivity : (0:ℝ)<2*Real.pi)).mpr (actual_mellin_convergent p hshift)
  have hweight := (MellinConvergent.cpow_smul
    (f := fun y => (MaassSpectral.K p (2*Real.pi*y):ℂ)) (s := s) (a := (δ:ℂ))).mpr hscale
  simpa only [MellinConvergent, parityKernel, cpow_natCast, smul_eq_mul] using hweight.const_smul (4:ℂ)

theorem parity_mellin (p : MaassSpectral.Parameter) (δ : ℕ)
    {s : ℂ} (hs : 1<s.re) :
    mellin (parityKernel p δ) s = realGammaPair (MaassSpectral.order p) (s+(δ:ℂ)) := by
  have hshift : 1<(s+(δ:ℂ)).re := by
    simp only [add_re, natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) δ]
  have hf : parityKernel p δ = fun y : ℝ => (4:ℂ) •
      ((y:ℂ)^(δ:ℂ) • (MaassSpectral.K p (2*Real.pi*y):ℂ)) := by
    funext y
    simp only [parityKernel, smul_eq_mul, cpow_natCast]
  rw [hf, mellin_const_smul, mellin_cpow_smul,
    mellin_comp_mul_left (fun y => (MaassSpectral.K p y:ℂ)) _
      (by positivity : (0:ℝ)<2*Real.pi), actual_mellin p hshift]
  rw [gammaPair_normalization]
  dsimp [gammaPair]
  ring

theorem realGammaPair_vertical {ν : ℂ} {c : ℝ} (hc : |ν.re|<c) :
    VerticalIntegrable (realGammaPair ν) c := by
  have hm : Continuous (fun v : ℝ => realGammaPair ν ((c:ℂ)+(v:ℂ)*I)) := by
    simp_rw [gammaPair_normalization]
    apply Continuous.mul _ (gammaPair_line_continuous hc)
    apply continuous_const.mul
    apply Continuous.const_cpow (by fun_prop)
    exact Or.inl (ofReal_ne_zero.mpr (by positivity : (2*Real.pi:ℝ)≠0))
  apply ((gammaPair_vertical hc).norm.const_mul
    (4*((2*Real.pi:ℝ)^(-c)))).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro v
  rw [gammaPair_normalization, norm_mul, norm_mul]
  have hp : ‖((2*Real.pi:ℝ):ℂ)^(-((c:ℂ)+(v:ℂ)*I))‖ = (2*Real.pi:ℝ)^(-c) := by
    simpa using norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ)<2*Real.pi)
      (-((c:ℂ)+(v:ℂ)*I))
  rw [hp]
  norm_num

theorem parity_inverse_mellin (p : MaassSpectral.Parameter) (δ : ℕ)
    {c y : ℝ} (hc : 1<c) (hy : 0<y) :
    mellinInv c (fun s => realGammaPair (MaassSpectral.order p) (s+(δ:ℂ))) y =
      parityKernel p δ y := by
  have hbound : |(MaassSpectral.order p).re|<c+(δ:ℝ) := by
    have h := order_re_bound p
    linarith [Nat.cast_nonneg (α := ℝ) δ]
  have hv : VerticalIntegrable (fun s => realGammaPair (MaassSpectral.order p) (s+(δ:ℂ))) c := by
    apply (realGammaPair_vertical hbound).congr
    apply Filter.Eventually.of_forall
    intro v
    dsimp only
    congr 1
    push_cast
    ring
  have he (v:ℝ) : mellin (parityKernel p δ) ((c:ℂ)+(v:ℂ)*I) =
      realGammaPair (MaassSpectral.order p) (((c:ℂ)+(v:ℂ)*I)+(δ:ℂ)) :=
    parity_mellin p δ (by simpa using hc)
  have hvm : VerticalIntegrable (mellin (parityKernel p δ)) c := by
    exact hv.congr (Filter.Eventually.of_forall (fun v => (he v).symm))
  have hcont : ContinuousAt (parityKernel p δ) y := by
    apply continuousAt_const.mul
    apply (Complex.continuous_ofReal.continuousAt.pow δ).mul
    exact (actual_K_continuousAt p (by positivity : (0:ℝ)<2*Real.pi*y)).comp
      (by fun_prop : ContinuousAt (fun v : ℝ => 2*Real.pi*v) y)
  calc
    _ = mellinInv c (mellin (parityKernel p δ)) y := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun v => by dsimp only; rw [he v])
    _ = _ := mellinInv_mellin_eq c _ hy (parity_mellin_convergent p δ (by simpa using hc)) hvm hcont

#print axioms gammaPair_normalization
#print axioms parity_mellin
#print axioms parity_inverse_mellin

end MaassMellin
