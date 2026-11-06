module

public import AsymptoticCylinderFourierV1
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinder

open MeasureTheory Set Filter AsymptoticFourierNorm
open scoped BigOperators

noncomputable def radialConstant (m t : ℕ) (scale ε : ℝ) : ℝ :=
  (1/ε)^(2*t)*(1/scale)^(m+2*t+1)*((m+2*t).factorial:ℝ)

/-- Polynomially bounded Fourier coefficients have summable L² modes
once the fixed capped weight absorbs their excess growth. -/
theorem coefficient_mode_norm_le (m t d n : ℕ) {scale ε A : ℝ}
    (hs : 0<scale) (hε : 0<ε) (hA : 0≤A) (hdegree : 2*d+4≤m+2*t+1)
    {a : ℂ} (ha : ‖a‖≤A*(n+1:ℕ)^d) :
    ‖a • modeLp m t n hs hε‖≤A*Real.sqrt (radialConstant m t scale ε)*((n+1:ℕ)^2:ℝ)⁻¹ := by
  let q : ℝ := (n+1:ℕ)
  have hq : 0<q := by dsimp [q]; positivity
  have hq1 : 1≤q := by dsimp [q]; exact_mod_cast (show 1≤n+1 by omega)
  have hB : 0≤radialConstant m t scale ε := by unfold radialConstant; positivity
  have hb : beta m t (scale*q) ε≤radialConstant m t scale ε/q^(m+2*t+1) := by
    apply (beta_le_uncapped m t (mul_pos hs hq) hε).trans_eq
    unfold radialConstant
    simp only [div_pow,mul_pow]
    ring
  have hb' : beta m t (scale*q) ε≤radialConstant m t scale ε/q^(2*d+4) := by
    apply hb.trans
    gcongr
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_smul,mul_pow,modeLp_norm_sq]
  have ha' : ‖a‖^2≤(A*q^d)^2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  calc
    ‖a‖^2*beta m t (scale*(n+1:ℕ)) ε ≤ (A*q^d)^2*(radialConstant m t scale ε/q^(2*d+4)) :=
      mul_le_mul ha' hb' (beta_nonneg m t hε) (sq_nonneg _)
    _ = _ := by
      change (A*q^d)^2*(radialConstant m t scale ε/q^(2*d+4))=
        (A*Real.sqrt (radialConstant m t scale ε)*(q^2)⁻¹)^2
      simp only [mul_pow,Real.sq_sqrt hB]
      simp only [pow_add,pow_mul]
      field_simp
      ring

theorem coefficient_modes_summable_norm (m t d : ℕ) {scale ε A : ℝ}
    (hs : 0<scale) (hε : 0<ε) (hA : 0≤A) (hdegree : 2*d+4≤m+2*t+1)
    (a : ℕ → ℂ) (ha : ∀ n,‖a (n+1)‖≤A*(n+1:ℕ)^d) :
    Summable (fun n => ‖a (n+1) • modeLp m t n hs hε‖) := by
  have hp : Summable (fun n : ℕ => ((n:ℝ)^2)⁻¹) := by
    simpa only [one_div] using (Real.summable_one_div_nat_pow (p:=2)).mpr (by omega)
  have hshift : Summable (fun n : ℕ => (((n+1:ℕ):ℝ)^2)⁻¹) := hp.comp_injective Nat.succ_injective
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (hshift.mul_left (A*Real.sqrt (radialConstant m t scale ε)))
  intro n
  exact coefficient_mode_norm_le m t d n hs hε hA hdegree (ha n)

/-- The actual L² sum of the positive Fourier series. -/
noncomputable def fourierSum (m t : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε)
    (a : ℕ → ℂ) : Space := ∑' n,a (n+1) • modeLp m t n hs hε

theorem modeLp_mem_holomorphicSpace (m t n : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    modeLp m t n hs hε∈holomorphicSpace m t hs hε := by
  have hu := (modeInSpace m t n hs hε).property
  have hp := beta_pos m t (mul_pos hs (by positivity : (0:ℝ)<(n+1:ℕ))) hε
  have he : modeLp m t n hs hε=
      (Real.sqrt (beta m t (scale*(n+1:ℕ)) ε):ℂ) • unitMode m t n hs hε := by
    rw [unitMode,smul_smul,mul_inv_cancel₀ (by exact_mod_cast (Real.sqrt_pos.mpr hp).ne'),one_smul]
  rw [he]
  exact (holomorphicSpace m t hs hε).smul_mem _ hu

theorem fourierSum_mem (m t : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) (a : ℕ → ℂ) :
    fourierSum m t hs hε a∈holomorphicSpace m t hs hε := by
  apply tsum_mem (Submodule.isClosed_topologicalClosure _)
  intro n
  exact (holomorphicSpace m t hs hε).smul_mem _ (modeLp_mem_holomorphicSpace m t n hs hε)

/-- Summation in L² agrees almost everywhere with the literal Fourier
series on the cylinder. No arbitrary values on rational orbits are used. -/
theorem fourierSum_coeFn (m t d : ℕ) {scale ε A : ℝ}
    (hs : 0<scale) (hε : 0<ε) (hA : 0≤A) (hdegree : 2*d+4≤m+2*t+1)
    (a : ℕ → ℂ) (ha : ∀ n,‖a (n+1)‖≤A*(n+1:ℕ)^d) :
    fourierSum m t hs hε a =ᵐ[measure] (fun z => ∑' n,a (n+1)*mode m t n scale ε z) := by
  have hh := coefficient_modes_summable_norm m t d hs hε hA hdegree a ha
  have he := Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hh)
  apply he.trans
  have hterms : ∀ᵐ z ∂measure,∀ n,(a (n+1) • modeLp m t n hs hε) z=a (n+1)*mode m t n scale ε z := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [Lp.coeFn_smul (a (n+1)) (modeLp m t n hs hε),modeLp_coeFn m t n hs hε] with z hsm hm
    simp only [hsm,Pi.smul_apply,smul_eq_mul,hm]
  filter_upwards [hterms] with z hz
  exact tsum_congr hz

#print axioms coefficient_modes_summable_norm
#print axioms fourierSum_coeFn

end AsymptoticCylinder
