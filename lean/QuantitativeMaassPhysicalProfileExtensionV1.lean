module

public import QuantitativeMaassAbelIntertwiningV1
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A one-sided profile admits a smooth compact representative above any
strictly physical threshold. This makes no extension claim at the endpoint one. -/
theorem physicalProfile_exists_extension (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (B : ℝ)
    (hs : Function.support F ⊆ Iic B) (b : ℝ) (hb : 1 < b) :
    ∃ G : ℝ → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      ∀ x, b ≤ x → G x = F x := by
  let a := (1+b)/2
  have ha : 1 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a]; linarith
  let c := fun x : ℝ => (Real.smoothTransition ((x-a)/(b-a)) : ℂ)
  have hc : ContDiff ℝ ∞ c :=
    Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const (b-a)))
  have hc0 (x : ℝ) (hx : x ≤ a) : c x = 0 := by
    dsimp [c]
    rw [Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_nonneg.mpr hab.le))]
    rfl
  have hc1 (x : ℝ) (hx : b ≤ x) : c x = 1 := by
    dsimp [c]
    rw [Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith))]
    rfl
  let G := fun x => c x * F x
  have hG : ContDiff ℝ ∞ G := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : 1 < x
    · exact hc.contDiffAt.mul ((hF x hx.le).contDiffAt (Ici_mem_nhds hx))
    · have hxa : x < a := (le_of_not_gt hx).trans_lt ha
      have he : G =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
        filter_upwards [Iio_mem_nhds hxa] with y hy
        change c y * F y = 0
        rw [hc0 y hy.le, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  have hsupport : Function.support G ⊆ Icc a B := by
    intro x hx
    constructor
    · by_contra hn
      exact hx (by change c x * F x = 0; rw [hc0 x (le_of_not_ge hn), zero_mul])
    · apply hs
      intro hz
      exact hx (by change c x * F x = 0; rw [hz, mul_zero])
  refine ⟨G, hG, isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal hsupport isClosed_Icc), ?_⟩
  intro x hx
  change c x * F x = F x
  rw [hc1 x hx, one_mul]

/-- The Abel integral at a threshold samples only values strictly above it. -/
theorem abelProfile_congr_above_threshold (F G : ℝ → ℂ) (b : ℝ)
    (he : ∀ x, b < x → F x = G x) (q : ℝ) (hq : b ≤ q) :
    abelProfile F q = abelProfile G q := by
  have hd (v : ℝ) (hv : b < v) : deriv F v = deriv G v := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioi_mem_nhds hv] with w hw
    exact he w hw
  unfold abelProfile abelIntegral
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  apply hd
  have hs0 : 0 < s := hs
  nlinarith [sq_pos_of_pos hs0]

/-- The existing global differential intertwining also holds for a physical
one-sided profile at every interior physical point. -/
theorem abelProfile_laplacian_physical (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (B : ℝ)
    (hs : Function.support F ⊆ Iic B) (q : ℝ) (hq : 1 < q) :
    radialLaplacianProfile (abelProfile F) q =
      (1/4 : ℂ) * abelProfile F q - abelProfile (coshTimeOperator F) q := by
  let b := (1+q)/2
  have hb : 1 < b := by dsimp [b]; linarith
  have hbq : b < q := by dsimp [b]; linarith
  obtain ⟨G,hG,hGc,hGF⟩ := physicalProfile_exists_extension F hF B hs b hb
  have hlocal (x : ℝ) (hx : b < x) : G =ᶠ[𝓝 x] F := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hGF y hy.le
  have hdlocal (x : ℝ) (hx : b < x) : deriv G =ᶠ[𝓝 x] deriv F := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (hlocal y hy).deriv_eq
  have hop (x : ℝ) (hx : b < x) : coshTimeOperator G x = coshTimeOperator F x := by
    simp only [coshTimeOperator, (hlocal x hx).deriv_eq, (hdlocal x hx).deriv_eq]
  have hAb (x : ℝ) (hx : b ≤ x) : abelProfile G x = abelProfile F x :=
    abelProfile_congr_above_threshold G F b (fun y hy => hGF y hy.le) x hx
  have hAbLocal (x : ℝ) (hx : b < x) : abelProfile G =ᶠ[𝓝 x] abelProfile F := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hAb y hy.le
  have hAbDeriv : deriv (abelProfile G) =ᶠ[𝓝 q] deriv (abelProfile F) := by
    filter_upwards [Ioi_mem_nhds hbq] with y hy
    exact (hAbLocal y hy).deriv_eq
  have hlap : radialLaplacianProfile (abelProfile G) q =
      radialLaplacianProfile (abelProfile F) q := by
    simp only [radialLaplacianProfile, (hAbLocal q hbq).deriv_eq, hAbDeriv.deriv_eq]
  rw [← hlap, abelProfile_laplacian G hG hGc, hAb q hbq.le,
    abelProfile_congr_above_threshold (coshTimeOperator G) (coshTimeOperator F) b hop q hbq.le]

#print axioms physicalProfile_exists_extension
#print axioms abelProfile_congr_above_threshold
#print axioms abelProfile_laplacian_physical

end QuantitativeMaass
