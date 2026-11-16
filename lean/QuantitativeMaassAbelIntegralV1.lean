module

public import QuantitativeMaassRadialSeedV1
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Square substitution removes the square-root singularity of the Abel
integral. Its derivative and support properties are proved below. -/
def abelIntegral (f : ℝ → ℂ) (q : ℝ) : ℂ :=
  ∫ s in Ioi (0:ℝ), f (q+s^2)

/-- One compact integration interval works for all nearby parameters. -/
theorem quadratic_support_uniform (f : ℝ → ℂ) (hf : HasCompactSupport f) (q₀ : ℝ) :
    ∃ R : ℝ, 0<R ∧ ∀ q∈Ioo (q₀-1) (q₀+1),
      Function.support (fun s : ℝ => f (q+s^2))⊆Icc (-R) R := by
  obtain ⟨C,hCpos,hC⟩ := hf.isBounded.exists_pos_norm_le
  let R := Real.sqrt (C+|q₀|+1)
  have hR : 0<R := Real.sqrt_pos.mpr (by positivity)
  refine ⟨R,hR,?_⟩
  intro q hq s hs
  have hb := hC (q+s^2) (subset_tsupport f hs)
  rw [Real.norm_eq_abs] at hb
  have hh : s^2≤R^2 := by
    dsimp [R]
    rw [Real.sq_sqrt (by positivity : 0≤C+|q₀|+1)]
    have hval := (le_abs_self (q+s^2)).trans hb
    nlinarith [neg_abs_le q₀,hq.1]
  have ha : |s|≤R := (sq_le_sq₀ (abs_nonneg s) hR.le).mp (by simpa only [sq_abs] using hh)
  exact abs_le.mp ha

theorem quadratic_compactSupport (f : ℝ → ℂ) (hf : HasCompactSupport f) (q : ℝ) :
    HasCompactSupport (fun s : ℝ => f (q+s^2)) := by
  obtain ⟨R,_,hR⟩ := quadratic_support_uniform f hf q
  exact (isCompact_Icc : IsCompact (Icc (-R) R)).of_isClosed_subset isClosed_closure
    (closure_minimal (hR q ⟨by linarith,by linarith⟩) isClosed_Icc)

theorem quadratic_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (q : ℝ) :
    Integrable (fun s : ℝ => f (q+s^2)) :=
  (hf.comp (by fun_prop)).integrable_of_hasCompactSupport (quadratic_compactSupport f hc q)

/-- Differentiation under the actual Abel integral, with the uniform
integrable bound constructed from compact support rather than assumed. -/
theorem abelIntegral_hasDerivAt (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (q : ℝ) :
    HasDerivAt (abelIntegral f) (abelIntegral (deriv f) q) q := by
  have hf' : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  obtain ⟨R,hRpos,hR⟩ := quadratic_support_uniform (deriv f) hc.deriv q
  obtain ⟨C,hC⟩ := hc.deriv.exists_bound_of_continuous hf'.continuous
  let bound : ℝ → ℝ := (Icc (-R) R).indicator (fun _ => C)
  have hbi : Integrable bound (volume : Measure ℝ) := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const isCompact_Icc.measure_ne_top
  have hd (s x : ℝ) : HasDerivAt (fun v => f (v+s^2)) (deriv f (x+s^2)) x := by
    simpa only [Function.comp_def,one_smul,id_eq] using
      (((hf.differentiable (by simp)) (x+s^2)).hasDerivAt.scomp x
        ((hasDerivAt_id x).add_const (s^2)))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=volume.restrict (Ioi (0:ℝ))) (F:=fun x s : ℝ => f (x+s^2))
    (F':=fun x s : ℝ => deriv f (x+s^2)) (bound:=bound)
    (s:=Ioo (q-1) (q+1)) (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun x => (hf.continuous.comp (by fun_prop)).aestronglyMeasurable))
    (quadratic_integrable f hf.continuous hc q).integrableOn
    (hf'.continuous.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall (fun s x hx => by
      by_cases hs : s∈Icc (-R) R
      · simpa only [bound,indicator_of_mem hs] using hC (x+s^2)
      · have hz : deriv f (x+s^2)=0 := by
          by_contra hn
          exact hs (hR x hx hn)
        simp only [bound,indicator_of_notMem hs,hz,norm_zero,le_refl]))
    hbi.integrableOn (Eventually.of_forall (fun s x _ => hd s x))
  exact h.2

#print axioms quadratic_support_uniform
#print axioms quadratic_compactSupport
#print axioms abelIntegral_hasDerivAt

end QuantitativeMaass
