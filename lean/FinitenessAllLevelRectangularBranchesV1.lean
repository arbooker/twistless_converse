module

public import FinitenessAllLevelEliminantBranchesV1
public import FinitenessAllLevelRectangularAlgebraV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCoefficientRing

open Complex Set Filter
open scoped Topology

variable {ι σ : Type*} {U : Set ℂ} (g : ι → ℂ → ℂ)

/-- Scalar implicit functions assemble into an exact local graph for the
rectangular system, retaining all the equations on the graph. -/
theorem rectangular_branch [Fintype σ]
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U) (q : σ → Polynomial (ring U g))
    (w : U) (v : σ → ℂ)
    (hs : ∀ i, ((q i).map (evaluation U g w)).Separable)
    (hv : ∀ i, (q i).eval₂ (evaluation U g w) (v i) = 0) :
    ∃ B : ℂ → (σ → ℂ), B w = v ∧ AnalyticAt ℂ B w ∧
      (∀ᶠ z in 𝓝 w.val, ∀ i, polynomialEquation g (q i) (z, B z i) = 0) ∧
      ∀ᶠ t in 𝓝 (w.val, v),
        (∀ i, polynomialEquation g (q i) (t.1, t.2 i) = 0) ↔ t.2 = B t.1 := by
  classical
  have hb i := eliminant_root_branch g hg (q i) w (v i) (hs i) (hv i)
  choose b hb ha hz hu using hb
  refine ⟨fun z i => b i z, funext hb, AnalyticAt.pi ha,
    Filter.eventually_all.mpr hz, ?_⟩
  have hall : ∀ᶠ t : ℂ × (σ → ℂ) in 𝓝 (w.val, v), ∀ i,
      polynomialEquation g (q i) (t.1, t.2 i) = 0 ↔ b i t.1 = t.2 i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun t : ℂ × (σ → ℂ) => (t.1, t.2 i)) (w.val, v) := by
      fun_prop
    exact hc.tendsto.eventually (hu i)
  filter_upwards [hall] with t ht
  constructor
  · intro he
    exact funext (fun i => ((ht i).mp (he i)).symm)
  · intro he i
    exact (ht i).mpr (congrFun he i).symm

/-- A continuous residual satisfying X^n S(X)=0 cannot leave zero near a
point where S(0) is nonzero. The certificate is an exact analytic identity. -/
theorem residual_stays_zero
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U) (s : Polynomial (ring U g))
    (n : ℕ) (w : U) (r : ℂ → ℂ) (hr : ContinuousAt r w.val) (hrw : r w = 0)
    (hs : evaluation U g w (s.coeff 0) ≠ 0)
    (he : ∀ᶠ z in 𝓝 w.val, r z ^ n * polynomialEquation g s (z, r z) = 0) :
    ∀ᶠ z in 𝓝 w.val, r z = 0 := by
  have hc : ContinuousAt (fun z : ℂ => polynomialEquation g s (z, r z)) w.val :=
    (polynomialEquation_analytic g hg s (x := r w) w.property).continuousAt.comp
      (f := fun z : ℂ => (z, r z)) (continuousAt_id.prodMk hr)
  have hn : polynomialEquation g s (w.val, r w) ≠ 0 := by
    rw [hrw, polynomialEquation_eq]
    simpa only [Polynomial.eval₂_at_zero] using hs
  filter_upwards [he, hc.eventually_ne hn] with z hz hnz
  exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hz).resolve_right hnz)

#print axioms rectangular_branch
#print axioms residual_stays_zero

end FinitenessAllLevelCoefficientRing
