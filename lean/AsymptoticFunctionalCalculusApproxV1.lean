module

public import AsymptoticPolarIsometryV1
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFunctionalCalculus

open Filter Polynomial
open scoped Topology

variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Functional calculus on a complex Hilbert space, with its real scalar
structure fixed by restriction from the complex field. -/
noncomputable def value (f : ℝ → ℝ) (B : H →L[ℂ] H) : H →L[ℂ] H := cfc f B

noncomputable def positiveRoot (B : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt B

theorem positiveRoot_eq_value (B : H →L[ℂ] H) (hB : 0≤B) :
    positiveRoot B=value Real.sqrt B := by
  unfold positiveRoot value
  rw [CFC.sqrt_eq_real_sqrt B hB,cfcₙ_eq_cfc]

/-- A scalar polynomial approximation on a common spectral interval
approximates every self-adjoint operator in the bounded family. -/
theorem polynomial_error (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (M : ℝ) (hM : ‖B‖≤M)
    (f : ℝ → ℝ) (hf : Continuous f) (p : ℝ[X]) {ε : ℝ} (hε : 0≤ε)
    (hp : ∀ t∈Set.Icc (-M) M,|p.eval t-f t|≤ε) :
    ‖aeval B p-value f B‖≤ε := by
  rcases subsingleton_or_nontrivial H with htriv | hnontriv
  · have he : aeval B p-value f B=0 := Subsingleton.elim _ _
    simpa only [he,norm_zero] using hε
  ·
    unfold value
    rw [← cfc_polynomial p B hB,← cfc_sub p.eval f B p.continuous.continuousOn hf.continuousOn]
    apply norm_cfc_le hε
    intro t ht
    have hb : |t|≤M := (spectrum.norm_le_norm_of_mem ht).trans hM
    exact hp t (abs_le.mp hb)

/-- One sequence of real polynomials approximates continuous functional
calculus pointwise in operator norm for a uniformly bounded family.
No measurability assumption is needed for this analytic statement. -/
theorem exists_polynomial_approximation (B : α → H →L[ℂ] H)
    (hB : ∀ x,IsSelfAdjoint (B x)) (M : ℝ) (hM : ∀ x,‖B x‖≤M)
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ p : ℕ → ℝ[X],∀ x,Tendsto (fun n => aeval (B x) (p n)) atTop (𝓝 (value f (B x))) := by
  have hp (n : ℕ) : ∃ p : ℝ[X],∀ t∈Set.Icc (-M) M,|p.eval t-f t|<1/((n:ℝ)+1) :=
    exists_polynomial_near_of_continuousOn (-M) M f hf.continuousOn _ (by positivity)
  choose p hp using hp
  refine ⟨p,fun x => ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply squeeze_zero (fun n => norm_nonneg _) _ he
  intro n
  exact polynomial_error (B x) (hB x) M (hM x) f hf (p n) (by positivity)
    (fun t ht => (hp n t ht).le)

#print axioms positiveRoot_eq_value
#print axioms polynomial_error
#print axioms exists_polynomial_approximation

end AsymptoticFunctionalCalculus
