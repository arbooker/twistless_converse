module

public import QuantitativeEulerEndpointLevelOneCuspV1
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

open UpperHalfPlane Filter FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction
open scoped ModularForm MatrixGroups Manifold Topology

/-- The Fourier function appearing literally in paper2's small-level theorem. -/
def fourierFunction (k : ℕ) (f : ℕ → ℂ) (z : ℍ) : ℂ :=
  fourier (fullCoefficients f k) z

theorem fourierFunction_eq_series (k : ℕ) (f : ℕ → ℂ) (z : ℍ) :
    fourierFunction k f z = ∑' n : ℕ,
      (f n * (((n : ℝ) ^ (((k : ℝ)-1)/2) : ℝ) : ℂ)) *
        Complex.exp (2*Real.pi*Complex.I*(n : ℂ)*(z : ℂ)) := by
  rw [fourierFunction, fourier_eq_exp]
  rfl

/-- The target is genuine Mathlib modular-form membership, including
holomorphy at every cusp, not just a list of transformation equations. -/
def IsModular (N k : ℕ) (f : ℕ → ℂ) : Prop :=
  ∃ F : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) (k : ℤ),
    (F : ℍ → ℂ) = fourierFunction k f

/-- Exact scope of paper2-Astra.tex thm:small-levels. This is the proposition
to be proved; declaring the proposition is not a proof of it. -/
def SmallLevelsTheorem : Prop :=
  ∀ N k : ℕ, 0 < N → N ≤ 36 → N ≠ 29 → N ≠ 31 → 0 < k → Even k →
    ∀ f : ℕ → ℂ, IsSolution N k f → IsModular N k f

theorem fourierFunction_holomorphic {N k : ℕ} {f : ℕ → ℂ}
    (hf : IsSolution N k f) : MDiff (fourierFunction k f) := by
  obtain ⟨τ, _, hg⟩ := hf.growth
  intro z
  exact (FinitenessFourierConstruction.holomorphic (polynomial_bound hf.zero hg k)
    z.im_pos).mdifferentiableAt.comp z (mdifferentiable_coe z)

theorem fourierFunction_zeroAtInfty {N k : ℕ} {f : ℕ → ℂ}
    (hf : IsSolution N k f) : IsZeroAtImInfty (fourierFunction k f) := by
  obtain ⟨τ, _, hg⟩ := hf.growth
  have hs := (FinitenessPolynomialSeries.has_series
    (polynomial_bound hf.zero hg k)).differentiableAt.continuousAt
  have hq := ((Function.Periodic.qParam_tendsto (by norm_num : (0:ℝ)<1)).mono_right
    nhdsWithin_le_nhds).comp tendsto_coe_atImInfty
  have hh := hs.tendsto.comp hq
  rw [FinitenessPolynomialSeries.zero (fullCoefficients_zero hf.zero k)] at hh
  exact hh

theorem level_one_eq_SL :
    (CongruenceSubgroup.Gamma0 1 : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  apply le_antisymm
  · rintro g ⟨γ, _, rfl⟩
    exact ⟨γ, rfl⟩
  · rintro g ⟨γ, rfl⟩
    exact ⟨γ, by change (γ 1 0 : ZMod 1)=0; exact Subsingleton.elim _ _, rfl⟩

/-- The level-one case already follows from the checked original-input
construction; the other 33 levels remain separate proof obligations. -/
theorem level_one {k : ℕ} (heven : Even k) {f : ℕ → ℂ} (hf : IsSolution 1 k f) :
    IsModular 1 k f := by
  obtain ⟨m, hm⟩ := heven
  have hk : k=2*m := by omega
  rw [hk] at hf ⊢
  unfold IsModular
  rw [level_one_eq_SL]
  exact ⟨CuspForm.toModularFormₗ (QuantitativeEulerEndpointLevelOne.solutionCusp m ⟨f, hf⟩), rfl⟩

#print axioms fourierFunction_eq_series
#print axioms fourierFunction_holomorphic
#print axioms fourierFunction_zeroAtInfty
#print axioms level_one

end SmallLevelOriginal
