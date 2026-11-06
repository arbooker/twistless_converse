module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Tactic

set_option autoImplicit false

@[expose] public section

open scoped InnerProduct ComplexConjugate BigOperators
open InnerProductSpace

namespace QuantitativeMaass

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Squared Hilbert--Schmidt energy in a specified ambient Hilbert basis.
All theorems using this real-valued sum require summability explicitly. -/
noncomputable def hilbertSchmidtEnergy (b : HilbertBasis ι ℂ H) (B : H →L[ℂ] H) : ℝ :=
  ∑' i, ‖B (b i)‖ ^ 2

/-- Parseval in nonnegative real form, without finite-dimensionality. -/
theorem hasSum_inner_norm_sq (b : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i => ‖⟪x, b i⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
  have hh := Complex.hasSum_re (b.hasSum_inner_mul_inner x x)
  have hnorm : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  rw [hnorm] at hh
  convert hh using 1
  funext i
  change ‖⟪x, b i⟫_ℂ‖ ^ 2 = RCLike.re (⟪x, b i⟫_ℂ * ⟪b i, x⟫_ℂ)
  rw [inner_mul_symm_re_eq_norm, norm_mul, norm_inner_symm (b i) x]
  ring

/-- Trace/Cauchy proof of the spectral counting inequality. The eigenbasis
`v` is an arbitrary algebraic basis, not assumed orthogonal. Only the test
basis `u` is orthonormal. Real eigenvalues at least one are exactly what
the positive bandlimited window supplies. -/
theorem eigenbasis_card_le_energy [Fintype ι] [Fintype κ]
    (v : Module.Basis ι ℂ H) (u : OrthonormalBasis κ ℂ H)
    (B : H →ₗ[ℂ] H) (eigenvalue : ι → ℝ)
    (heigen : ∀ i, B (v i) = (eigenvalue i : ℂ) • v i)
    (hlower : ∀ i, 1 ≤ eigenvalue i) :
    (Fintype.card ι : ℝ) ≤ ∑ j, ‖B (u j)‖ ^ 2 := by
  classical
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis u.toBasis, Module.finrank_eq_card_basis v]
  have ht : LinearMap.trace ℂ H B = ∑ i, (eigenvalue i : ℂ) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ v, Matrix.trace]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.diag, LinearMap.toMatrix_apply]
    rw [heigen, map_smul]
    simp
  have hu : LinearMap.trace ℂ H B = ∑ j, ⟪u j, B (u j)⟫_ℂ := by
    rw [LinearMap.trace_eq_matrix_trace ℂ u.toBasis]
    simp [Matrix.trace, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
  have hsum : (Fintype.card ι : ℝ) ≤ ∑ j, ‖B (u j)‖ := by
    calc
      _ = ∑ i : ι, (1 : ℝ) := by simp
      _ ≤ ∑ i, eigenvalue i := Finset.sum_le_sum (fun i _ => hlower i)
      _ = (LinearMap.trace ℂ H B).re := by rw [ht]; simp
      _ = ∑ j, (⟪u j, B (u j)⟫_ℂ).re := by rw [hu]; simp
      _ ≤ ∑ j, ‖B (u j)‖ := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ ≤ ‖⟪u j, B (u j)⟫_ℂ‖ := Complex.re_le_norm _
          _ ≤ ‖u j‖ * ‖B (u j)‖ := norm_inner_le_norm _ _
          _ = ‖B (u j)‖ := by rw [u.orthonormal.norm_eq_one j, one_mul]
  have hcauchy : (∑ j, ‖B (u j)‖) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ j, ‖B (u j)‖ ^ 2 := by
    simpa [hcard] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : κ => (1 : ℝ)) (fun j => ‖B (u j)‖)
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  by_cases hz : Fintype.card ι = 0
  · simp only [hz, Nat.cast_zero]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Nat.pos_of_ne_zero hz
    nlinarith [sq_nonneg ((∑ j, ‖B (u j)‖) - Fintype.card ι)]

theorem finite_adjoint_energy_le [CompleteSpace H] [Fintype κ]
    (b : HilbertBasis ι ℂ H) (v : κ → H) (hv : Orthonormal ℂ v)
    (B : H →L[ℂ] H) (hB : Summable (fun i => ‖B (b i)‖ ^ 2)) :
    (∑ j, ‖B.adjoint (v j)‖ ^ 2) ≤ hilbertSchmidtEnergy b B := by
  classical
  have hh : HasSum (fun i => ∑ j, ‖⟪v j, B (b i)⟫_ℂ‖ ^ 2)
      (∑ j, ‖B.adjoint (v j)‖ ^ 2) := by
    have hp := hasSum_sum (fun j (_ : j ∈ (Finset.univ : Finset κ)) =>
      hasSum_inner_norm_sq b (B.adjoint (v j)))
    simpa only [B.adjoint_inner_left] using hp
  rw [← hh.tsum_eq]
  apply hh.summable.tsum_le_tsum _ hB
  intro i
  simpa using hv.sum_inner_products_le (s := Finset.univ) (B (b i))

theorem invariant_energy_le_ambient [CompleteSpace H] [Fintype κ]
    (b : HilbertBasis ι ℂ H) (W : Submodule ℂ H)
    (u : OrthonormalBasis κ ℂ W) (B : H →L[ℂ] H)
    (hW : ∀ w ∈ W, B w ∈ W)
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)) :
    (∑ j, ‖B (u j : H)‖ ^ 2) ≤ hilbertSchmidtEnergy b B := by
  classical
  have hu : Orthonormal ℂ (fun j => (u j : H)) :=
    u.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hp (j : κ) : ‖B (u j : H)‖ ^ 2 =
      ∑ k, ‖⟪(u k : H), B (u j : H)⟫_ℂ‖ ^ 2 := by
    exact (u.sum_sq_norm_inner_right ⟨B (u j : H), hW _ (u j).property⟩).symm
  calc
    _ = ∑ j, ∑ k, ‖⟪(u k : H), B (u j : H)⟫_ℂ‖ ^ 2 :=
      Finset.sum_congr rfl (fun j _ => hp j)
    _ = ∑ k, ∑ j, ‖⟪B.adjoint (u k : H), (u j : H)⟫_ℂ‖ ^ 2 := by
      rw [Finset.sum_comm]
      simp only [B.adjoint_inner_left]
    _ ≤ ∑ k, ‖B.adjoint (u k : H)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [norm_inner_symm] using
        hu.sum_inner_products_le (s := Finset.univ) (B.adjoint (u k : H))
    _ ≤ hilbertSchmidtEnergy b B := finite_adjoint_energy_le b _ hu B hB

theorem adjoint_energy_le [CompleteSpace H] (b : HilbertBasis ι ℂ H)
    (B : H →L[ℂ] H) (hB : Summable (fun i => ‖B (b i)‖ ^ 2)) :
    Summable (fun i => ‖B.adjoint (b i)‖ ^ 2) ∧
    hilbertSchmidtEnergy b B.adjoint ≤ hilbertSchmidtEnergy b B := by
  classical
  have hfinite (s : Finset ι) :
      ∑ i ∈ s, ‖B.adjoint (b i)‖ ^ 2 ≤ hilbertSchmidtEnergy b B := by
    have hh := finite_adjoint_energy_le b (fun i : s => b i)
      (b.orthonormal.comp Subtype.val Subtype.val_injective) B hB
    calc
      _ = ∑ j : s, ‖B.adjoint (b j)‖ ^ 2 :=
        (Finset.sum_coe_sort s (fun i => ‖B.adjoint (b i)‖ ^ 2)).symm
      _ ≤ hilbertSchmidtEnergy b B := hh
  have hs := summable_of_sum_le (fun _ => sq_nonneg _) hfinite
  exact ⟨hs, hs.tsum_le_of_sum_le hfinite⟩

/-- Hilbert--Schmidt energy is invariant under adjoint. The proof uses
finite Bessel inequalities, so neither a double-sum exchange nor an
unproved trace-class identity is hidden in this statement. -/
theorem adjoint_energy_eq [CompleteSpace H] (b : HilbertBasis ι ℂ H)
    (B : H →L[ℂ] H) (hB : Summable (fun i => ‖B (b i)‖ ^ 2)) :
    Summable (fun i => ‖B.adjoint (b i)‖ ^ 2) ∧
    hilbertSchmidtEnergy b B.adjoint = hilbertSchmidtEnergy b B := by
  obtain ⟨hs, hle⟩ := adjoint_energy_le b B hB
  have hge := (adjoint_energy_le b B.adjoint hs).2
  simp only [ContinuousLinearMap.adjoint_adjoint] at hge
  exact ⟨hs, le_antisymm hle hge⟩

/-- The counting bound for an arbitrary independent finite family of
eigenvectors in an infinite-dimensional Hilbert space. -/
theorem independent_eigenvectors_card_le_energy [CompleteSpace H] [Fintype κ]
    (b : HilbertBasis ι ℂ H) (B : H →L[ℂ] H)
    (v : κ → H) (hv : LinearIndependent ℂ v) (eigenvalue : κ → ℝ)
    (heigen : ∀ i, B (v i) = (eigenvalue i : ℂ) • v i)
    (hlower : ∀ i, 1 ≤ eigenvalue i)
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)) :
    (Fintype.card κ : ℝ) ≤ hilbertSchmidtEnergy b B := by
  classical
  let W := Submodule.span ℂ (Set.range v)
  let basis : Module.Basis κ ℂ W := Module.Basis.span hv
  let : FiniteDimensional ℂ W := Module.Finite.of_basis basis
  have hW : ∀ w ∈ W, B w ∈ W := by
    intro w hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨i, rfl⟩
      rw [heigen]
      exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
    · simp
    · intro x y _ _ hx hy
      simpa only [map_add] using W.add_mem hx hy
    · intro a x _ hx
      simpa only [map_smul] using W.smul_mem a hx
  let D : W →ₗ[ℂ] W := B.toLinearMap.restrict hW
  have he (i : κ) : D (basis i) = (eigenvalue i : ℂ) • basis i := by
    apply Subtype.ext
    change B ((Module.Basis.span hv i : W) : H) =
      (eigenvalue i : ℂ) • ((Module.Basis.span hv i : W) : H)
    simpa only [Module.Basis.coe_span_apply] using heigen i
  have hfinite := eigenbasis_card_le_energy basis (stdOrthonormalBasis ℂ W) D
    eigenvalue he hlower
  exact hfinite.trans (invariant_energy_le_ambient b W (stdOrthonormalBasis ℂ W) B hW hB)

theorem projected_output_summable [CompleteSpace H] (b : HilbertBasis ι ℂ H)
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (B : H →L[ℂ] H) (hB : Summable (fun i => ‖B (b i)‖ ^ 2)) :
    Summable (fun i => ‖W.starProjection (B (b i))‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hB
  intro i
  exact pow_le_pow_left₀ (norm_nonneg _) (W.norm_starProjection_apply_le _) 2

/-- Exact energy splitting by orthogonal output subspaces. -/
theorem output_projection_energy_split [CompleteSpace H] (b : HilbertBasis ι ℂ H)
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (B : H →L[ℂ] H) (hB : Summable (fun i => ‖B (b i)‖ ^ 2)) :
    hilbertSchmidtEnergy b B =
      hilbertSchmidtEnergy b (W.starProjection.comp B) +
      hilbertSchmidtEnergy b (Wᗮ.starProjection.comp B) := by
  unfold hilbertSchmidtEnergy
  simp only [ContinuousLinearMap.comp_apply]
  rw [← (projected_output_summable b W B hB).tsum_add
    (projected_output_summable b Wᗮ B hB)]
  apply tsum_congr
  intro i
  exact Submodule.norm_sq_eq_add_norm_sq_starProjection (B (b i)) W

/-- Exact source splitting. Cross terms vanish after the full Hilbert--Schmidt
sum, even though the two output vectors for an individual basis vector need
not be orthogonal. No multiplicative constant is lost on the target term. -/
theorem source_projection_energy_split [CompleteSpace H] (b : HilbertBasis ι ℂ H)
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (B : H →L[ℂ] H) (hB : Summable (fun i => ‖B (b i)‖ ^ 2)) :
    hilbertSchmidtEnergy b B =
      hilbertSchmidtEnergy b (B.comp W.starProjection) +
      hilbertSchmidtEnergy b (B.comp Wᗮ.starProjection) := by
  have hadj := adjoint_energy_eq b B hB
  have hleft := adjoint_energy_eq b (W.starProjection.comp B.adjoint)
    (projected_output_summable b W B.adjoint hadj.1)
  have hright := adjoint_energy_eq b (Wᗮ.starProjection.comp B.adjoint)
    (projected_output_summable b Wᗮ B.adjoint hadj.1)
  have hP : W.starProjection.adjoint = W.starProjection :=
    (isSelfAdjoint_starProjection W).adjoint_eq
  have hQ : Wᗮ.starProjection.adjoint = Wᗮ.starProjection :=
    (isSelfAdjoint_starProjection Wᗮ).adjoint_eq
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, hP] at hleft
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, hQ] at hright
  rw [← hadj.2, output_projection_energy_split b W B.adjoint hadj.1,
    ← hleft.2, ← hright.2]

theorem projected_source_summable [CompleteSpace H] (b : HilbertBasis ι ℂ H)
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (B : H →L[ℂ] H) (hB : Summable (fun i => ‖B (b i)‖ ^ 2)) :
    Summable (fun i => ‖B (W.starProjection (b i))‖ ^ 2) := by
  have hs := (adjoint_energy_eq b B hB).1
  have hh := (adjoint_energy_eq b (W.starProjection.comp B.adjoint)
    (projected_output_summable b W B.adjoint hs)).1
  have hP : W.starProjection.adjoint = W.starProjection :=
    (isSelfAdjoint_starProjection W).adjoint_eq
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    hP, ContinuousLinearMap.comp_apply] using hh

#print axioms hasSum_inner_norm_sq
#print axioms eigenbasis_card_le_energy
#print axioms finite_adjoint_energy_le
#print axioms invariant_energy_le_ambient
#print axioms adjoint_energy_le
#print axioms adjoint_energy_eq
#print axioms independent_eigenvectors_card_le_energy
#print axioms projected_output_summable
#print axioms output_projection_energy_split
#print axioms source_projection_energy_split
#print axioms projected_source_summable

end QuantitativeMaass
