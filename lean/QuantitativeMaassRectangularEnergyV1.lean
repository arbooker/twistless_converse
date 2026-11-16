module

public import QuantitativeMaassFiniteEnergyPerturbationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeMaass

variable {E F H ι κ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

/-- The right ideal estimate for different input and output spaces. In
particular the output may lie outside the input spectral band. -/
theorem rectangular_energy_right (b : OrthonormalBasis ι ℂ E)
    (c : OrthonormalBasis κ ℂ F) (A : F →L[ℂ] H) (B : E →L[ℂ] F) :
    (∑ i,‖A (B (b i))‖^2)≤‖B‖^2*(∑ j,‖A (c j)‖^2) := by
  classical
  let : FiniteDimensional ℂ F := Module.Finite.of_basis c.toBasis
  let V := A.range
  let : FiniteDimensional ℂ V := LinearMap.finiteDimensional_range A.toLinearMap
  let d := stdOrthonormalBasis ℂ V
  have hd (z : F) : ‖A z‖^2=∑ k,‖inner ℂ (d k:H) (A z)‖^2 := by
    exact (d.sum_sq_norm_inner_right ⟨A z,⟨z,rfl⟩⟩).symm
  have hadj : (∑ k,‖A.adjoint (d k:H)‖^2)=∑ j,‖A (c j)‖^2 := by
    calc
      _ = ∑ k,∑ j,‖inner ℂ (A.adjoint (d k:H)) (c j)‖^2 := by
        exact Finset.sum_congr rfl (fun k _ => (c.sum_sq_norm_inner_left _).symm)
      _ = ∑ j,∑ k,‖inner ℂ (d k:H) (A (c j))‖^2 := by
        rw [Finset.sum_comm]
        simp only [A.adjoint_inner_left]
      _ = _ := Finset.sum_congr rfl (fun j _ => (hd (c j)).symm)
  calc
    _ = ∑ k,∑ i,‖inner ℂ (B.adjoint (A.adjoint (d k:H))) (b i)‖^2 := by
      simp_rw [hd]
      rw [Finset.sum_comm]
      simp only [B.adjoint_inner_left,A.adjoint_inner_left]
    _ = ∑ k,‖B.adjoint (A.adjoint (d k:H))‖^2 := by
      exact Finset.sum_congr rfl (fun k _ => b.sum_sq_norm_inner_left _)
    _ ≤ ‖B‖^2*∑ k,‖A.adjoint (d k:H)‖^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      have hh := pow_le_pow_left₀ (norm_nonneg _)
        (B.adjoint.le_opNorm (A.adjoint (d k:H))) 2
      simpa only [mul_pow,ContinuousLinearMap.adjoint.norm_map] using hh
    _ = _ := by rw [hadj]

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace H] [Fintype κ] in
/-- Bounded maps on the output also control rectangular finite-input
energy, without an invariant-range hypothesis. -/
theorem rectangular_energy_left (v : ι → E) (A : F →L[ℂ] H) (B : E →L[ℂ] F) :
    (∑ i,‖A (B (v i))‖^2)≤‖A‖^2*(∑ i,‖B (v i)‖^2) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => by
    simpa only [mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm (B (v i))) 2)

#print axioms rectangular_energy_right
#print axioms rectangular_energy_left

end QuantitativeMaass
