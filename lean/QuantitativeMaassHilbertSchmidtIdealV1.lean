module

public import QuantitativeMaassHilbertSchmidtV1

set_option autoImplicit false

@[expose] public section

open scoped InnerProduct BigOperators

namespace QuantitativeMaass

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]

theorem finite_orthonormal_energy_le [Fintype κ] (b : HilbertBasis ι ℂ H)
    (v : κ → H) (hv : Orthonormal ℂ v) (B : H →L[ℂ] H)
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)) :
    (∑ j, ‖B (v j)‖ ^ 2) ≤ hilbertSchmidtEnergy b B := by
  obtain ⟨hs, he⟩ := adjoint_energy_eq b B hB
  have hh := finite_adjoint_energy_le b v hv B.adjoint hs
  simpa only [ContinuousLinearMap.adjoint_adjoint, he] using hh

theorem energy_change_basis_le (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H)
    (B : H →L[ℂ] H) (hB : Summable (fun i => ‖B (b i)‖ ^ 2)) :
    Summable (fun j => ‖B (c j)‖ ^ 2) ∧
    hilbertSchmidtEnergy c B ≤ hilbertSchmidtEnergy b B := by
  classical
  have hfinite (s : Finset κ) : ∑ j ∈ s, ‖B (c j)‖ ^ 2 ≤ hilbertSchmidtEnergy b B := by
    calc
      _ = ∑ j : s, ‖B (c j)‖ ^ 2 :=
        (Finset.sum_coe_sort s (fun j => ‖B (c j)‖ ^ 2)).symm
      _ ≤ hilbertSchmidtEnergy b B := finite_orthonormal_energy_le b (fun j : s => c j)
        (c.orthonormal.comp Subtype.val Subtype.val_injective) B hB
  have hs := summable_of_sum_le (fun _ => sq_nonneg _) hfinite
  exact ⟨hs, hs.tsum_le_of_sum_le hfinite⟩

/-- The energy is independent of the chosen Hilbert basis, with summability
transported as part of the conclusion. -/
theorem energy_change_basis (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H)
    (B : H →L[ℂ] H) (hB : Summable (fun i => ‖B (b i)‖ ^ 2)) :
    Summable (fun j => ‖B (c j)‖ ^ 2) ∧
    hilbertSchmidtEnergy c B = hilbertSchmidtEnergy b B := by
  obtain ⟨hs, hle⟩ := energy_change_basis_le b c B hB
  exact ⟨hs, le_antisymm hle (energy_change_basis_le c b B hs).2⟩

omit [CompleteSpace H] in
theorem left_comp_energy_bound (b : HilbertBasis ι ℂ H) (C B : H →L[ℂ] H)
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)) :
    Summable (fun i => ‖(C.comp B) (b i)‖ ^ 2) ∧
    hilbertSchmidtEnergy b (C.comp B) ≤ ‖C‖ ^ 2 * hilbertSchmidtEnergy b B := by
  have hpoint (i : ι) : ‖(C.comp B) (b i)‖ ^ 2 ≤ ‖C‖ ^ 2 * ‖B (b i)‖ ^ 2 := by
    simpa only [mul_pow, ContinuousLinearMap.comp_apply] using
      pow_le_pow_left₀ (norm_nonneg _) (C.le_opNorm (B (b i))) 2
  have hmajor := hB.mul_left (‖C‖ ^ 2)
  have hs := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hpoint hmajor
  refine ⟨hs, ?_⟩
  unfold hilbertSchmidtEnergy
  rw [← hB.tsum_mul_left]
  exact hs.tsum_le_tsum hpoint hmajor

theorem right_comp_energy_bound (b : HilbertBasis ι ℂ H) (B C : H →L[ℂ] H)
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)) :
    Summable (fun i => ‖(B.comp C) (b i)‖ ^ 2) ∧
    hilbertSchmidtEnergy b (B.comp C) ≤ ‖C‖ ^ 2 * hilbertSchmidtEnergy b B := by
  obtain ⟨hs, he⟩ := adjoint_energy_eq b B hB
  obtain ⟨hc, hbound⟩ := left_comp_energy_bound b C.adjoint B.adjoint hs
  obtain ⟨hresult, henergy⟩ := adjoint_energy_eq b (C.adjoint.comp B.adjoint) hc
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] at hresult henergy
  refine ⟨hresult, ?_⟩
  rw [henergy]
  simpa only [ContinuousLinearMap.adjoint.norm_map, he] using hbound

#print axioms finite_orthonormal_energy_le
#print axioms energy_change_basis_le
#print axioms energy_change_basis
#print axioms left_comp_energy_bound
#print axioms right_comp_energy_bound

end QuantitativeMaass
