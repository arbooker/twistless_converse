module

public import QuantitativeMaassHilbertSchmidtV1

set_option autoImplicit false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

open scoped InnerProductSpace

namespace QuantitativeMaass

variable {G H E ι κ η : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem rectangular_finite_adjoint_energy_le [Fintype κ]
    (bG : HilbertBasis ι ℂ G) (v : κ → H) (hv : Orthonormal ℂ v)
    (A : G →L[ℂ] H) (hA : Summable (fun i => ‖A (bG i)‖^2)) :
    (∑ j, ‖A.adjoint (v j)‖^2) ≤ ∑' i, ‖A (bG i)‖^2 := by
  classical
  have hh : HasSum (fun i => ∑ j, ‖inner ℂ (v j) (A (bG i))‖^2)
      (∑ j, ‖A.adjoint (v j)‖^2) := by
    have hp := hasSum_sum (fun j (_ : j ∈ (Finset.univ : Finset κ)) =>
      hasSum_inner_norm_sq bG (A.adjoint (v j)))
    simpa only [A.adjoint_inner_left] using hp
  rw [← hh.tsum_eq]
  apply hh.summable.tsum_le_tsum _ hA
  intro i
  simpa using hv.sum_inner_products_le (s := Finset.univ) (A (bG i))

theorem rectangular_adjoint_energy_le (bG : HilbertBasis ι ℂ G) (bH : HilbertBasis κ ℂ H)
    (A : G →L[ℂ] H) (hA : Summable (fun i => ‖A (bG i)‖^2)) :
    Summable (fun j => ‖A.adjoint (bH j)‖^2) ∧
      (∑' j, ‖A.adjoint (bH j)‖^2) ≤ ∑' i, ‖A (bG i)‖^2 := by
  classical
  have hfinite (s : Finset κ) :
      ∑ j ∈ s, ‖A.adjoint (bH j)‖^2 ≤ ∑' i, ‖A (bG i)‖^2 := by
    have hh := rectangular_finite_adjoint_energy_le bG (fun j : s => bH j)
      (bH.orthonormal.comp Subtype.val Subtype.val_injective) A hA
    calc
      _ = ∑ j : s, ‖A.adjoint (bH j)‖^2 :=
        (Finset.sum_coe_sort s (fun j => ‖A.adjoint (bH j)‖^2)).symm
      _ ≤ _ := hh
  have hs := summable_of_sum_le (fun _ => sq_nonneg _) hfinite
  exact ⟨hs,hs.tsum_le_of_sum_le hfinite⟩

theorem rectangular_adjoint_energy_eq (bG : HilbertBasis ι ℂ G) (bH : HilbertBasis κ ℂ H)
    (A : G →L[ℂ] H) (hA : Summable (fun i => ‖A (bG i)‖^2)) :
    Summable (fun j => ‖A.adjoint (bH j)‖^2) ∧
      (∑' j, ‖A.adjoint (bH j)‖^2) = ∑' i, ‖A (bG i)‖^2 := by
  obtain ⟨hs,hle⟩ := rectangular_adjoint_energy_le bG bH A hA
  have hge := (rectangular_adjoint_energy_le bH bG A.adjoint hs).2
  simp only [ContinuousLinearMap.adjoint_adjoint] at hge
  exact ⟨hs,le_antisymm hle hge⟩

/-- The right ideal bound works between different quotient Hilbert
spaces. It is derived from finite Bessel inequalities and adjoints. -/
theorem rectangular_right_comp_energy_le (bG : HilbertBasis ι ℂ G)
    (bH : HilbertBasis κ ℂ H) (bE : HilbertBasis η ℂ E)
    (A : G →L[ℂ] H) (C : E →L[ℂ] G)
    (hA : Summable (fun i => ‖A (bG i)‖^2)) :
    Summable (fun j => ‖A (C (bE j))‖^2) ∧
      (∑' j, ‖A (C (bE j))‖^2) ≤ ‖C‖^2*(∑' i, ‖A (bG i)‖^2) := by
  obtain ⟨hs,he⟩ := rectangular_adjoint_energy_eq bG bH A hA
  have hpoint (i : κ) : ‖C.adjoint (A.adjoint (bH i))‖^2 ≤
      ‖C‖^2*‖A.adjoint (bH i)‖^2 := by
    have h := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      (C.adjoint.le_opNorm (A.adjoint (bH i)))
    simpa only [mul_pow,ContinuousLinearMap.adjoint.norm_map] using h
  have hca : Summable (fun i => ‖C.adjoint (A.adjoint (bH i))‖^2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hpoint (hs.mul_left (‖C‖^2))
  have hsum := hca.tsum_le_tsum hpoint (hs.mul_left (‖C‖^2))
  rw [tsum_mul_left,he] at hsum
  obtain ⟨hc,hce⟩ := rectangular_adjoint_energy_eq bH bE (C.adjoint.comp A.adjoint) hca
  simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply] at hc hce
  exact ⟨hc,hce.trans_le hsum⟩

#print axioms rectangular_adjoint_energy_eq
#print axioms rectangular_right_comp_energy_le

end QuantitativeMaass
