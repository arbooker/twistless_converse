module

public import QuantitativeMaassMetricSourceColumnCountV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeMaass
variable {H V ι κ : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The canonical packet's finite energy follows from the actual ambient
finite-energy packet and isometric intertwining; it is not an extra analytic
hypothesis on the canonical spectrum. -/
theorem isometric_packet_summable (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ V)
    (J : V→ₗᵢ[ℂ]H) (B : H→L[ℂ]H) (T : V→L[ℂ]V)
    (hBT : ∀ x,B (J x)=J (T x))
    (hB : Summable (fun i => ‖B (b i)‖^2)) :
    Summable (fun j => ‖T (c j)‖^2) ∧
      hilbertSchmidtEnergy c T≤hilbertSchmidtEnergy b B := by
  classical
  have hfinite (s : Finset κ) : ∑ j∈s,‖T (c j)‖^2≤hilbertSchmidtEnergy b B := by
    have h := finite_orthonormal_energy_le b (fun j : s => J (c j))
      ((c.orthonormal.comp Subtype.val Subtype.val_injective).comp_linearIsometry J) B hB
    simp only [hBT,J.norm_map] at h
    calc
      _ = ∑ j : s,‖T (c j)‖^2 := (Finset.sum_coe_sort s _).symm
      _ ≤ _ := h
  have hs := summable_of_sum_le (fun _ => sq_nonneg _) hfinite
  exact ⟨hs,hs.tsum_le_of_sum_le hfinite⟩

#print axioms isometric_packet_summable
end QuantitativeMaass
