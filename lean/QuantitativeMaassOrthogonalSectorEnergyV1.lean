module

public import QuantitativeMaassHilbertSchmidtIdealV1
public import Mathlib.Analysis.InnerProductSpace.Subspace

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

open scoped InnerProductSpace BigOperators

namespace QuantitativeMaass

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem orthonormal_energy_le (b : HilbertBasis ι ℂ H) (v : κ→H)
    (hv : Orthonormal ℂ v) (B : H→L[ℂ]H)
    (hB : Summable (fun i => ‖B (b i)‖^2)) :
    Summable (fun j => ‖B (v j)‖^2) ∧ (∑' j,‖B (v j)‖^2)≤hilbertSchmidtEnergy b B := by
  classical
  have hfinite (s : Finset κ) : ∑ j∈s,‖B (v j)‖^2≤hilbertSchmidtEnergy b B := by
    rw [←Finset.sum_coe_sort]
    exact finite_orthonormal_energy_le b (fun j : s => v j)
      (hv.comp Subtype.val Subtype.val_injective) B hB
  have hs := summable_of_sum_le (fun _ => sq_nonneg _) hfinite
  exact ⟨hs,hs.tsum_le_of_sum_le hfinite⟩

/-- Orthogonal invariant sectors contribute at most the ambient energy,
with coefficient one, whether or not they span the ambient space. -/
theorem orthogonal_sector_energy_le {α : Type*} {K : α→Type*}
    [∀ a,NormedAddCommGroup (K a)] [∀ a,InnerProductSpace ℂ (K a)]
    [∀ a,CompleteSpace (K a)] {β : α→Type*}
    (L : ∀ a,K a→ₗᵢ[ℂ]H) (hL : OrthogonalFamily ℂ K L)
    (b : HilbertBasis ι ℂ H) (c : ∀ a,HilbertBasis (β a) ℂ (K a))
    (B : H→L[ℂ]H) (D : ∀ a,K a→L[ℂ]K a)
    (hBD : ∀ a x,B (L a x)=L a (D a x))
    (hB : Summable (fun i => ‖B (b i)‖^2)) :
    (∀ a,Summable (fun j => ‖D a (c a j)‖^2)) ∧
    Summable (fun a => hilbertSchmidtEnergy (c a) (D a)) ∧
    (∑' a,hilbertSchmidtEnergy (c a) (D a))≤hilbertSchmidtEnergy b B := by
  have hv := hL.orthonormal_sigma_orthonormal (fun a => (c a).orthonormal)
  obtain ⟨hs,hle⟩ := orthonormal_energy_le b (fun j : Sigma β => L j.1 (c j.1 j.2)) hv B hB
  have he (j : Sigma β) : ‖B (L j.1 (c j.1 j.2))‖^2=‖D j.1 (c j.1 j.2)‖^2 := by
    rw [hBD,LinearIsometry.norm_map]
  have hs' : Summable (fun j : Sigma β => ‖D j.1 (c j.1 j.2)‖^2) := hs.congr he
  refine ⟨hs'.sigma_factor,hs'.sigma,?_⟩
  change (∑' a,∑' j,‖D a (c a j)‖^2)≤_
  rw [←hs'.tsum_sigma]
  simpa only [he] using hle

#print axioms orthonormal_energy_le
#print axioms orthogonal_sector_energy_le

end QuantitativeMaass
