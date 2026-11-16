module

public import QuantitativeMaassHilbertSchmidtV1
public import Mathlib.Data.Set.Card

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeMaass

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A Hilbert--Schmidt spectral majorant proves finiteness, before a natural
cardinality is used. The family need only be algebraically independent. -/
theorem independent_eigenfamily_finite
    (basis : HilbertBasis ι ℂ H) (B : H →L[ℂ] H)
    (v : κ → H) (hv : LinearIndependent ℂ v) (eigenvalue : κ → ℝ)
    (heigen : ∀ i, B (v i) = (eigenvalue i : ℂ) • v i)
    (hlower : ∀ i, 1 ≤ eigenvalue i)
    (hB : Summable (fun i => ‖B (basis i)‖ ^ 2)) :
    Finite κ ∧ (Nat.card κ : ℝ) ≤ hilbertSchmidtEnergy basis B := by
  classical
  have hfinite : (Set.univ : Set κ).Finite := by
    by_contra hinfinite
    obtain ⟨n,hn⟩ := exists_nat_gt (hilbertSchmidtEnergy basis B)
    obtain ⟨s,_,hs⟩ := Set.Infinite.exists_subset_card_eq hinfinite n
    have hbound := independent_eigenvectors_card_le_energy basis B
      (fun i : s => v i) (hv.comp _ Subtype.val_injective)
      (fun i : s => eigenvalue i) (fun i => heigen i) (fun i => hlower i) hB
    rw [Fintype.card_coe,hs] at hbound
    exact (not_le_of_gt hn) hbound
  let : Finite κ := Set.finite_univ_iff.mp hfinite
  let : Fintype κ := Fintype.ofFinite κ
  refine ⟨inferInstance,?_⟩
  simpa only [Nat.card_eq_fintype_card] using
    independent_eigenvectors_card_le_energy basis B v hv eigenvalue heigen hlower hB

#print axioms independent_eigenfamily_finite

end QuantitativeMaass
