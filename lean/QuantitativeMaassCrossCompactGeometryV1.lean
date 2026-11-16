module

public import QuantitativeMaassDisplacementSublevelV1
public import QuantitativeMaassCylinderCorrespondenceBoundV1

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels

namespace QuantitativeMaass

/-- A group element carrying a point of one bounded region into another
lies in an explicit orbit set at their common base point. -/
theorem compact_overlap_in_diagonalOrbitSet (N : ℕ) (o : ℍ)
    (K L : Set ℍ) (R S : ℝ)
    (hK : K ⊆ Metric.closedBall o R) (hL : L ⊆ Metric.closedBall o S)
    (γ : gamma N) (hγ : ((fun z : ℍ => γ • z) '' K ∩ L).Nonempty) :
    γ ∈ diagonalOrbitSet N o (R+S) := by
  obtain ⟨y, ⟨⟨x, hx, rfl⟩, hy⟩⟩ := hγ
  have hx' : dist x o ≤ R := hK hx
  have hy' : dist (γ • x) o ≤ S := hL hy
  apply (mem_diagonalOrbitSet N o (R+S) γ).mpr
  have ht := dist_triangle (γ • o) (γ • x) o
  rw [congruence_action_dist, dist_comm o x] at ht
  linarith

/-- Explicit representative-entry control for every retained overlap label. -/
theorem compact_overlap_entry_bound (N : ℕ) (o : ℍ)
    (K L : Set ℍ) (R S : ℝ)
    (hK : K ⊆ Metric.closedBall o R) (hL : L ⊆ Metric.closedBall o S)
    (γ : gamma N) (hγ : ((fun z : ℍ => γ • z) '' K ∩ L).Nonempty)
    (i j : Fin 2) :
    |((representative γ) i j : ℝ)| ≤ Real.exp ((R+S)/2+dist o I) :=
  diagonalOrbitSet_entry_bound N o (R+S) γ
    (compact_overlap_in_diagonalOrbitSet N o K L R S hK hL γ hγ) i j

/-- The number of compact overlap labels has the existing explicit orbit
multiplicity bound, including at cylinder level zero. -/
theorem compact_overlap_card_bound (N : ℕ) (o : ℍ)
    (K L : Set ℍ) (R S : ℝ)
    (hK : K ⊆ Metric.closedBall o R) (hL : L ⊆ Metric.closedBall o S)
    (F : Finset (gamma N))
    (hF : ∀ γ ∈ F, ((fun z : ℍ => γ • z) '' K ∩ L).Nonempty) :
    F.card ≤ QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (R+S) := by
  apply (Finset.card_le_card (show F ⊆ diagonalOrbitSet N o (R+S) from ?_)).trans
    (diagonalOrbitSet_all_card_bound N o (R+S))
  intro γ hγ
  exact compact_overlap_in_diagonalOrbitSet N o K L R S hK hL γ (hF γ hγ)

#print axioms compact_overlap_in_diagonalOrbitSet
#print axioms compact_overlap_entry_bound
#print axioms compact_overlap_card_bound

end QuantitativeMaass
