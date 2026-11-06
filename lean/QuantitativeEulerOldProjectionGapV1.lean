module

public import QuantitativeEulerOldProjectionKernelV1

set_option autoImplicit false
set_option maxHeartbeats 600000
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionBlock

open AsymptoticNestedQuotients AsymptoticQuotientOperators
open scoped lp

variable {G : Type*} [Group G] {H J K S : Subgroup G}
    (hHJ : H ≤ J) (hHK : H ≤ K) (hJS : J ≤ S) (hKS : K ≤ S)
    [Finite (J ⧸ H.subgroupOf J)] [Finite (K ⧸ H.subgroupOf K)]
    [(H.subgroupOf S).FiniteIndex]

include hJS hKS in
/-- A finite actual join block gives a uniform gap on the full infinite
regular coset Hilbert space. The same finite-dimensional constant works
on every translated block, and exact Parseval sums the inequalities. -/
theorem ambient_old_gap :
    ∃ γ : ℝ, 0 < γ ∧ ∀ v : ℓ²(Classes H,ℂ),
      γ * ‖v - (newSpace hHJ hHK).starProjection v‖^2 ≤
        ‖(space hHJ).starProjection v‖^2 + ‖(space hHK).starProjection v‖^2 := by
  obtain ⟨γ, hγ, hg⟩ := QuantitativeNewGap.finite_coset_old_average_gap
    (inside_le (S := S) hHJ) (inside_le (S := S) hHK)
  refine ⟨γ, hγ, ?_⟩
  intro v
  have hb (y : Classes S) :
      γ * ‖cosetBlock (H := H) (S := S) y.out
        (v - (newSpace hHJ hHK).starProjection v)‖^2 ≤
      ‖cosetBlock (H := H) (S := S) y.out ((space hHJ).starProjection v)‖^2 +
      ‖cosetBlock (H := H) (S := S) y.out ((space hHK).starProjection v)‖^2 := by
    rw [map_sub, cosetBlock_new hHJ hHK hJS hKS,
      cosetBlock_old hHJ hJS, cosetBlock_old hHK hKS]
    exact hg (cosetBlock (H := H) (S := S) y.out v)
  have hleft := (cosetBlocks_energy (hHJ.trans hJS)
    (v - (newSpace hHJ hHK).starProjection v)).mul_left γ
  have hright := (cosetBlocks_energy (hHJ.trans hJS) ((space hHJ).starProjection v)).add
    (cosetBlocks_energy (hHJ.trans hJS) ((space hHK).starProjection v))
  exact hasSum_le hb hleft hright

#print axioms ambient_old_gap
end QuantitativeEulerOldProjectionBlock
