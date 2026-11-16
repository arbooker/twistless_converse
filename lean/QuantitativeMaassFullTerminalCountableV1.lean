module

public import QuantitativeMaassTerminalCountableV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory
open AsymptoticClassicalPetersson
namespace QuantitativeMaass

/-- The full terminal space has a countable Hilbert basis through its
actual isometric inclusion into the translation cylinder. -/
theorem exists_countable_full_terminal_basis (δ : ℝ) :
    ∃ (ι : Type),Countable ι ∧ Nonempty (HilbertBasis ι ℂ (AsymptoticCylinderTerminal.Space δ)) := by
  obtain ⟨w,b,_⟩ := exists_hilbertBasis ℂ (AsymptoticCylinderTerminal.Space δ)
  let U := productCylinderToTranslation.comp (AsymptoticCylinderTerminal.Space δ).subtypeₗᵢ
  have hb : Orthonormal ℂ (fun i => U (b i)) := U.orthonormal_comp_iff.mpr b.orthonormal
  exact ⟨w,orthonormal_countable_index _ hb,⟨b⟩⟩

theorem exists_countable_cylinder_basis :
    ∃ (ι : Type),Countable ι ∧ Nonempty (HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0))) := by
  obtain ⟨w,b,_⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 (quotientMeasure 0))
  exact ⟨w,orthonormal_countable_index b b.orthonormal,⟨b⟩⟩

#print axioms exists_countable_full_terminal_basis
#print axioms exists_countable_cylinder_basis
end QuantitativeMaass
