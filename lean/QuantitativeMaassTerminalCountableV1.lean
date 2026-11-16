module

public import QuantitativeMaassNonzeroTerminalV1
public import QuantitativeMaassCountableBasisV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open AsymptoticClassicalPetersson
open scoped ENNReal

namespace QuantitativeMaass

/-- The translation-cylinder L2 space is separable despite its infinite
volume: its measure is sigma finite on a countably generated Borel space. -/
instance cylinderLp_secondCountable : SecondCountableTopology (Lp ℂ 2 (quotientMeasure 0)) := by
  let : Fact ((1:ℝ≥0∞)≤2) := ⟨by norm_num⟩
  let : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩
  infer_instance

/-- A countable terminal basis follows from the isometric embedding into
the genuine translation cylinder, independently of any spectral theorem. -/
theorem exists_countable_terminal_nonzero_basis (ε : ℝ) :
    ∃ (ι : Type),Countable ι ∧ Nonempty (HilbertBasis ι ℂ (terminalNonzeroModes ε)) := by
  obtain ⟨w,b,_⟩ := exists_hilbertBasis ℂ (terminalNonzeroModes ε)
  let U := productCylinderToTranslation.comp (terminalNonzeroModes ε).subtypeₗᵢ
  have hb : Orthonormal ℂ (fun i => U (b i)) := U.orthonormal_comp_iff.mpr b.orthonormal
  exact ⟨w,orthonormal_countable_index _ hb,⟨b⟩⟩

#print axioms exists_countable_terminal_nonzero_basis

end QuantitativeMaass
