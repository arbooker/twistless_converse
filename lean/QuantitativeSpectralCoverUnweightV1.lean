module

public import QuantitativeSpectralCongruenceCoverV1
public import QuantitativeSpectralModularHeightV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralCoverUnweight

open Matrix UpperHalfPlane Set MeasureTheory
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticCompactBranch
open QuantitativeHolomorphic QuantitativeSpectralModularHeight QuantitativeSpectralCongruenceCover
open scoped MatrixGroups ENNReal lp

/-- A constant depending only on the actual finite list of integral
congruence representatives, never on the truncation height. -/
theorem exists_cover_entry_bound (N : ℕ) (hN : 0 < N) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      MatrixEntryBound (q.out⁻¹).val B := by
  let : NeZero N := ⟨hN.ne'⟩
  let f := fun p : (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) × Fin 2 × Fin 2 =>
    |((p.1.out⁻¹).val p.2.1 p.2.2 : ℝ)|
  obtain ⟨B,hB⟩ := (Set.finite_range f).bddAbove
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro q i j
  exact (hB ⟨(q,i,j),rfl⟩).trans (le_max_right _ _)

def coverBound (N : ℕ) (hN : 0 < N) : ℝ := Classical.choose (exists_cover_entry_bound N hN)

theorem coverBound_one_le (N : ℕ) (hN : 0 < N) : 1 ≤ coverBound N hN :=
  (Classical.choose_spec (exists_cover_entry_bound N hN)).1

theorem coverBound_entry (N : ℕ) (hN : 0 < N)
    (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    MatrixEntryBound (q.out⁻¹).val (coverBound N hN) :=
  (Classical.choose_spec (exists_cover_entry_bound N hN)).2 q

/-- On the concrete compact congruence cover every coordinate has a
polynomial lower-height bound, including the neighborhoods of finite cusps. -/
theorem compactCover_height_lower (N : ℕ) (hN : 0 < N) (H : ℝ)
    {z : ℍ} (hz : z ∈ compactCover N H) :
    ((1:ℝ)/4)/((coverBound N hN)^2*(H+2)^2) ≤ z.im := by
  obtain ⟨q,w,hw,rfl⟩ := mem_iUnion.mp hz
  dsimp only at *
  rw [← map_inv, integralLabel_action]
  exact modular_height_lower q.out⁻¹ (by linarith [coverBound_one_le N hN])
    (coverBound_entry N hN q) (by norm_num) w
    (abs_le.mpr ⟨by linarith [hw.1],hw.2.1⟩) hw.2.2.1 hw.2.2.2

/-- Uniform polynomial cost of removing the actual weight on the compact
cover. This is a statement about the literal cap and actual Gamma0 images. -/
theorem compactCover_cap_inverse (N : ℕ) (hN : 0 < N) (H : ℝ)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) {z : ℍ} (hz : z ∈ compactCover N H) :
    (cap ε t z)⁻¹ ≤ (max 1 (4*ε*(coverBound N hN)^2*(H+2)^2))^t := by
  obtain ⟨q,w,hw,rfl⟩ := mem_iUnion.mp hz
  dsimp only at *
  rw [← map_inv, integralLabel_action]
  have hh := cap_inverse_modular q.out⁻¹ (by linarith [coverBound_one_le N hN])
    (coverBound_entry N hN q) (by norm_num : (0:ℝ)<1/4) hε t w
    (abs_le.mpr ⟨by linarith [hw.1],hw.2.1⟩) hw.2.2.1 hw.2.2.2
  convert hh using 1
  ring_nf

/-- The concrete unweighting coefficient, with a genuine compact cutoff. -/
def coefficient (N : ℕ) (H ε : ℝ) (t : ℕ) : ℍ → ℂ :=
  (compactCover N H).indicator (fun z => Complex.ofReal ((cap ε t z)⁻¹))

theorem coefficient_measurable (N : ℕ) (hN : 0 < N) (H ε : ℝ) (t : ℕ) :
    Measurable (coefficient N H ε t) :=
  (Complex.measurable_ofReal.comp (cap_continuous ε t).measurable.inv).indicator
    (compactCover_compact N hN H).measurableSet

theorem coefficient_norm_le (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ}
    (hε : 0 < ε) (t : ℕ) (z : ℍ) :
    ‖coefficient N H ε t z‖ ≤ (max 1 (4*ε*(coverBound N hN)^2*(H+2)^2))^t := by
  classical
  by_cases hz : z ∈ compactCover N H
  · rw [coefficient, Set.indicator_of_mem hz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (cap_pos hε t z))]
    exact compactCover_cap_inverse N hN H hε t hz
  · rw [coefficient, Set.indicator_of_notMem hz, norm_zero]
    positivity

#print axioms compactCover_height_lower
#print axioms compactCover_cap_inverse
#print axioms coefficient_norm_le

end QuantitativeSpectralCoverUnweight
