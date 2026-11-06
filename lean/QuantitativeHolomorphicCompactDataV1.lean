module

public import QuantitativeHolomorphicReconstructionMatrixV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open UpperHalfPlane MeasureTheory AsymptoticRationalFreeness
open AsymptoticCompactBranch AsymptoticMobiusFold

/-- The actual regular strip-restricted compact branch has a single
selected fold at each orbit point. In particular its value does not depend
on the auxiliary finite superset of folds or its norm bound. -/
theorem regular_compact_selected (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t)
    (z : ℍ) (f : AsymptoticRegularCompactBranch.Space) (a : AsymptoticRationalGroup.Group) :
    AsymptoticRegularCompactBranch.operator g hg hε t D z f a =
      coefficient (realMatrix g) s ε t (a • z) *
        f (AsymptoticRationalBranches.compactFold g hg
          (Int.floor (realMatrix g • (a • z)).re)*a) := by
  classical
  rw [AsymptoticRegularCompactBranch.operator_apply]
  by_cases ha : a • z ∈ s
  · rw [Finset.sum_eq_single (Int.floor (realMatrix g • (a • z)).re)]
    · rw [AsymptoticOrbitDiagonal.corner_apply]
      have hm : (AsymptoticRationalBranches.compactFold g hg
          (Int.floor (realMatrix g • (a • z)).re)*a) • z ∈ AsymptoticMassTransport.strip := by
        rw [mul_smul,AsymptoticRationalBranches.compactFold_action]
        exact (fold_mem_strip_iff _ _ _).mpr rfl
      rw [ite_eq_left hm]
    · intro n _ hn
      rw [AsymptoticOrbitDiagonal.corner_apply]
      have hm : (AsymptoticRationalBranches.compactFold g hg n*a) • z ∉ AsymptoticMassTransport.strip := by
        rw [mul_smul,AsymptoticRationalBranches.compactFold_action]
        exact (fold_mem_strip_iff _ _ _).not.mpr hn
      rw [ite_eq_right hm,mul_zero]
    · exact fun hn => False.elim (hn (D.fold_mem _ ha))
  · simp [coefficient,ha]

theorem regular_compact_data_independent (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D E : Data (realMatrix g) s ε t) (z : ℍ) :
    AsymptoticRegularCompactBranch.operator g hg hε t D z =
      AsymptoticRegularCompactBranch.operator g hg hε t E z := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext a
  rw [regular_compact_selected,regular_compact_selected]

/-- The elementary selection identity for arbitrary strip-supported
functions. It is not restricted to holomorphic or automorphic vectors. -/
theorem compact_folded_sum_selected (g : GL (Fin 2) ℝ)
    {s : Set ℍ} {ε : ℝ} (t m : ℕ) (D : Data g s ε t)
    (u : ℍ → ℂ) (z : ℍ) :
    (∑ n ∈ D.folds, coefficient g s ε t z *
      AsymptoticHyperbolicSlash.phase (fold g n) (2*m) z *
        AsymptoticMassTransport.strip.indicator u (fold g n • z)) =
      coefficient g s ε t z *
        AsymptoticHyperbolicSlash.phase (fold g (Int.floor (g • z).re)) (2*m) z *
        u (fold g (Int.floor (g • z).re) • z) := by
  classical
  by_cases hz : z∈s
  · rw [Finset.sum_eq_single (Int.floor (g • z).re)]
    · rw [Set.indicator_of_mem ((fold_mem_strip_iff _ _ _).mpr rfl)]
    · intro n _ hn
      rw [Set.indicator_of_notMem ((fold_mem_strip_iff _ _ _).not.mpr hn),mul_zero]
    · exact fun hn => False.elim (hn (D.fold_mem z hz))
  · simp [coefficient,hz]

/-- Replacing qualitative compact data by an explicitly bounded finite
fold set leaves the full physical strip-restricted operator unchanged. -/
theorem physical_compact_data_independent (g : GL (Fin 2) ℝ)
    {s : Set ℍ} (hs : MeasurableSet s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D E : Data g s ε t) (m : ℕ) :
    (AsymptoticCompactBranch.operator g hs hε t D m).comp
      (AsymptoticRegionL2.projection volume AsymptoticMassTransport.strip
        AsymptoticMassTransport.strip_measurable) =
    (AsymptoticCompactBranch.operator g hs hε t E m).comp
      (AsymptoticRegionL2.projection volume AsymptoticMassTransport.strip
        AsymptoticMassTransport.strip_measurable) := by
  apply ContinuousLinearMap.ext
  intro u
  let v := AsymptoticRegionL2.projection volume AsymptoticMassTransport.strip
    AsymptoticMassTransport.strip_measurable u
  have hv : ∀ᵐ z ∂volume, ∀ n : ℤ,
      v (fold g n • z)=AsymptoticMassTransport.strip.indicator u (fold g n • z) := by
    apply ae_all_iff.mpr
    intro n
    exact (measurePreserving_smul (fold g n)
      (volume : Measure ℍ)).quasiMeasurePreserving.ae
      (AsymptoticRegionL2.projection_coeFn volume AsymptoticMassTransport.strip
        AsymptoticMassTransport.strip_measurable u)
  apply Lp.ext
  filter_upwards [operator_coeFn g hs hε t D m v,operator_coeFn g hs hε t E m v,hv] with z hD hE hvz
  change AsymptoticCompactBranch.operator g hs hε t D m v z =
    AsymptoticCompactBranch.operator g hs hε t E m v z
  rw [hD,hE]
  simp_rw [hvz]
  rw [compact_folded_sum_selected,compact_folded_sum_selected]

#print axioms regular_compact_data_independent
#print axioms physical_compact_data_independent

end QuantitativeHolomorphic
