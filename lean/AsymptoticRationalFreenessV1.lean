module

public import AsymptoticHyperbolicSlashV1
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Data.Rat.Encodable

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRationalFreeness

open MeasureTheory UpperHalfPlane Filter Set

theorem volume_singleton (z : ℍ) : (volume : Measure ℍ) {z}=0 := by
  rw [UpperHalfPlane.volume_eq_lintegral,Set.image_singleton]
  simp

/-- A positive-determinant nonscalar Möbius transformation has at most
one fixed point in the upper half-plane, hence a hyperbolic null fixed set. -/
theorem fixedPoints_null (g : GL (Fin 2) ℝ) (hg : 0<g.det.val)
    (hn : g∉Subgroup.center (GL (Fin 2) ℝ)) :
    (volume : Measure ℍ) {z | g • z=z}=0 := by
  by_cases hx : ∃ z : ℍ, g • z=z
  · have he := isElliptic_of_exists_smul_eq_self hg hn hx
    have hs : {z : ℍ | g • z=z}={fixedPt g he} := by
      ext z
      exact gl_smul_eq_self_iff_eq_fixedPt hg he
    rw [hs,volume_singleton]
  · have hs : {z : ℍ | g • z=z}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hx ⟨z,hz⟩
    rw [hs,measure_empty]

/-- One null exceptional set works simultaneously for every element of
a countable family. This is the freeness input in rooted branch traces. -/
theorem ae_returns_are_scalar {ι : Type*} [Countable ι] (g : ι → GL (Fin 2) ℝ) :
    ∀ᵐ z : ℍ ∂volume, ∀ i, 0<(g i).det.val → g i • z=z →
      g i∈Subgroup.center (GL (Fin 2) ℝ) := by
  apply ae_all_iff.mpr
  intro i
  by_cases hp : 0<(g i).det.val
  · by_cases hc : g i∈Subgroup.center (GL (Fin 2) ℝ)
    · exact Filter.Eventually.of_forall (fun _ _ _ => hc)
    · have hf : ∀ᵐ z : ℍ ∂volume, g i • z≠z := by
        rw [ae_iff]
        simpa only [not_not] using fixedPoints_null (g i) hp hc
      filter_upwards [hf] with z hz _ hfix
      exact (hz hfix).elim
  · exact Filter.Eventually.of_forall (fun _ h _ => (hp h).elim)

noncomputable def realMatrix (g : GL (Fin 2) ℚ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g

instance rationalGL_countable : Countable (GL (Fin 2) ℚ) := by
  let _ : Countable (Matrix (Fin 2) (Fin 2) ℚ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  exact Function.Injective.countable (f:=fun g : GL (Fin 2) ℚ => g.val) Units.val_injective

theorem ae_rational_returns_are_scalar :
    ∀ᵐ z : ℍ ∂volume, ∀ g : GL (Fin 2) ℚ, 0<(realMatrix g).det.val →
      realMatrix g • z=z → realMatrix g∈Subgroup.center (GL (Fin 2) ℝ) :=
  ae_returns_are_scalar realMatrix

/-- On the same conull set, every returning rational branch word has
unit even-weight slash phase. There is no square-summability assumption
on the values of a holomorphic function along a rational orbit. -/
theorem ae_rational_return_phase :
    ∀ᵐ z : ℍ ∂volume, ∀ g : GL (Fin 2) ℚ, 0<(realMatrix g).det.val →
      realMatrix g • z=z → ∀ m : ℕ, AsymptoticHyperbolicSlash.phase (realMatrix g) (2*m) z=1 := by
  filter_upwards [ae_rational_returns_are_scalar] with z hz g hg hfix m
  have hc := hz g hg hfix
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨u,hu⟩ := hc
  rw [← hu]
  exact AsymptoticHyperbolicSlash.phase_scalar u m z

#print axioms fixedPoints_null
#print axioms ae_rational_returns_are_scalar
#print axioms ae_rational_return_phase

end AsymptoticRationalFreeness
