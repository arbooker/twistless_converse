module

public import AsymptoticOrbitDiagonalV1
public import AsymptoticCompactBranchV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalUnweight

open MeasureTheory UpperHalfPlane AsymptoticCompactBranch AsymptoticOrbitDiagonal
open AsymptoticRegularTrace
open scoped lp

abbrev G := AsymptoticRationalGroup.Group
abbrev Space := ℓ²(G,ℂ)

/-- A bound for actual reciprocal cap on a specified output region. -/
structure Data (s : Set ℍ) (ε : ℝ) (t : ℕ) where
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  inverse_le : ∀ z ∈ s, (cap ε t z)⁻¹ ≤ bound

theorem data_exists {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) (t : ℕ) :
    Nonempty (Data s ε t) := by
  have hc : Continuous (fun z : ℍ => (cap ε t z)⁻¹) :=
    (cap_continuous ε t).inv₀ (fun z => (cap_pos hε t z).ne')
  obtain ⟨C, hC⟩ := hs.bddAbove_image hc.continuousOn
  exact ⟨⟨max C 0, le_max_right _ _, fun z hz =>
    (hC (Set.mem_image_of_mem _ hz)).trans (le_max_left _ _)⟩⟩

def data {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) (t : ℕ) : Data s ε t :=
  Classical.choice (data_exists hs hε t)

def coefficient (s : Set ℍ) (ε : ℝ) (t : ℕ) : ℍ → ℂ :=
  s.indicator (fun z => Complex.ofReal ((cap ε t z)⁻¹))

theorem coefficient_bound {s : Set ℍ} {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (D : Data s ε t) (z : ℍ) : ‖coefficient s ε t z‖ ≤ D.bound := by
  classical
  by_cases hz : z ∈ s
  · rw [coefficient, Set.indicator_of_mem hz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (cap_pos hε t z))]
    exact D.inverse_le z hz
  · rw [coefficient, Set.indicator_of_notMem hz, norm_zero]
    exact D.bound_nonneg

def unweight {s : Set ℍ} {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (D : Data s ε t) (x : ℍ) : Space →L[ℂ] Space :=
  AsymptoticOrbitDiagonal.operator (fun g => coefficient s ε t (g • x))
    D.bound_nonneg (fun g => coefficient_bound hε t D (g • x))

theorem unweight_apply {s : Set ℍ} {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (D : Data s ε t) (x : ℍ) (v : Space) (g : G) :
    unweight hε t D x v g = coefficient s ε t (g • x) * v g := rfl

theorem unweight_norm {s : Set ℍ} {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (D : Data s ε t) (x : ℍ) : ‖unweight hε t D x‖ ≤ D.bound :=
  operator_norm_le _ _ _

theorem unweight_regular {s : Set ℍ} (hs : MeasurableSet s) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (D : Data s ε t) :
    (∀ g h : G, Measurable (fun x => matrix (unweight hε t D x) g h)) ∧
      Covariant (unweight hε t D) := by
  have hc : Measurable (coefficient s ε t) :=
    (Complex.continuous_ofReal.comp ((cap_continuous ε t).inv₀
      (fun z => (cap_pos hε t z).ne'))).measurable.indicator hs
  constructor
  · intro g h
    simp only [unweight, operator_matrix]
    by_cases he : g = h
    · simp only [he, ite_true]
      exact hc.comp (AsymptoticRationalGroup.measurePreserving h).measurable
    · simp only [he, ite_false]
      exact measurable_const
  · intro x a g h
    simp only [unweight, operator_matrix, mul_smul]
    have he : g*a = h*a ↔ g=h := mul_right_cancel_iff
    rw [he]

#print axioms data_exists
#print axioms unweight_norm
#print axioms unweight_regular

end QuantitativeSpectralExceptionalUnweight
