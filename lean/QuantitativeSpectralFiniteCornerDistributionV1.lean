module

public import QuantitativeSpectralFiniteCornerTraceV1
public import QuantitativeTracialSpectralMeasureV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
@[expose] public section

open MeasureTheory
open scoped lp ENNReal

namespace QuantitativeSpectralFiniteCornerDistribution

open AsymptoticRegularTrace AsymptoticOrbitDiagonal
open QuantitativeSpectralRegularAlgebra QuantitativeSpectralFiniteCornerTrace

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
  (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)

/-- The canonical C*-order on the concrete corner. -/
noncomputable instance cornerOrder : PartialOrder (FiniteCorner G α hact s hs) :=
  CStarAlgebra.spectralOrder _

instance cornerStarOrdered : StarOrderedRing (FiniteCorner G α hact s hs) :=
  CStarAlgebra.spectralOrderedRing _

variable (μ : Measure α) (hf : μ s < ∞)

theorem rootedTrace_one : rootedTrace μ hact s hs hf 1 = (μ s).toReal := by
  change signedTrace μ (corner (G:=G) s) = (μ s).toReal
  rw [signedTrace_eq_toReal μ _ (corner_matrix_measurable hact hs 1 1) (corner_positive s),
    trace_corner μ hs]

/-- Positivity of the concrete rooted trace is derived from the actual
regular Gram matrices, rather than supplied as a trace axiom. -/
theorem rootedTrace_mono : Monotone (rootedTrace μ hact s hs hf) := by
  intro a b hab
  exact QuantitativeSpectralTraceFunctional.traceCLM_mono μ hs hf
    (representation G α hact s hs)
    (fun a => representation_matrix_measurable G α hact s hs a 1 1)
    (representation_norm_le G α hact s hs)
    (representation_supported G α hact s hs)
    (representation_mul G α hact s hs)
    (representation_star G α hact s hs) hab

/-- Collective triangular domination gives a lower bound for the actual
regular trace-log in the geometric corner. -/
theorem log_lower_bound
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    {n : ℕ} (Q : Fin n → FiniteCorner G α hact s hs) (hQ : ∑ i, Q i = 1)
    (hid : ∀ i, Q i*Q i = Q i) {V : FiniteCorner G α hact s hs}
    (hV : QuantitativeSpectralBlockTriangular.Below Q V 1)
    (B : FiniteCorner G α hact s hs) (hB : IsUnit B) (S : FiniteCorner G α hact s hs)
    (hdom : star (B*(1+V))*(B*(1+V)) ≤ S) :
    rootedTrace μ hact s hs hf (CFC.log (star B*B)) ≤ rootedTrace μ hact s hs hf (CFC.log S) := by
  have hu : IsUnit (B*(1+V)) := hB.mul
    ((show IsNilpotent V from ⟨n+1, QuantitativeSpectralBlockTriangular.pow_eq_zero Q hQ hV⟩).isUnit_one_add)
  have hp : IsStrictlyPositive (star (B*(1+V))*(B*(1+V))) :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mpr ⟨B*(1+V),hu,rfl⟩
  have ht := rootedTrace_mono hact s hs μ hf (CFC.log_le_log hdom hp)
  have he := trace_log_block_congruence μ hact s hs hf hmp Q hQ hid hV B hB 1
  simp only [one_smul] at he
  rwa [he] at ht

/-- The actual finite regular spectral measure obeys the determinant
small-spectrum estimate, with total mass equal to the geometric area. -/
theorem small_mass_of_log_lower_bound
    (A : FiniteCorner G α hact s hs) (hA : IsSelfAdjoint A) (hpos : IsStrictlyPositive A)
    {sigma K lam : ℝ} (hsigma : 0 < sigma) (hK : 0 < K)
    (hlam : 0 < lam) (hlamK : lam < K) (hnorm : ‖A‖ ≤ K)
    (hlower : (μ s).toReal * Real.log sigma ≤ rootedTrace μ hact s hs hf (CFC.log A)) :
    (QuantitativeTracialSpectralMeasure.measure (rootedTrace μ hact s hs hf)
      (rootedTrace_mono hact s hs μ hf) A hA).real
      {x : spectrum ℝ A | (x : ℝ) ≤ lam} ≤
        (μ s).toReal * Real.log (K/sigma) / Real.log (K/lam) := by
  have hh := QuantitativeTracialSpectralMeasure.small_mass_of_trace_log_norm
    (rootedTrace μ hact s hs hf) (rootedTrace_mono hact s hs μ hf) A hA hpos
    hsigma hK hlam hlamK hnorm (by rwa [rootedTrace_one hact s hs μ hf])
  rwa [rootedTrace_one hact s hs μ hf] at hh

#print axioms rootedTrace_one
#print axioms rootedTrace_mono
#print axioms log_lower_bound
#print axioms small_mass_of_log_lower_bound

end QuantitativeSpectralFiniteCornerDistribution
