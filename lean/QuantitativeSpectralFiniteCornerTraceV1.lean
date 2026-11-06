module

public import QuantitativeSpectralRegularAlgebraV1
public import QuantitativeSpectralTraceFunctionalV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
@[expose] public section

open MeasureTheory
open scoped lp ENNReal

namespace QuantitativeSpectralFiniteCornerTrace

open AsymptoticRegularTrace QuantitativeSpectralRegularAlgebra

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α] [MeasurableSpace α] [MulAction G α]
  (μ : Measure α) (hact : ∀ g : G, Measurable (fun x : α => g • x))
  (s : Set α) (hs : MeasurableSet s) (hf : μ s < ∞)

/-- The bounded rooted trace on the actual regular finite-corner C*-algebra. -/
noncomputable def rootedTrace : FiniteCorner G α hact s hs →L[ℝ] ℝ :=
  QuantitativeSpectralTraceFunctional.traceCLM μ hs hf
    (representation G α hact s hs)
    (fun a => representation_matrix_measurable G α hact s hs a 1 1)
    (representation_norm_le G α hact s hs)
    (representation_supported G α hact s hs)

@[simp] theorem rootedTrace_apply (a : FiniteCorner G α hact s hs) :
    rootedTrace μ hact s hs hf a = signedTrace μ (representation G α hact s hs a) := rfl

theorem rootedTrace_cyclic
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (a b : FiniteCorner G α hact s hs) :
    rootedTrace μ hact s hs hf (a*b) = rootedTrace μ hact s hs hf (b*a) :=
  QuantitativeSpectralTraceFunctional.traceCLM_cyclic μ hs hf
    (representation G α hact s hs)
    (fun a => representation_matrix_measurable G α hact s hs a 1 1)
    (representation_norm_le G α hact s hs)
    (representation_supported G α hact s hs) hmp
    (representation_matrix_measurable G α hact s hs)
    (representation_covariant G α hact s hs)
    (representation_mul G α hact s hs) a b

theorem rootedTrace_star (a : FiniteCorner G α hact s hs) :
    rootedTrace μ hact s hs hf (star a) = rootedTrace μ hact s hs hf a :=
  QuantitativeSpectralTraceFunctional.traceCLM_star μ hs hf
    (representation G α hact s hs)
    (fun a => representation_matrix_measurable G α hact s hs a 1 1)
    (representation_norm_le G α hact s hs)
    (representation_supported G α hact s hs)
    (representation_star G α hact s hs) a

/-- The triangular trace-log identity now holds in the concrete regular
corner: no abstract tracial-functional or representation hypotheses remain. -/
theorem trace_log_block_congruence
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    {n : ℕ} (Q : Fin n → FiniteCorner G α hact s hs) (hQ : ∑ i, Q i = 1)
    (hid : ∀ i, Q i*Q i = Q i) {V : FiniteCorner G α hact s hs}
    (hV : QuantitativeSpectralBlockTriangular.Below Q V 1)
    (B : FiniteCorner G α hact s hs) (hB : IsUnit B) (t : ℝ) :
    rootedTrace μ hact s hs hf (CFC.log (star (B*(1+t • V))*(B*(1+t • V)))) =
      rootedTrace μ hact s hs hf (CFC.log (star B*B)) :=
  QuantitativeSpectralBlockTriangular.trace_log_block_congruence Q hQ hid hV B hB
    (rootedTrace μ hact s hs hf) (rootedTrace_cyclic μ hact s hs hf hmp)
    (rootedTrace_star μ hact s hs hf) t

#print axioms rootedTrace
#print axioms rootedTrace_cyclic
#print axioms trace_log_block_congruence

end QuantitativeSpectralFiniteCornerTrace
