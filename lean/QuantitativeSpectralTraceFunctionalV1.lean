module

public import QuantitativeSpectralBlockTriangularV1
public import AsymptoticSignedCornerV1
public import AsymptoticProjectionTraceV1
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

set_option autoImplicit false
@[expose] public section

open MeasureTheory ContinuousLinearMap
open scoped lp ENNReal

namespace QuantitativeSpectralTraceFunctional

open AsymptoticRegularTrace AsymptoticOrbitDiagonal

variable {G α 𝔄 : Type*} [Group G] [MeasurableSpace α] [MulAction G α] [CStarAlgebra 𝔄]

variable (μ : Measure α) {s : Set α} (hs : MeasurableSet s) (hf : μ s < ∞)
  (ρ : 𝔄 →ₗ[ℝ] (α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)))
  (hm : ∀ a, Measurable (fun x => matrix (ρ a x) 1 1))
  (hn : ∀ a x, ‖ρ a x‖ ≤ ‖a‖)
  (hc : ∀ a x, (ρ a x).comp (corner s x) = ρ a x)

/-- The actual rooted integral is a linear functional on a uniformly
contractive representation supported in a finite geometric corner. -/
noncomputable def traceLinear : 𝔄 →ₗ[ℝ] ℝ where
  toFun a := signedTrace μ (ρ a)
  map_add' a b := by
    have ha := corner_diagonal_integrable μ hs hf (ρ a) (hm a) (hn a) (hc a)
    have hb := corner_diagonal_integrable μ hs hf (ρ b) (hm b) (hn b) (hc b)
    simpa [signedTrace, matrix] using integral_add ha hb
  map_smul' c a := by
    simp [signedTrace, matrix, integral_const_mul]

/-- The finite geometric corner supplies the norm bound, so the actual
rooted integral is a continuous linear functional suitable for CFC integrals. -/
noncomputable def traceCLM : 𝔄 →L[ℝ] ℝ :=
  (traceLinear μ hs hf ρ hm hn hc).mkContinuous (μ s).toReal (fun a => by
    exact (norm_signedTrace_le_corner μ hs hf (ρ a) (hn a) (hc a)).trans_eq (mul_comm _ _))

@[simp] theorem traceCLM_apply (a : 𝔄) :
    traceCLM μ hs hf ρ hm hn hc a = signedTrace μ (ρ a) := rfl

include hs hf hn hc in
/-- Finite energy of every represented element follows from geometric
corner support and the operator norm bound. -/
theorem representation_energy_finite (a : 𝔄) :
    trace μ (fun x => (ρ a x).adjoint.comp (ρ a x)) < ∞ := by
  apply (trace_le_corner μ hs (fun x => (ρ a x).adjoint.comp (ρ a x))
    (C := ‖a‖^2) ?_ ?_).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)
  · intro x
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact (mul_le_mul (hn a x) (hn a x) (norm_nonneg _) (norm_nonneg _)).trans_eq (pow_two _).symm
  · intro x
    rw [ContinuousLinearMap.comp_assoc, hc a x]

variable [Countable G]

/-- Covariance and measure preservation prove cyclicity of the actual
bounded rooted trace; cyclicity is not postulated for the trace functional. -/
theorem traceCLM_cyclic
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (hmm : ∀ a g h, Measurable (fun x => matrix (ρ a x) g h))
    (hcov : ∀ a, Covariant (ρ a))
    (hmul : ∀ a b x, ρ (a*b) x = (ρ a x).comp (ρ b x)) (a b : 𝔄) :
    traceCLM μ hs hf ρ hm hn hc (a*b) = traceCLM μ hs hf ρ hm hn hc (b*a) := by
  simp only [traceCLM_apply]
  have he := signedTrace_comp_comm μ hmp (ρ a) (ρ b) (hmm a) (hmm b) (hcov a) (hcov b)
    (representation_energy_finite μ hs hf ρ hn hc a)
    (representation_energy_finite μ hs hf ρ hn hc b)
  simpa only [← hmul] using he

omit [Countable G] in
/-- Compatibility with the adjoint is inherited from the actual rooted
real trace. -/
theorem traceCLM_star (hstar : ∀ a x, ρ (star a) x = (ρ a x).adjoint) (a : 𝔄) :
    traceCLM μ hs hf ρ hm hn hc (star a) = traceCLM μ hs hf ρ hm hn hc a := by
  simp only [traceCLM_apply]
  simpa only [← hstar] using signedTrace_adjoint μ (ρ a)

include hs hf hm hn hc in
/-- The abstract block identity applies to the actual rooted finite-corner
trace, with cyclicity discharged by covariance and measure preservation. -/
theorem rooted_trace_log_block_congruence
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (hmm : ∀ a g h, Measurable (fun x => matrix (ρ a x) g h))
    (hcov : ∀ a, Covariant (ρ a))
    (hmul : ∀ a b x, ρ (a*b) x = (ρ a x).comp (ρ b x))
    (hstar : ∀ a x, ρ (star a) x = (ρ a x).adjoint)
    {n : ℕ} (Q : Fin n → 𝔄) (hQ : ∑ i, Q i = 1)
    (hid : ∀ i, Q i*Q i = Q i) {V : 𝔄}
    (hV : QuantitativeSpectralBlockTriangular.Below Q V 1)
    (B : 𝔄) (hB : IsUnit B) (t : ℝ) :
    signedTrace μ (ρ (CFC.log (star (B*(1+t • V))*(B*(1+t • V))))) =
      signedTrace μ (ρ (CFC.log (star B*B))) :=
  QuantitativeSpectralBlockTriangular.trace_log_block_congruence Q hQ hid hV B hB
    (traceCLM μ hs hf ρ hm hn hc)
    (traceCLM_cyclic μ hs hf ρ hm hn hc hmp hmm hcov hmul)
    (traceCLM_star μ hs hf ρ hm hn hc hstar) t

section Ordered

variable [PartialOrder 𝔄] [StarOrderedRing 𝔄]

omit [Countable G] in
/-- Positivity of the actual rooted functional follows from its Gram
formula and the representation's multiplication/adjoint identities. -/
theorem traceCLM_nonneg
    (hmul : ∀ a b x, ρ (a*b) x = (ρ a x).comp (ρ b x))
    (hstar : ∀ a x, ρ (star a) x = (ρ a x).adjoint)
    {a : 𝔄} (ha : 0 ≤ a) : 0 ≤ traceCLM μ hs hf ρ hm hn hc a := by
  obtain ⟨b,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  change 0 ≤ ∫ x, (matrix (ρ (star b*b) x) 1 1).re ∂μ
  apply integral_nonneg
  intro x
  change 0 ≤ (matrix (ρ (star b*b) x) 1 1).re
  rw [hmul, hstar, matrix_gram]
  positivity

omit [Countable G] in
/-- Order preservation of the rooted bounded trace is proved from positivity. -/
theorem traceCLM_mono
    (hmul : ∀ a b x, ρ (a*b) x = (ρ a x).comp (ρ b x))
    (hstar : ∀ a x, ρ (star a) x = (ρ a x).adjoint)
    {a b : 𝔄} (hab : a ≤ b) :
    traceCLM μ hs hf ρ hm hn hc a ≤ traceCLM μ hs hf ρ hm hn hc b := by
  have hh := traceCLM_nonneg μ hs hf ρ hm hn hc hmul hstar (sub_nonneg.mpr hab)
  rw [map_sub] at hh
  exact sub_nonneg.mp hh

include hs hf hm hn hc in
/-- Collective domination by a triangular Gram operator transfers the
actual rooted trace-log lower bound to the fixed diagonal factor. -/
theorem rooted_log_lower_bound
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (hmm : ∀ a g h, Measurable (fun x => matrix (ρ a x) g h))
    (hcov : ∀ a, Covariant (ρ a))
    (hmul : ∀ a b x, ρ (a*b) x = (ρ a x).comp (ρ b x))
    (hstar : ∀ a x, ρ (star a) x = (ρ a x).adjoint)
    {n : ℕ} (Q : Fin n → 𝔄) (hQ : ∑ i, Q i = 1)
    (hid : ∀ i, Q i*Q i = Q i) {V : 𝔄}
    (hV : QuantitativeSpectralBlockTriangular.Below Q V 1)
    (B : 𝔄) (hB : IsUnit B) (S : 𝔄)
    (hdom : star (B*(1+V))*(B*(1+V)) ≤ S) :
    signedTrace μ (ρ (CFC.log (star B*B))) ≤ signedTrace μ (ρ (CFC.log S)) := by
  have hu : IsUnit (B*(1+V)) := hB.mul
    ((show IsNilpotent V from ⟨n+1, QuantitativeSpectralBlockTriangular.pow_eq_zero Q hQ hV⟩).isUnit_one_add)
  have hp : IsStrictlyPositive (star (B*(1+V))*(B*(1+V))) :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mpr ⟨B*(1+V),hu,rfl⟩
  have hlog := CFC.log_le_log hdom hp
  have ht := traceCLM_mono μ hs hf ρ hm hn hc hmul hstar hlog
  change signedTrace μ (ρ (CFC.log (star (B*(1+V))*(B*(1+V))))) ≤ _ at ht
  have he := rooted_trace_log_block_congruence μ hs hf ρ hm hn hc
    hmp hmm hcov hmul hstar Q hQ hid hV B hB 1
  simp only [one_smul] at he
  rwa [he] at ht

end Ordered

#print axioms traceLinear
#print axioms rooted_trace_log_block_congruence
#print axioms traceCLM_nonneg
#print axioms traceCLM_mono
#print axioms rooted_log_lower_bound
#print axioms traceCLM
#print axioms representation_energy_finite
#print axioms traceCLM_cyclic
#print axioms traceCLM_star

end QuantitativeSpectralTraceFunctional
