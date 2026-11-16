module

public import QuantitativeMaassNormalizerCompletionV1
public import QuantitativeMaassTargetMetricV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set UpperHalfPlane MeasureTheory
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson

namespace QuantitativeMaass

theorem lower_energy_antilipschitz {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (R : H →L[ℂ] K) {a : ℝ} (ha : 0<a) (hR : ∀ x,a*‖x‖^2≤‖R x‖^2) :
    AntilipschitzWith ⟨(Real.sqrt a)⁻¹,inv_nonneg.mpr (Real.sqrt_nonneg a)⟩ R := by
  apply R.antilipschitz_of_bound
  intro x
  have hs := Real.sqrt_pos.mpr ha
  have hb : Real.sqrt a*‖x‖≤‖R x‖ := by
    apply (sq_le_sq₀ (mul_nonneg hs.le (norm_nonneg _)) (norm_nonneg _)).mp
    rw [mul_pow,Real.sq_sqrt ha.le]
    exact hR x
  change ‖x‖≤(Real.sqrt a)⁻¹*‖R x‖
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hs).mpr
  simpa only [mul_comm] using hb

theorem lower_energy_injective_closed {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (R : H →L[ℂ] K) {a : ℝ} (ha : 0<a) (hR : ∀ x,a*‖x‖^2≤‖R x‖^2) :
    Function.Injective R ∧ IsClosed (Set.range R) := by
  have h := lower_energy_antilipschitz R ha hR
  exact ⟨h.injective,h.isClosed_range R.uniformContinuous⟩

/-- The actual weighted embedding of the completed normalizer eigenspace
has closed range once its finite cusp cover is supplied. -/
theorem normalizerWeightedEmbedding_closed {ι : Type*} [Fintype ι]
    (N : ℕ) {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y) {v : ℕ} (hv : 1≤v)
    (g : ι → AsymptoticRationalGroup.Group) (χ : ι → ℂ) (hχ : ∀ i,‖χ i‖=1)
    (hc : ∀ i,∀ b∈gamma N,g i*b*(g i)⁻¹∈gamma N)
    (hci : ∀ i,∀ b∈gamma N,(g i)⁻¹*b*g i∈gamma N)
    (hcover : ∀ z : ℍ,∃ i,∃ b : gamma N,Y≤(b.val • (g i • z)).im) :
    Function.Injective (normalizerWeightedEmbedding N hε hv g χ) ∧
      IsClosed (Set.range (normalizerWeightedEmbedding N hε hv g χ)) := by
  have ha : 0<heightWeightFloor ε v Y/((Fintype.card ι:ℝ)+1) :=
    div_pos (heightWeightFloor_pos hε hY v) (by positivity)
  apply lower_energy_injective_closed
    (H := normalizerCompletion N g χ) (K := Lp ℂ 2 (quotientMeasure 0))
    (normalizerWeightedEmbedding N hε hv g χ) ha
  intro x
  exact normalizerWeightedEmbedding_lower N hε hY hv g χ hχ hc hci hcover x

/-- A genuine continuous linear equivalence onto the closed weighted range,
with the same pointwise map as the literal cap-weighted embedding. -/
def normalizerWeightedEquiv {ι : Type*} [Fintype ι]
    (N : ℕ) {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y) {v : ℕ} (hv : 1≤v)
    (g : ι → AsymptoticRationalGroup.Group) (χ : ι → ℂ) (hχ : ∀ i,‖χ i‖=1)
    (hc : ∀ i,∀ b∈gamma N,g i*b*(g i)⁻¹∈gamma N)
    (hci : ∀ i,∀ b∈gamma N,(g i)⁻¹*b*g i∈gamma N)
    (hcover : ∀ z : ℍ,∃ i,∃ b : gamma N,Y≤(b.val • (g i • z)).im) :
    normalizerCompletion N g χ ≃L[ℂ] (normalizerWeightedEmbedding N hε hv g χ).range :=
  ContinuousLinearMap.equivRange
    (E := normalizerCompletion N g χ) (F := Lp ℂ 2 (quotientMeasure 0))
    (f := normalizerWeightedEmbedding N hε hv g χ)
    (normalizerWeightedEmbedding_closed N hε hY hv g χ hχ hc hci hcover).1
    (normalizerWeightedEmbedding_closed N hε hY hv g χ hχ hc hci hcover).2

theorem normalizerWeightedEquiv_apply {ι : Type*} [Fintype ι]
    (N : ℕ) {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y) {v : ℕ} (hv : 1≤v)
    (g : ι → AsymptoticRationalGroup.Group) (χ : ι → ℂ) (hχ : ∀ i,‖χ i‖=1)
    (hc : ∀ i,∀ b∈gamma N,g i*b*(g i)⁻¹∈gamma N)
    (hci : ∀ i,∀ b∈gamma N,(g i)⁻¹*b*g i∈gamma N)
    (hcover : ∀ z : ℍ,∃ i,∃ b : gamma N,Y≤(b.val • (g i • z)).im)
    (f : normalizerCompletion N g χ) :
    (normalizerWeightedEquiv N hε hY hv g χ hχ hc hci hcover f : Lp ℂ 2 (quotientMeasure 0))=
      weightedQuotientEmbedding N hε hv f.val := rfl

#print axioms lower_energy_antilipschitz
#print axioms lower_energy_injective_closed
#print axioms normalizerWeightedEmbedding_closed
#print axioms normalizerWeightedEquiv
#print axioms normalizerWeightedEquiv_apply

end QuantitativeMaass
