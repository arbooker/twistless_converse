module

public import QuantitativeMaassNormalizerMetricLowerV1
public import Mathlib.Analysis.Normed.Operator.Banach

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCompactBranch
open scoped ENNReal

namespace QuantitativeMaass

/-- Pointwise normalizer eigenspaces, before taking the quotient completion. -/
def normalizerRepresentatives {ι : Type*} (N : ℕ)
    (g : ι → AsymptoticRationalGroup.Group) (χ : ι → ℂ) :
    Submodule ℂ (AutomorphicL2.representatives (gamma N) (quotientMeasure N)) where
  carrier := {f | ∀ i z,f.val (g i • z)=χ i*f.val z}
  zero_mem' := by simp
  add_mem' := by
    intro f h hf hh i z
    change f.val (g i • z)+h.val (g i • z)=χ i*(f.val z+h.val z)
    rw [hf,hh,mul_add]
  smul_mem' := by
    intro c f hf i z
    change c*f.val (g i • z)=χ i*(c*f.val z)
    rw [hf]
    ring

def normalizerCompletion {ι : Type*} (N : ℕ)
    (g : ι → AsymptoticRationalGroup.Group) (χ : ι → ℂ) : Submodule ℂ (AutomorphicSpace N) :=
  ((normalizerRepresentatives N g χ).map
    (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))).topologicalClosure

instance normalizerCompletion_complete {ι : Type*} (N : ℕ)
    (g : ι → AsymptoticRationalGroup.Group) (χ : ι → ℂ) :
    CompleteSpace (normalizerCompletion N g χ) :=
  ((normalizerRepresentatives N g χ).map
    (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))).isClosed_topologicalClosure.completeSpace_coe

theorem normalizerRepresentative_energy_lower {ι : Type*} [Fintype ι]
    (N : ℕ) {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y) {v : ℕ} (hv : 1≤v)
    (g : ι → AsymptoticRationalGroup.Group) (χ : ι → ℂ) (hχ : ∀ i,‖χ i‖=1)
    (hc : ∀ i,∀ a∈gamma N,g i*a*(g i)⁻¹∈gamma N)
    (hci : ∀ i,∀ a∈gamma N,(g i)⁻¹*a*g i∈gamma N)
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • (g i • z)).im)
    (f : normalizerRepresentatives N g χ) :
    heightWeightFloor ε v Y*
        ‖AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f.val‖^2≤
      (Fintype.card ι:ℝ)*‖weightedQuotientRepresentative N hε hv f.val‖^2 := by
  have hm := weightedRepresentative_memLp N hε hv f.val
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have ht : (∫⁻ z,ENNReal.ofReal (‖(cap ε v z:ℂ)*f.val.val z‖^2)
      ∂quotientMeasure 0)≠∞ :=
    ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mp hi.2).ne
  have hb := weighted_quotient_energy_lower_of_normalizers N hε hY hv g hc hci hcover
    f.val.val f.val.property.1 f.val.property.2.1 (by
      intro i z
      rw [f.property i z,norm_mul,hχ,one_mul])
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ht) hb
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (heightWeightFloor_pos hε hY v).le,
    square_energy_toReal _ f.val.property.2.2,square_energy_toReal _ hm] at hr
  simp only [ENNReal.toReal_natCast] at hr
  change heightWeightFloor ε v Y*
    ‖AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f.val‖^2≤
    (Fintype.card ι:ℝ)*‖weightedQuotientRepresentative N hε hv f.val‖^2 at hr
  exact hr

/-- The lower estimate survives completion by closedness of the norm inequality. -/
theorem normalizerCompletion_energy_lower {ι : Type*} [Fintype ι]
    (N : ℕ) {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y) {v : ℕ} (hv : 1≤v)
    (g : ι → AsymptoticRationalGroup.Group) (χ : ι → ℂ) (hχ : ∀ i,‖χ i‖=1)
    (hc : ∀ i,∀ a∈gamma N,g i*a*(g i)⁻¹∈gamma N)
    (hci : ∀ i,∀ a∈gamma N,(g i)⁻¹*a*g i∈gamma N)
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • (g i • z)).im)
    (f : normalizerCompletion N g χ) :
    heightWeightFloor ε v Y*‖f‖^2≤
      (Fintype.card ι:ℝ)*‖weightedQuotientEmbedding N hε hv f.val‖^2 := by
  have hclosed : IsClosed {x : AutomorphicSpace N | heightWeightFloor ε v Y*‖x‖^2≤
      (Fintype.card ι:ℝ)*‖weightedQuotientEmbedding N hε hv x‖^2} :=
    isClosed_le (continuous_const.mul (continuous_norm.pow 2))
      (continuous_const.mul ((weightedQuotientEmbedding N hε hv).continuous.norm.pow 2))
  apply closure_minimal (t := {x : AutomorphicSpace N | heightWeightFloor ε v Y*‖x‖^2≤
      (Fintype.card ι:ℝ)*‖weightedQuotientEmbedding N hε hv x‖^2}) _ hclosed f.property
  rintro x ⟨r,hr,rfl⟩
  rw [mem_ofPred_eq,weightedQuotientEmbedding_representative]
  exact normalizerRepresentative_energy_lower N hε hY hv g χ hχ hc hci hcover ⟨r,hr⟩

def normalizerWeightedEmbedding {ι : Type*} (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (g : ι → AsymptoticRationalGroup.Group) (χ : ι → ℂ) :
    normalizerCompletion N g χ →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  (weightedQuotientEmbedding N hε hv).comp (normalizerCompletion N g χ).subtypeL

theorem normalizerWeightedEmbedding_lower {ι : Type*} [Fintype ι]
    (N : ℕ) {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y) {v : ℕ} (hv : 1≤v)
    (g : ι → AsymptoticRationalGroup.Group) (χ : ι → ℂ) (hχ : ∀ i,‖χ i‖=1)
    (hc : ∀ i,∀ a∈gamma N,g i*a*(g i)⁻¹∈gamma N)
    (hci : ∀ i,∀ a∈gamma N,(g i)⁻¹*a*g i∈gamma N)
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • (g i • z)).im)
    (f : normalizerCompletion N g χ) :
    (heightWeightFloor ε v Y/((Fintype.card ι:ℝ)+1))*‖f‖^2≤
      ‖normalizerWeightedEmbedding N hε hv g χ f‖^2 := by
  have h := normalizerCompletion_energy_lower N hε hY hv g χ hχ hc hci hcover f
  change heightWeightFloor ε v Y*‖f‖^2≤
    (Fintype.card ι:ℝ)*‖normalizerWeightedEmbedding N hε hv g χ f‖^2 at h
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0<(Fintype.card ι:ℝ)+1)).mpr
  nlinarith [sq_nonneg ‖normalizerWeightedEmbedding N hε hv g χ f‖]

#print axioms normalizerRepresentative_energy_lower
#print axioms normalizerCompletion_energy_lower
#print axioms normalizerWeightedEmbedding_lower

end QuantitativeMaass
