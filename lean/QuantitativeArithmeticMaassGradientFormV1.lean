module

public import QuantitativeArithmeticMaassGradientExtensionV1
public import QuantitativeMaassFormLocalizationDefectV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeArithmeticMaassGradient

open QuantitativeMaass MaassDifferential

theorem raw_pair_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun z => star (f z)*g z) μ := by
  apply (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with z hz₁ hz₂
  rw [hz₁,hz₂,RCLike.inner_apply']
  rfl

theorem inner_toLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : α → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℂ (hf.toLp f) (hg.toLp g)=∫ z, star (f z)*g z ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with z hz₁ hz₂
  rw [hz₁,hz₂,RCLike.inner_apply']
  rfl

theorem seed_gradient_energy (N : ℕ) (u v : SmoothUpperSeed) (z : ℍ) :
    star (seedGradient N true u z)*seedGradient N true v z+
      star (seedGradient N false u z)*seedGradient N false v z=
      upperEnergy (congruencePoincareCartesian N u.toFun)
        (congruencePoincareCartesian N v.toFun) z := by
  unfold seedGradient axis upperEnergy upperFunction hyperbolicEnergy X Y
  simp only [ite_true,Bool.false_eq_true,ite_false,star_mul,Complex.star_def,
    Complex.conj_ofReal]
  ring

theorem poincare_gradient_form (N : ℕ) (u v : SmoothUpperSeed) :
    quotientClosedEnergy N (poincareEnergySeed N u) (poincareEnergySeed N v)=
      inner ℂ (seedGradientLp N true u) (seedGradientLp N true v)+
      inner ℂ (seedGradientLp N false u) (seedGradientLp N false v) := by
  rw [poincareClosedEnergy_integral]
  simp only [seedGradientLp,inner_toLp]
  rw [← integral_add (raw_pair_integrable (seedGradient_memLp N true u) (seedGradient_memLp N true v))
    (raw_pair_integrable (seedGradient_memLp N false u) (seedGradient_memLp N false v))]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun z => (seed_gradient_energy N u v z).symm))

/-- The completed Dirichlet form is exactly the sum of the two literal
hyperbolic gradient pairings. No regularity assumption on completed vectors. -/
theorem quotientGradient_form (N : ℕ) (u v : QuotientEnergySpace N) :
    quotientClosedEnergy N u v=
      inner ℂ (quotientGradient N true u) (quotientGradient N true v)+
      inner ℂ (quotientGradient N false u) (quotientGradient N false v) := by
  have hd := (poincareEnergySeed_completion_dense N).prodMap (poincareEnergySeed_completion_dense N)
  have hl : Continuous (fun p : QuotientEnergySpace N × QuotientEnergySpace N =>
      quotientClosedEnergy N p.1 p.2) := by unfold quotientClosedEnergy; fun_prop
  have hr : Continuous (fun p : QuotientEnergySpace N × QuotientEnergySpace N =>
      inner ℂ (quotientGradient N true p.1) (quotientGradient N true p.2)+
      inner ℂ (quotientGradient N false p.1) (quotientGradient N false p.2)) := by fun_prop
  apply congrFun (hd.equalizer hl hr ?_) (u,v)
  funext p
  change quotientClosedEnergy N (poincareEnergySeed N p.1) (poincareEnergySeed N p.2)=
    inner ℂ (quotientGradient N true (poincareEnergySeed N p.1))
      (quotientGradient N true (poincareEnergySeed N p.2))+
    inner ℂ (quotientGradient N false (poincareEnergySeed N p.1))
      (quotientGradient N false (poincareEnergySeed N p.2))
  simp only [quotientGradient_seed]
  exact poincare_gradient_form N p.1 p.2

theorem quotientGradient_norm_sq (N : ℕ) (u : QuotientEnergySpace N) :
    (quotientClosedEnergy N u u).re=
      ‖quotientGradient N true u‖^2+‖quotientGradient N false u‖^2 := by
  rw [quotientGradient_form,Complex.add_re]
  exact congrArg₂ (·+·) (inner_self_eq_norm_sq (𝕜 := ℂ) _) (inner_self_eq_norm_sq (𝕜 := ℂ) _)

#print axioms quotientGradient_form
#print axioms quotientGradient_norm_sq

end QuantitativeArithmeticMaassGradient
