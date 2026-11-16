module

public import QuantitativeMaassWeightedGreenV1
public import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Weighted

open QuantitativeArithmeticMaassGradient QuantitativeArithmeticMaassWave

theorem normSquared_hasDerivAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {f : ℝ → H} {v : H} {t : ℝ} (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => ‖f s‖^2) (2*(inner ℂ (f t) v).re) t := by
  let := InnerProductSpace.rclikeToReal ℂ H
  simpa only [real_inner_eq_re_inner,RCLike.re_to_complex] using hf.norm_sq

/-- Weighted kinetic, gradient and mass energy. Gradients are multiplied
after differentiation, so no spurious cutoff derivative enters this energy. -/
def energy (N : ℕ) (b : Cutoff N) (u : QuotientEnergySpace N) (v : AutomorphicSpace N) : ℝ :=
  ‖multiplier N b v.val‖^2+
  ‖multiplier N b (quotientGradient N true u)‖^2+
  ‖multiplier N b (quotientGradient N false u)‖^2+
  ‖multiplier N b (ambientInclusion N u)‖^2

def energyRate (N : ℕ) (b : Cutoff N) (u du : QuotientEnergySpace N)
    (v dv : AutomorphicSpace N) : ℝ :=
  2*(inner ℂ (multiplier N b v.val) (multiplier N b dv.val)).re+
  2*(inner ℂ (multiplier N b (quotientGradient N true u))
    (multiplier N b (quotientGradient N true du))).re+
  2*(inner ℂ (multiplier N b (quotientGradient N false u))
    (multiplier N b (quotientGradient N false du))).re+
  2*(inner ℂ (multiplier N b (ambientInclusion N u))
    (multiplier N b (ambientInclusion N du))).re

theorem energy_nonneg (N : ℕ) (b : Cutoff N) (u : QuotientEnergySpace N) (v : AutomorphicSpace N) :
    0≤energy N b u v := by unfold energy; positivity

/-- Ordinary differentiation of the actual weighted energy for an energy-norm
position curve and an L2 velocity curve. -/
theorem energy_hasDerivAt (N : ℕ) (b : Cutoff N)
    {u : ℝ → QuotientEnergySpace N} {v : ℝ → AutomorphicSpace N}
    {du : QuotientEnergySpace N} {dv : AutomorphicSpace N} {t : ℝ}
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t) :
    HasDerivAt (fun s => energy N b (u s) (v s))
      (energyRate N b (u t) du (v t) dv) t := by
  let K := (multiplier N b).comp (AutomorphicSpace N).subtypeL
  let Gx := (multiplier N b).comp (quotientGradient N true)
  let Gy := (multiplier N b).comp (quotientGradient N false)
  let I := (multiplier N b).comp (ambientInclusion N)
  have hk := normSquared_hasDerivAt ((K.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hv)
  have hx := normSquared_hasDerivAt ((Gx.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hu)
  have hy := normSquared_hasDerivAt ((Gy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hu)
  have hi := normSquared_hasDerivAt ((I.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hu)
  exact ((hk.add hx).add hy).add hi

#print axioms energy_hasDerivAt

end QuantitativeMaass.Weighted
