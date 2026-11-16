module

public import QuantitativeArithmeticMaassResidualColumnGraphV1
public import QuantitativeMaassCrossResidualL2V1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap InnerProductSpace

namespace QuantitativeMaass

/-- Integrated leakage of actual cylinder wave columns through a compact
cross-quotient localization. Both energies on the right are the literal
source and residual column energies, not assumed spectral trace bounds. -/
theorem cylinderTimeColumn_integrated_leakage {ι : Type*} [Fintype ι]
    (N : ℕ) (b : SmoothUpperSeed) (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN m0 : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N), (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ mN)
    (hm0 : ∀ z : ℍ, ∀ S : Finset (gamma 0), (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ m0)
    (B C : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (hreal : ∀ Z, star (b.toFun Z) = b.toFun Z)
    (r : ι → ℝ) (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hr : ∀ i, 0 ≤ r i)
    (hgraph : ∀ i, FriedrichsGraph N (v i) ((r i : ℂ) • v i))
    (f : SchwartzMap ℝ ℂ) (hfc : HasCompactSupport (f : ℝ → ℂ))
    (hfe : Function.Even f) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support f ⊆ Icc (-R) R) (t L : ℝ) (hL : 0 < L)
    (hsep : ∀ i, L ≤ |Real.sqrt (1+r i) - Real.sqrt (1+(t^2+1/4))|)
    (o : ℍ) (D : ℝ) :
    let c := fun z => cylinderAutomorphic (cylinderTimeColumn f hfc hfe R hR hs z)
    let d := fun z => cylinderAutomorphic (cylinderTimeColumn (spectralResidualSchwartz t f)
      (spectralResidualSchwartz_compact t f hfc) (spectralResidualSchwartz_even t f hfe)
      R hR (spectralTimeResidual_support t f R hs) z)
    let A := crossQuotientLocalization N 0 K hK b hbound
    let a := 2*Real.sqrt (mN : ℝ)*|C| *Real.sqrt (m0 : ℝ)
    let b0 := Real.sqrt (mN : ℝ)*B*Real.sqrt (m0 : ℝ)
    (∫ z in Metric.closedBall o D, ∑ i, ‖inner ℂ (v i) (A (c z))‖^2) ≤
      (2/L^2)*(5*a^2*(∫ z in Metric.closedBall o D, ‖c z‖^2)+
        (2*a^2+2*b0^2)*(∫ z in Metric.closedBall o D, ‖d z‖^2)/(1+(t^2+1/4))) := by
  intro c d A a b0
  have hcc : Continuous c := cylinderAutomorphic.continuous.comp
    (cylinderAbelColumn_continuous _ _ R hR _)
  have hdc : Continuous d := cylinderAutomorphic.continuous.comp
    (cylinderAbelColumn_continuous _ _ R hR _)
  have hic : IntegrableOn (fun z => ‖c z‖^2) (Metric.closedBall o D) :=
    (hcc.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall o D)
  have hid : IntegrableOn (fun z => ‖d z‖^2) (Metric.closedBall o D) :=
    (hdc.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall o D)
  have hil : IntegrableOn (fun z => ∑ i, ‖inner ℂ (v i) (A (c z))‖^2)
      (Metric.closedBall o D) := by
    apply integrable_finsetSum
    intro i _
    exact (((continuous_const.inner (A.continuous.comp hcc)).norm).pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall o D)
  have hpoint (z : ℍ) : (∑ i, ‖inner ℂ (v i) (A (c z))‖^2) ≤
      (2/L^2)*(5*a^2*‖c z‖^2+(2*a^2+2*b0^2)*‖d z‖^2/(1+(t^2+1/4))) :=
    crossQuotientLocalization_residual_L2_bound N 0 b K hK hbK mN m0 hmN hm0
      B C hB hbound hgrad hreal r (t^2+1/4) v (c z) (d z) hv hr
      (by positivity) hgraph (cylinderTimeColumn_spectralResidual_graph f hfc hfe R hR hs z t)
      L hL hsep
  calc
    _ ≤ ∫ z in Metric.closedBall o D,
        (2/L^2)*(5*a^2*‖c z‖^2+(2*a^2+2*b0^2)*‖d z‖^2/(1+(t^2+1/4))) :=
      integral_mono_ae hil
        (((hic.const_mul _).add ((hid.const_mul _).div_const _)).const_mul _)
        (Filter.Eventually.of_forall hpoint)
    _ = _ := by
      rw [integral_const_mul, integral_add (hic.const_mul _)
        ((hid.const_mul _).div_const _), integral_const_mul, integral_div,
        integral_const_mul]

/-- A fixed broad spectral band supplies a gap proportional to t. -/
theorem broadBand_sqrt_gap (t r : ℝ) (ht : 2 ≤ t) (hr : 0 ≤ r)
    (hout : r ≤ t^2/4 ∨ 4*t^2 ≤ r) :
    t/4 ≤ |Real.sqrt (1+r)-Real.sqrt (1+(t^2+1/4))| := by
  have htp : 0 < t := by linarith
  have hs := Real.sq_sqrt (show 0 ≤ 1+r by positivity)
  have hc := Real.sq_sqrt (show 0 ≤ 1+(t^2+1/4) by positivity)
  have hsn := Real.sqrt_nonneg (1+r)
  have hcn := Real.sqrt_nonneg (1+(t^2+1/4))
  rcases hout with hlo | hhi
  · have hlow : Real.sqrt (1+r) ≤ 3*t/4 := by nlinarith [sq_nonneg (t-2)]
    have hcentre : t ≤ Real.sqrt (1+(t^2+1/4)) := by nlinarith
    have he := le_abs_self (-(Real.sqrt (1+r)-Real.sqrt (1+(t^2+1/4))))
    rw [abs_neg] at he
    linarith
  · have hhigh : 2*t ≤ Real.sqrt (1+r) := by nlinarith
    have hcentre : Real.sqrt (1+(t^2+1/4)) ≤ 3*t/2 := by nlinarith [sq_nonneg (t-2)]
    have he := le_abs_self (Real.sqrt (1+r)-Real.sqrt (1+(t^2+1/4)))
    linarith

/-- Source energy O(t ε) and residual energy O(t³ ε) yield O(ε/t)
leakage outside the broad band. All localization constants are retained. -/
theorem broadBand_residual_energy_rate (t ε a b G H E : ℝ)
    (ht : 0 < t) (hε : 0 ≤ ε) (hE : 0 ≤ E)
    (hG : G ≤ E*t*ε) (hH : H ≤ E*t^3*ε) :
    (2/(t/4)^2)*(5*a^2*G+(2*a^2+2*b^2)*H/(1+(t^2+1/4))) ≤
      32*(7*a^2+2*b^2)*E*ε/t := by
  have hden : 0 < 1+(t^2+1/4) := by positivity
  have hr : H/(1+(t^2+1/4)) ≤ E*t*ε := by
    apply (div_le_iff₀ hden).mpr
    apply hH.trans
    nlinarith [mul_nonneg (show 0 ≤ E*t*ε by positivity) (show 0 ≤ (5/4 : ℝ) by norm_num)]
  calc
    _ ≤ (2/(t/4)^2)*(5*a^2*(E*t*ε)+(2*a^2+2*b^2)*(E*t*ε)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [mul_div_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_left hG (by positivity))
        (mul_le_mul_of_nonneg_left hr (by positivity))
    _ = _ := by field_simp; ring

#print axioms cylinderTimeColumn_integrated_leakage
#print axioms broadBand_sqrt_gap
#print axioms broadBand_residual_energy_rate

end QuantitativeMaass
