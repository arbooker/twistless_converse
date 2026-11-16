module

public import QuantitativeMaassCutoffResidualV1
public import QuantitativeMaassCrossPoincareBoundV1
public import QuantitativeMaassPoincareGraphLinearV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- The residual of a genuine compact seed belongs to the actual
Friedrichs graph; no separate operator-domain assumption is needed. -/
theorem friedrichsGraph_seed_residual (N : ℕ) (u : SmoothUpperSeed) (μ : ℂ) :
    FriedrichsGraph N (poincareSeedVector N u)
      (μ • poincareSeedVector N u+
        (poincareSeedVector N u.laplacian-μ • poincareSeedVector N u)) := by
  simpa only [add_sub_cancel] using friedrichsGraph_poincareSeed N u

/-- An actual compactly localized Poincare graph residual is bounded
by the local source residual, mass and gradient integrals. The target
overlap multiplicity and both cutoff derivative bounds are explicit. -/
theorem localized_poincare_residual_norm_sq (N : ℕ)
    (b : SmoothUpperSeed) (G : Point → ℂ)
    (hG : ContDiffOn ℝ ∞ G {Z | 0<Z.2})
    (hreal : ∀ W, star (b.toFun W)=b.toFun W)
    (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m)
    (μ : ℂ) (B H C : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hlap : ∀ z ∈ K, ‖upperLaplacian b.toFun z‖ ≤ H)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2) :
    let q := b.localized G hG
    ‖poincareSeedVector N q.laplacian-μ • poincareSeedVector N q‖^2 ≤
      3*(m:ℝ)*(B^2*(∫ z in K, ‖upperLaplacian G z-μ*upperFunction G z‖^2)+
        H^2*(∫ z in K, ‖upperFunction G z‖^2)+
        4*C^2*(∫ z in K, (upperEnergy G G z).re)) := by
  intro q
  let w := q.laplacian.add (q.smul (-μ))
  have hqK : tsupport (upperFunction q.toFun) ⊆ K :=
    tsupport_mul_subset_right.trans hbK
  have hwzero (z : ℍ) (hz : z ∉ K) : upperFunction w.toFun z=0 := by
    have hq : upperFunction q.toFun z=0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hz (hqK hh))
    have hl : upperLaplacian q.toFun z=0 := by
      by_contra hn
      exact hz (hqK (upperLaplacian_support q.toFun hn))
    change upperLaplacian q.toFun z+(-μ)*upperFunction q.toFun z=0
    rw [hq,hl,mul_zero,add_zero]
  have hwK : tsupport (upperFunction w.toFun) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hn
    exact hz (hwzero z hn)
  have hp := poincareSeedVector_norm_sq_le_of_overlap N K hK m hm w hwK
  have hwvec : poincareSeedVector N w=
      poincareSeedVector N q.laplacian-μ • poincareSeedVector N q := by
    rw [poincareSeedVector_add,poincareSeedVector_smul]
    module
  rw [hwvec] at hp
  have hrestrict : (∫ z : ℍ, ‖upperFunction w.toFun z‖^2)=
      ∫ z in K, ‖upperFunction w.toFun z‖^2 := by
    rw [← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      by_cases hz : z ∈ K
      · rw [indicator_of_mem hz]
      · rw [indicator_of_notMem hz]
        dsimp only
        rw [hwzero z hz,norm_zero,zero_pow (by decide : 2≠0)])
  rw [hrestrict] at hp
  have hwInt : IntegrableOn (fun z : ℍ => ‖upperFunction w.toFun z‖^2) K :=
    (((upperFunction_continuous w.smooth).norm.pow 2).continuousOn.integrableOn_compact hK)
  have hrInt : IntegrableOn (fun z : ℍ => ‖upperLaplacian G z-μ*upperFunction G z‖^2) K :=
    ((((upperLaplacian_continuous hG).sub
      (continuous_const.mul (upperFunction_continuous hG))).norm.pow 2).continuousOn.integrableOn_compact hK)
  have hgInt : IntegrableOn (fun z : ℍ => ‖upperFunction G z‖^2) K :=
    (((upperFunction_continuous hG).norm.pow 2).continuousOn.integrableOn_compact hK)
  have heInt : IntegrableOn (fun z : ℍ => (upperEnergy G G z).re) K :=
    ((Complex.continuous_re.comp (upperEnergy_continuous hG hG)).continuousOn.integrableOn_compact hK)
  have hpoint (z : ℍ) (hz : z ∈ K) :
      ‖upperFunction w.toFun z‖^2 ≤
      3*(B^2*‖upperLaplacian G z-μ*upperFunction G z‖^2+
        H^2*‖upperFunction G z‖^2+4*C^2*(upperEnergy G G z).re) := by
    have hq : q.toFun = fun W => b.toFun W*G W := by
      funext W
      exact mul_comm _ _
    change ‖hyperbolic q.toFun (z.re,z.im)+(-μ)*q.toFun (z.re,z.im)‖^2 ≤ _
    rw [hq]
    simpa only [neg_mul,sub_eq_add_neg,upperLaplacian,upperFunction,upperEnergy] using
      hyperbolic_cutoff_residual_norm_sq b.toFun G b.smooth hG hreal μ
        (z.re,z.im) z.im_pos B H C hB hH (hbound z hz) (hlap z hz) (hgrad z hz)
  have hlocal : (∫ z in K, ‖upperFunction w.toFun z‖^2) ≤
      3*(B^2*(∫ z in K, ‖upperLaplacian G z-μ*upperFunction G z‖^2)+
        H^2*(∫ z in K, ‖upperFunction G z‖^2)+
        4*C^2*(∫ z in K, (upperEnergy G G z).re)) := by
    calc
      _ ≤ ∫ z in K, 3*(B^2*‖upperLaplacian G z-μ*upperFunction G z‖^2+
          H^2*‖upperFunction G z‖^2+4*C^2*(upperEnergy G G z).re) := by
        apply integral_mono_ae hwInt
          (((hrInt.const_mul _).add (hgInt.const_mul _)).add (heInt.const_mul _) |>.const_mul _)
        filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
        exact hpoint z hz
      _ = _ := by
        have hsum := integral_add ((hrInt.const_mul (B^2)).add (hgInt.const_mul (H^2)))
          (heInt.const_mul (4*C^2))
        have htwo := integral_add (hrInt.const_mul (B^2)) (hgInt.const_mul (H^2))
        simp only [Pi.add_apply] at hsum htwo
        rw [integral_const_mul,hsum,htwo]
        simp only [integral_const_mul]
  apply (hp.trans (mul_le_mul_of_nonneg_left hlocal (Nat.cast_nonneg m))).trans_eq
  ring

#print axioms friedrichsGraph_seed_residual
#print axioms localized_poincare_residual_norm_sq

end QuantitativeMaass
