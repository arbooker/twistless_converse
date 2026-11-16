module

public import QuantitativeMaassIntegralReflectionSublevelV1
public import QuantitativeMaassCylinderCorrespondenceBoundV1
public import QuantitativeMaassReflectionWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels
open scoped Topology ENNReal MatrixGroups

namespace QuantitativeMaass

/-- Finite propagation for a fixed correspondence matrix: the orbit radius
has just the additional displacement of the base point under that matrix. -/
theorem reflected_correspondence_displacement_in_diagonalOrbitSet (N : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (o x : ℍ) (L R : ℝ) (hx : dist x o≤L) (γ : gamma N)
    (hγ : dist (γ • (positiveIntegralGL M hM • (J•x))) x≤R) :
    γ∈diagonalOrbitSet N o (R+2*L+dist (positiveIntegralGL M hM • (J•o)) o) := by
  apply (mem_diagonalOrbitSet N o _ γ).mpr
  let G := positiveIntegralGL M hM
  have h1 := dist_triangle (γ•o) (γ•(G•(J•o))) o
  have h2 := dist_triangle (γ•(G•(J•o))) (γ•(G•(J•x))) o
  have h3 := dist_triangle (γ•(G•(J•x))) x o
  rw [congruence_action_dist,dist_comm o (G•(J•o))] at h1
  have hg : 0<G.det.val := by rw [positiveIntegralGL_det];exact_mod_cast hM
  rw [congruence_action_dist,positiveGL_action_dist G hg,reflection_dist,dist_comm o x] at h2
  change dist (γ • (G•(J•x))) x≤R at hγ
  change dist (γ•o) o≤R+2*L+dist (G•(J•o)) o
  linarith

/-- The full actual correspondence kernel has the same finite orbit support. -/
theorem radialReflectedIntegralKernel_eq_finite (N : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (o x : ℍ) (L : ℝ) (hx : dist x o≤L) :
    radialPoincareKernel N g x (positiveIntegralGL M hM • (J•x))=
      ∑ γ∈diagonalOrbitSet N o (R+2*L+dist (positiveIntegralGL M hM • (J•o)) o),
        g (Real.cosh (dist (γ • (positiveIntegralGL M hM • (J•x))) x)) := by
  classical
  simp only [radialPoincareKernel,poincareSum,radialFunction_upper]
  apply tsum_eq_sum
  intro γ hγ
  by_contra hn
  have hd : dist (γ • (positiveIntegralGL M hM • (J•x))) x≤R := by
    have hh := Real.cosh_le_cosh.mp (hs hn)
    simpa only [abs_of_nonneg dist_nonneg,abs_of_nonneg hR] using hh
  exact hγ (reflected_correspondence_displacement_in_diagonalOrbitSet N M hM o x L R hx γ hd)

/-- Integrate the actual off-diagonal radial profile along every reflected
congruence-times-integral-matrix branch, including elliptic products. -/
theorem congruence_product_reflected_profile_integral_bound (N : ℕ) (o : ℍ) (L D B : ℝ) (hB : 0<B)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) (hentry : ∀ i j,|(M i j:ℝ)|≤B)
    (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    IntegrableOn (fun z : ℍ => g (Real.cosh (dist (γ • (positiveIntegralGL M hM • (J•z))) z))) (Metric.closedBall o L) ∧
    (∫ z in Metric.closedBall o L,‖g (Real.cosh (dist (γ • (positiveIntegralGL M hM • (J•z))) z))‖)≤
      C*(Real.pi*(volume.real (Metric.closedBall o L)+reflectedSublevelConstant o L (D+2*Real.log (2*B)))) := by
  have hc : Continuous (fun z : ℍ => g (Real.cosh (dist (γ • (positiveIntegralGL M hM • (J•z))) z))) :=
    hg.comp_continuous (Real.continuous_cosh.comp (((AsymptoticRationalBranches.action_continuous γ.val).comp ((continuous_const_smul (positiveIntegralGL M hM)).comp (continuous_const_smul J))).dist continuous_id))
      (fun _ => Real.one_le_cosh _)
  have hi : IntegrableOn (fun z : ℍ => g (Real.cosh (dist (γ • (positiveIntegralGL M hM • (J•z))) z))) (Metric.closedBall o L) :=
    hc.continuousOn.integrableOn_compact (isCompact_closedBall o L)
  obtain ⟨hj,hbound⟩ := congruence_product_reflected_inverse_sqrt_integral N o L D B hB γ hγ M hM hentry
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ z in Metric.closedBall o L,C*(1/Real.sqrt (dist (γ • (positiveIntegralGL M hM • (J•z))) z)) := by
      apply integral_mono_ae hi.norm (hj.const_mul C)
      filter_upwards [congruence_product_reflected_displacement_pos_ae N o L D B hB γ hγ M hM hentry] with z hz
      calc
        _ ≤ C/Real.sqrt (Real.sinh (dist (γ • (positiveIntegralGL M hM • (J•z))) z)) := hb _ hz
        _ ≤ C/Real.sqrt (dist (γ • (positiveIntegralGL M hM • (J•z))) z) := div_le_div_of_nonneg_left hC
          (Real.sqrt_pos.mpr hz) (Real.sqrt_le_sqrt (Real.self_le_sinh_iff.mpr hz.le))
        _ = _ := by ring
    _ = C*(∫ z in Metric.closedBall o L,1/Real.sqrt (dist (γ • (positiveIntegralGL M hM • (J•z))) z)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound hC

#print axioms reflected_correspondence_displacement_in_diagonalOrbitSet
#print axioms radialReflectedIntegralKernel_eq_finite
#print axioms congruence_product_reflected_profile_integral_bound

end QuantitativeMaass
