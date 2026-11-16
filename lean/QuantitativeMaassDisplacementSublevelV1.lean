module

public import QuantitativeMaassGeometricRemainderV1
public import QuantitativeHolomorphicAutomaticGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels
open scoped Topology MatrixGroups ENNReal

namespace QuantitativeMaass

/-- Exact fractional-linear action of the selected integral representative. -/
theorem congruence_action_fractional (N : ℕ) (γ : gamma N) (z : ℍ) :
    ((γ•z : ℍ):ℂ)=
      (((representative γ) 0 0:ℂ)*(z:ℂ)+(representative γ) 0 1)/
      (((representative γ) 1 0:ℂ)*(z:ℂ)+(representative γ) 1 1) := by
  have he : representative γ•z=γ•z := by
    rw [← integralLabel_action,representative_label]
    rfl
  rw [← he]
  simpa using coe_specialLinearGroup_apply (representative γ) z

theorem congruence_denominator_ne_zero (N : ℕ) (γ : gamma N) (z : ℍ) :
    ((representative γ) 1 0:ℂ)*(z:ℂ)+(representative γ) 1 1≠0 :=
  QuantitativeArithmetic.integer_matrix_denominator_ne_zero (representative γ).val
    (by rw [(representative γ).property]; norm_num) z

/-- A nonidentity projective element automatically has a nonscalar integral
representative, including elliptic and parabolic elements. -/
theorem congruence_representative_nonscalar (N : ℕ) (γ : gamma N) (hγ : γ≠1) :
    (representative γ) 1 0≠0 ∨ (representative γ) 1 1≠(representative γ) 0 0 ∨
      (representative γ) 0 1≠0 := by
  by_contra hh
  push Not at hh
  have ha : ((representative γ) 0 0:ℂ)≠0 := by
    simpa only [hh.1,hh.2.1,Int.cast_zero,zero_mul,zero_add] using
      congruence_denominator_ne_zero N γ I
  apply hγ
  apply Subtype.ext
  apply QuantitativeHolomorphic.rational_label_eq_one_of_fixed γ.val
  intro z
  apply UpperHalfPlane.ext
  change ((γ•z : ℍ):ℂ)=(z:ℂ)
  rw [congruence_action_fractional N γ z]
  simp only [hh.1,hh.2.1,hh.2.2,Int.cast_zero,zero_mul,zero_add,add_zero,
    mul_div_cancel_left₀ _ ha]

/-- Quantitative near-return area for an actual nonidentity congruence
transformation. Matrix nonscalarity, determinant and denominator conditions
are discharged from the group action; only geometric size bounds remain. -/
theorem congruence_displacement_sublevel_volume (N : ℕ) (γ : gamma N) (hγ : γ≠1)
    (Ω : Set ℍ) (D r Y : ℝ) (hD : 0≤D) (hr : 0<r) (hr1 : r≤1)
    (hsmall : r*D≤1) (hY : 0<Y) (hheight : ∀ z∈Ω,Y≤z.im)
    (hbound : ∀ z∈Ω,‖((representative γ) 1 0:ℂ)*(z:ℂ)+(representative γ) 1 1‖≤D) :
    volume {z∈Ω | ‖(z:ℂ)-((γ•z : ℍ):ℂ)‖<r} ≤
      ENNReal.ofReal ((1/Y)^2*((2*Real.pi*D+Real.pi*D^2)*r)) := by
  have hdet : (representative γ) 0 0*(representative γ) 1 1-
      (representative γ) 0 1*(representative γ) 1 0≠0 := by
    have hh := (representative γ).property
    rw [Matrix.det_fin_two] at hh
    rw [hh]
    norm_num
  have hb := QuantitativeHolomorphic.hyperbolic_integral_matrix_displacement_volume
    ((representative γ) 0 0) ((representative γ) 0 1)
    ((representative γ) 1 0) ((representative γ) 1 1) hdet
    (congruence_representative_nonscalar N γ hγ) Ω hD hr hr1 hsmall hY hheight
    (fun z _ => congruence_denominator_ne_zero N γ z) hbound
  simpa only [congruence_action_fractional N γ] using hb

/-- A union bound for ALL nonidentity near returns in a finite group family.
The denominator bound is uniform in that family; no separation of fixed points
or freeness away from a chosen exceptional set is assumed. -/
theorem congruence_near_returns_volume (N : ℕ) (S : Finset (gamma N))
    (Ω : Set ℍ) (D r Y : ℝ) (hD : 0≤D) (hr : 0<r) (hr1 : r≤1)
    (hsmall : r*D≤1) (hY : 0<Y) (hheight : ∀ z∈Ω,Y≤z.im)
    (hbound : ∀ γ∈S,∀ z∈Ω,
      ‖((representative γ) 1 0:ℂ)*(z:ℂ)+(representative γ) 1 1‖≤D) :
    volume {z∈Ω | ∃ γ∈S,γ≠1 ∧ ‖(z:ℂ)-((γ•z : ℍ):ℂ)‖<r} ≤
      (S.card:ℝ≥0∞)*ENNReal.ofReal ((1/Y)^2*((2*Real.pi*D+Real.pi*D^2)*r)) := by
  classical
  let E (γ : gamma N) := {z∈Ω | γ≠1 ∧ ‖(z:ℂ)-((γ•z : ℍ):ℂ)‖<r}
  have hsub : {z∈Ω | ∃ γ∈S,γ≠1 ∧ ‖(z:ℂ)-((γ•z : ℍ):ℂ)‖<r}⊆⋃ γ∈S,E γ := by
    rintro z ⟨hz,γ,hγ,hn,hd⟩
    exact mem_iUnion.mpr ⟨γ,mem_iUnion.mpr ⟨hγ,⟨hz,hn,hd⟩⟩⟩
  calc
    _ ≤ volume (⋃ γ∈S,E γ) := measure_mono hsub
    _ ≤ ∑ γ∈S,volume (E γ) := measure_biUnion_finset_le S E
    _ ≤ ∑ _γ∈S,ENNReal.ofReal ((1/Y)^2*((2*Real.pi*D+Real.pi*D^2)*r)) := by
      apply Finset.sum_le_sum
      intro γ hγ
      by_cases hn : γ=1
      · have hz : E γ=∅ := by simp [E,hn]
        rw [hz,measure_empty]
        exact bot_le
      · have heq : E γ={z∈Ω | ‖(z:ℂ)-((γ•z : ℍ):ℂ)‖<r} := by simp [E,hn]
        rw [heq]
        exact congruence_displacement_sublevel_volume N γ hn Ω D r Y hD hr hr1 hsmall
          hY hheight (hbound γ hγ)
    _ = _ := by simp

/-- Every entry of the actual representative is bounded explicitly by the
base-point displacement, uniformly in the level. -/
theorem diagonalOrbitSet_entry_bound (N : ℕ) (o : ℍ) (D : ℝ) (γ : gamma N)
    (hγ : γ∈diagonalOrbitSet N o D) (i j : Fin 2) :
    |((representative γ) i j:ℝ)|≤Real.exp (D/2+dist o I) := by
  have hd := (mem_diagonalOrbitSet N o D γ).mp hγ
  have h1 := dist_triangle (γ•I) (γ•o) I
  have h2 := dist_triangle (γ•o) o I
  rw [congruence_action_dist,dist_comm I o] at h1
  have he : representative γ•I=γ•I := by
    rw [← integralLabel_action,representative_label]
    rfl
  apply QuantitativeArithmeticMaassOverlap.entry_abs_le_exp
  rw [he]
  linarith

/-- Explicit Euclidean coordinate bound on a hyperbolic ball. -/
theorem norm_coe_le_on_ball (o z : ℍ) (L : ℝ) (hz : dist z o≤L) :
    ‖(z:ℂ)‖≤‖(o:ℂ)‖+o.im*Real.exp L := by
  have h1 : ‖(z:ℂ)‖≤‖(o:ℂ)‖+dist (z:ℂ) (o:ℂ) := by
    simpa only [dist_zero_right,add_comm] using dist_triangle (z:ℂ) (o:ℂ) 0
  have h2 := dist_coe_le z o
  have h3 : Real.exp (dist z o)≤Real.exp L := Real.exp_le_exp.mpr hz
  nlinarith [o.im_pos,mul_le_mul_of_nonneg_left h3 o.im_pos.le]

/-- Explicit lower height bound on a hyperbolic ball. -/
theorem im_lower_on_ball (o z : ℍ) (L : ℝ) (hz : dist z o≤L) :
    o.im/Real.exp L≤z.im := by
  have h := im_div_exp_dist_le o z
  rw [dist_comm o z] at h
  exact (div_le_div_of_nonneg_left o.im_pos.le (Real.exp_pos _)
    (Real.exp_le_exp.mpr hz)).trans h

def displacementDenominatorBound (o : ℍ) (L D : ℝ) : ℝ :=
  Real.exp (D/2+dist o I)*(‖(o:ℂ)‖+o.im*Real.exp L+1)

theorem displacementDenominatorBound_pos (o : ℍ) (L D : ℝ) :
    0<displacementDenominatorBound o L D := by
  unfold displacementDenominatorBound
  positivity

/-- The denominator bound is uniform in ALL group elements in the orbit set
and all centres in the ball, with its radius dependence explicit. -/
theorem diagonalOrbitSet_denominator_bound (N : ℕ) (o z : ℍ) (L D : ℝ)
    (hz : dist z o≤L) (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D) :
    ‖((representative γ) 1 0:ℂ)*(z:ℂ)+(representative γ) 1 1‖≤
      displacementDenominatorBound o L D := by
  have hc := diagonalOrbitSet_entry_bound N o D γ hγ 1 0
  have hd := diagonalOrbitSet_entry_bound N o D γ hγ 1 1
  have hcast (a : ℤ) : ‖(a:ℂ)‖=|(a:ℝ)| := by
    rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ‖((representative γ) 1 0:ℂ)*(z:ℂ)‖+‖((representative γ) 1 1:ℂ)‖ := norm_add_le _ _
    _ = |((representative γ) 1 0:ℝ)| * ‖(z:ℂ)‖+|((representative γ) 1 1:ℝ)| := by
      rw [norm_mul,hcast,hcast]
    _ ≤ Real.exp (D/2+dist o I)*(‖(o:ℂ)‖+o.im*Real.exp L)+Real.exp (D/2+dist o I) := by
      apply add_le_add _ hd
      exact mul_le_mul hc (norm_coe_le_on_ball o z L hz) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by unfold displacementDenominatorBound; ring

/-- Original congruence near-return area with every geometric constant
explicit, chosen before the level, group element, or small radius.
All nonidentity elements of the finite orbit set are included. -/
theorem diagonalOrbitSet_near_returns_volume (N : ℕ) [NeZero N] (o : ℍ) (L D r : ℝ)
    (hr : 0<r) (hr1 : r≤1) (hsmall : r*displacementDenominatorBound o L D≤1) :
    volume {z∈Metric.closedBall o L | ∃ γ∈diagonalOrbitSet N o D,
      γ≠1 ∧ ‖(z:ℂ)-((γ•z : ℍ):ℂ)‖<r} ≤
      (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 D:ℝ≥0∞)*
        ENNReal.ofReal ((1/(o.im/Real.exp L))^2*
          ((2*Real.pi*displacementDenominatorBound o L D+
            Real.pi*(displacementDenominatorBound o L D)^2)*r)) := by
  have h := congruence_near_returns_volume N (diagonalOrbitSet N o D)
    (Metric.closedBall o L) (displacementDenominatorBound o L D) r (o.im/Real.exp L)
    (displacementDenominatorBound_pos o L D).le hr hr1 hsmall (by positivity)
    (fun z hz => im_lower_on_ball o z L hz)
    (fun γ hγ z hz => diagonalOrbitSet_denominator_bound N o z L D hz γ hγ)
  apply h.trans
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast diagonalOrbitSet_card_bound N o D) (by positivity)

#print axioms diagonalOrbitSet_entry_bound
#print axioms norm_coe_le_on_ball
#print axioms im_lower_on_ball
#print axioms displacementDenominatorBound_pos
#print axioms diagonalOrbitSet_denominator_bound
#print axioms diagonalOrbitSet_near_returns_volume
#print axioms congruence_action_fractional
#print axioms congruence_denominator_ne_zero
#print axioms congruence_representative_nonscalar
#print axioms congruence_displacement_sublevel_volume
#print axioms congruence_near_returns_volume

end QuantitativeMaass
