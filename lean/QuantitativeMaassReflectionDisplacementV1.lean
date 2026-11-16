module

public import QuantitativeMaassReflectionSlicesV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix Complex
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels
open scoped Topology MatrixGroups ENNReal ComplexConjugate

namespace QuantitativeMaass

/-- Exact displacement numerator for the actual reflection J followed by
an integral fractional-linear transformation. -/
theorem reflected_displacement_identity (a b c d z : ℂ)
    (hd : c*(-conj z)+d≠0) :
    (z-(a*(-conj z)+b)/(c*(-conj z)+d))*(c*(-conj z)+d)=
      -c*z*conj z+d*z+a*conj z-b := by
  rw [sub_mul,div_mul_cancel₀ _ hd]
  ring

theorem reflected_displacement_real (a b c d : ℤ) (z : ℂ) :
    (-(c:ℂ)*z*conj z+(d:ℂ)*z+(a:ℂ)*conj z-b).re=
      -(c:ℝ)*(z.re^2+z.im^2)+((a:ℝ)+d)*z.re-b := by
  simp only [Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.mul_im,
    Complex.neg_re,Complex.neg_im,Complex.intCast_re,Complex.intCast_im,
    Complex.conj_re,Complex.conj_im]
  ring

/-- Every integral determinant-one reflected branch has an O(r) Euclidean
near-return area on a bounded rectangle above the real axis. -/
theorem reflected_fractional_displacement_volume (a b c d : ℤ) (hdet : a*d-b*c=1)
    (Ω : Set ℂ) (X Y Z D r : ℝ)
    (hX : 0≤X) (hY : 0<Y) (hZ : 0≤Z) (hD : 0≤D) (hr : 0<r)
    (hx : ∀ z∈Ω,|z.re|≤X) (hy : ∀ z∈Ω,Y≤z.im) (hz : ∀ z∈Ω,|z.im|≤Z)
    (hden : ∀ z∈Ω,(c:ℂ)*(-conj z)+d≠0)
    (hbound : ∀ z∈Ω,‖(c:ℂ)*(-conj z)+d‖≤D) :
    volume {z∈Ω | ‖z-((a:ℂ)*(-conj z)+b)/((c:ℂ)*(-conj z)+d)‖<r}≤
      ENNReal.ofReal ((4*X/Y+8*Z)*(D*r)) := by
  apply (measure_mono (show _⊆{z : ℂ | |z.re|≤X ∧ Y≤z.im ∧ |z.im|≤Z ∧
      |-(c:ℝ)*(z.re^2+z.im^2)+((a:ℝ)+d)*z.re-b|<D*r} from ?_)).trans
    (reflected_integral_numerator_area a b c d hdet X Y Z (D*r) hX hY hZ (mul_nonneg hD hr.le))
  intro z h
  refine ⟨hx z h.1,hy z h.1,hz z h.1,?_⟩
  rw [← reflected_displacement_real]
  apply (Complex.abs_re_le_norm _).trans_lt
  rw [← reflected_displacement_identity a b c d z (hden z h.1),norm_mul]
  calc
    _ < r*‖(c:ℂ)*(-conj z)+d‖ := mul_lt_mul_of_pos_right h.2 (norm_pos_iff.mpr (hden z h.1))
    _ ≤ r*D := mul_le_mul_of_nonneg_left (hbound z h.1) hr.le
    _ = D*r := mul_comm _ _

/-- The reflected fractional action has the same explicit sublevel bound
for hyperbolic area, after the elementary density comparison. -/
theorem reflected_hyperbolic_displacement_volume (a b c d : ℤ) (hdet : a*d-b*c=1)
    (Ω : Set ℍ) (X Y Z D r : ℝ)
    (hX : 0≤X) (hY : 0<Y) (hZ : 0≤Z) (hD : 0≤D) (hr : 0<r)
    (hx : ∀ z∈Ω,|z.re|≤X) (hy : ∀ z∈Ω,Y≤z.im) (hz : ∀ z∈Ω,|z.im|≤Z)
    (hden : ∀ z∈Ω,(c:ℂ)*(-conj (z:ℂ))+d≠0)
    (hbound : ∀ z∈Ω,‖(c:ℂ)*(-conj (z:ℂ))+d‖≤D) :
    volume {z∈Ω | ‖(z:ℂ)-((a:ℂ)*(-conj (z:ℂ))+b)/((c:ℂ)*(-conj (z:ℂ))+d)‖<r}≤
      ENNReal.ofReal ((1/Y)^2*((4*X/Y+8*Z)*(D*r))) := by
  let E := {z∈Ω | ‖(z:ℂ)-((a:ℂ)*(-conj (z:ℂ))+b)/((c:ℂ)*(-conj (z:ℂ))+d)‖<r}
  have hsub : UpperHalfPlane.coe '' E⊆{z∈UpperHalfPlane.coe '' Ω |
      ‖z-((a:ℂ)*(-conj z)+b)/((c:ℂ)*(-conj z)+d)‖<r} := by
    rintro z ⟨u,hu,rfl⟩
    exact ⟨⟨u,hu.1,rfl⟩,hu.2⟩
  have hp := reflected_fractional_displacement_volume a b c d hdet
    (UpperHalfPlane.coe '' Ω) X Y Z D r hX hY hZ hD hr
    (by rintro z ⟨u,hu,rfl⟩; exact hx u hu)
    (by rintro z ⟨u,hu,rfl⟩; exact hy u hu)
    (by rintro z ⟨u,hu,rfl⟩; exact hz u hu)
    (by rintro z ⟨u,hu,rfl⟩; exact hden u hu)
    (by rintro z ⟨u,hu,rfl⟩; exact hbound u hu)
  calc
    volume E ≤ ENNReal.ofReal ((1/Y)^2)*volume (UpperHalfPlane.coe '' E) :=
      QuantitativeHolomorphic.hyperbolic_volume_le_euclidean E hY (fun z h => hy z h.1)
    _ ≤ ENNReal.ofReal ((1/Y)^2)*ENNReal.ofReal ((4*X/Y+8*Z)*(D*r)) :=
      mul_le_mul le_rfl ((measure_mono hsub).trans hp) (by positivity) (by positivity)
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

/-- The genuine congruence action composed with Mathlib's reflection J.
The identity group element is included, and no small-radius assumption is used. -/
theorem congruence_reflected_displacement_volume (N : ℕ) (γ : gamma N)
    (Ω : Set ℍ) (X Y Z D r : ℝ)
    (hX : 0≤X) (hY : 0<Y) (hZ : 0≤Z) (hD : 0≤D) (hr : 0<r)
    (hx : ∀ z∈Ω,|z.re|≤X) (hy : ∀ z∈Ω,Y≤z.im) (hz : ∀ z∈Ω,|z.im|≤Z)
    (hbound : ∀ z∈Ω,‖((representative γ) 1 0:ℂ)*((J•z:ℍ):ℂ)+(representative γ) 1 1‖≤D) :
    volume {z∈Ω | ‖(z:ℂ)-((γ•(J•z):ℍ):ℂ)‖<r}≤
      ENNReal.ofReal ((1/Y)^2*((4*X/Y+8*Z)*(D*r))) := by
  have hd : (representative γ) 0 0*(representative γ) 1 1-
      (representative γ) 0 1*(representative γ) 1 0=1 := by
    simpa only [Matrix.det_fin_two] using (representative γ).property
  have hp := reflected_hyperbolic_displacement_volume
    ((representative γ) 0 0) ((representative γ) 0 1)
    ((representative γ) 1 0) ((representative γ) 1 1) hd Ω X Y Z D r hX hY hZ hD hr hx hy hz
    (fun z _ => by simpa only [coe_J_smul] using congruence_denominator_ne_zero N γ (J•z))
    (fun z h => by simpa only [coe_J_smul] using hbound z h)
  simpa only [congruence_action_fractional,coe_J_smul] using hp

#print axioms reflected_displacement_identity
#print axioms reflected_displacement_real
#print axioms reflected_fractional_displacement_volume
#print axioms reflected_hyperbolic_displacement_volume
#print axioms congruence_reflected_displacement_volume

end QuantitativeMaass
