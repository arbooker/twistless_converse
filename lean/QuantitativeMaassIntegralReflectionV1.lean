module

public import QuantitativeMaassReflectionSublevelV1
public import QuantitativeMaassIntegralProductsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix Complex
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels
open scoped Topology MatrixGroups ENNReal ComplexConjugate

namespace QuantitativeMaass

/-- Both reflection cases, with an explicit bound independent of the
matrix entries and valid for every positive sublevel width. -/
theorem positive_reflected_integral_numerator_area (a b c d : ℤ) (hdet : 0<a*d-b*c)
    (X Y Z δ : ℝ) (hX : 0≤X) (hY : 0<Y) (hZ : 0≤Z) (hδ : 0≤δ) :
    volume {z : ℂ | |z.re|≤X ∧ Y≤z.im ∧ |z.im|≤Z ∧
      |-(c:ℝ)*(z.re^2+z.im^2)+((a:ℝ)+d)*z.re-b|<δ}≤
      ENNReal.ofReal ((4*X/Y+8*Z)*δ) := by
  by_cases hc : c=0
  · have had : (1:ℝ)≤(a:ℝ)*(d:ℝ) := by
      have hi : (1:ℤ)≤a*d := by simpa [hc] using (Int.add_one_le_iff.mpr hdet)
      exact_mod_cast hi
    have hsum : 1≤|(a:ℝ)+(d:ℝ)| := by
      have hs := sq_nonneg ((a:ℝ)-(d:ℝ))
      have he := sq_abs ((a:ℝ)+(d:ℝ))
      nlinarith [abs_nonneg ((a:ℝ)+(d:ℝ))]
    apply (measure_mono (show _⊆{z : ℂ | |z.im|≤Z ∧ |((a:ℝ)+d)*z.re-b|<δ} from ?_)).trans
      ((reflected_affine_area (a+d) b Z δ hsum hZ hδ).trans ?_)
    · intro z hz
      exact ⟨hz.2.2.1,by simpa [hc] using hz.2.2.2⟩
    · apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_nonneg (div_nonneg (by positivity : 0≤4*X) hY.le) hδ]
  · have hc1 : 1≤|(c:ℝ)| := by
      have hi : (1:ℤ)≤|c| := by have hp := abs_pos.mpr hc; omega
      exact_mod_cast hi
    apply (measure_mono (show _⊆{z : ℂ | |z.re|≤X ∧ Y≤z.im ∧
      |-(c:ℝ)*(z.re^2+z.im^2)+((a:ℝ)+d)*z.re-b|<δ} from ?_)).trans
      ((reflected_quadratic_area a b c d X Y δ hc1 hX hY hδ).trans ?_)
    · intro z hz
      exact ⟨hz.1,hz.2.1,hz.2.2.2⟩
    · apply ENNReal.ofReal_le_ofReal
      have he : 4*X*δ/Y = (4*X/Y)*δ := by ring
      rw [he]
      nlinarith [mul_nonneg hZ hδ]

/-- Every integral positive-determinant reflected branch has an O(r) Euclidean
near-return area on a bounded rectangle above the real axis. -/
theorem positive_reflected_fractional_displacement_volume (a b c d : ℤ) (hdet : 0<a*d-b*c)
    (Ω : Set ℂ) (X Y Z D r : ℝ)
    (hX : 0≤X) (hY : 0<Y) (hZ : 0≤Z) (hD : 0≤D) (hr : 0<r)
    (hx : ∀ z∈Ω,|z.re|≤X) (hy : ∀ z∈Ω,Y≤z.im) (hz : ∀ z∈Ω,|z.im|≤Z)
    (hden : ∀ z∈Ω,(c:ℂ)*(-conj z)+d≠0)
    (hbound : ∀ z∈Ω,‖(c:ℂ)*(-conj z)+d‖≤D) :
    volume {z∈Ω | ‖z-((a:ℂ)*(-conj z)+b)/((c:ℂ)*(-conj z)+d)‖<r}≤
      ENNReal.ofReal ((4*X/Y+8*Z)*(D*r)) := by
  apply (measure_mono (show _⊆{z : ℂ | |z.re|≤X ∧ Y≤z.im ∧ |z.im|≤Z ∧
      |-(c:ℝ)*(z.re^2+z.im^2)+((a:ℝ)+d)*z.re-b|<D*r} from ?_)).trans
    (positive_reflected_integral_numerator_area a b c d hdet X Y Z (D*r) hX hY hZ (mul_nonneg hD hr.le))
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
theorem positive_reflected_hyperbolic_displacement_volume (a b c d : ℤ) (hdet : 0<a*d-b*c)
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
  have hp := positive_reflected_fractional_displacement_volume a b c d hdet
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

/-- Reflected rational branches satisfy the same explicit local area estimate
for every positive integral determinant. -/
theorem positiveIntegralGL_reflected_displacement_volume
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (Ω : Set ℍ) (X Y Z D r : ℝ)
    (hX : 0≤X) (hY : 0<Y) (hZ : 0≤Z) (hD : 0≤D) (hr : 0<r)
    (hx : ∀ z∈Ω,|z.re|≤X) (hy : ∀ z∈Ω,Y≤z.im) (hz : ∀ z∈Ω,|z.im|≤Z)
    (hbound : ∀ z∈Ω,‖(M 1 0:ℂ)*((J•z:ℍ):ℂ)+M 1 1‖≤D) :
    volume {z∈Ω | ‖(z:ℂ)-((positiveIntegralGL M hM • (J•z):ℍ):ℂ)‖<r}≤
      ENNReal.ofReal ((1/Y)^2*((4*X/Y+8*Z)*(D*r))) := by
  have hd : 0<M 0 0*M 1 1-M 0 1*M 1 0 := by
    simpa only [Matrix.det_fin_two] using hM
  have hp := positive_reflected_hyperbolic_displacement_volume
    (M 0 0) (M 0 1) (M 1 0) (M 1 1) hd Ω X Y Z D r hX hY hZ hD hr hx hy hz
    (fun z _ => by simpa only [coe_J_smul] using
      QuantitativeArithmetic.integer_matrix_denominator_ne_zero M hM.ne' (J•z))
    (fun z h => by simpa only [coe_J_smul] using hbound z h)
  simpa only [positiveIntegralGL_fractional,coe_J_smul] using hp

#print axioms positive_reflected_integral_numerator_area
#print axioms positive_reflected_fractional_displacement_volume
#print axioms positive_reflected_hyperbolic_displacement_volume
#print axioms positiveIntegralGL_reflected_displacement_volume

end QuantitativeMaass
