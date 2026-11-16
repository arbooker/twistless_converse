module

public import QuantitativeMaassAveragingNumeratorV1
public import QuantitativeMaassHyperbolicSublevelV1
public import QuantitativeMaassCylinderStationaryV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticMobiusFold
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- The affine averaging numerator is the displacement numerator of the
actual composed Möbius action, not an auxiliary polynomial model. -/
theorem averaging_action_displacement_identity (G H : GL (Fin 2) ℝ)
    (hG : G.val.det=1) (hH : H.val.det=1) (u : ℝ) (z : ℍ) :
    ((z:ℂ)-((G • (u+ᵥ(H•z)):ℍ):ℂ))*denom (G*translation u*H) z=
      realMatrixDisplacementNumerator (G.val*!![1,u;0,1]*H.val) z := by
  have hg : 0<(G*translation u*H).det.val := by
    change 0<(G.val*!![1,u;0,1]*H.val).det
    rw [Matrix.det_mul,Matrix.det_mul,hG,hH]
    norm_num
  have ht : translation u • (H•z)=u+ᵥ(H•z) := by
    apply UpperHalfPlane.ext
    rw [translation_action,coe_vadd]
    ring
  have ha : (G*translation u*H) • z=G • (u+ᵥ(H•z)) := by
    rw [mul_smul,mul_smul,ht]
  rw [←ha,coe_smul_of_det_pos hg,sub_mul,div_mul_cancel₀ _ (denom_ne_zero _ _)]
  change (z:ℂ)*(((G.val*!![1,u;0,1]*H.val) 1 0:ℂ)*(z:ℂ)+(G.val*!![1,u;0,1]*H.val) 1 1)-
    (((G.val*!![1,u;0,1]*H.val) 0 0:ℂ)*(z:ℂ)+(G.val*!![1,u;0,1]*H.val) 0 1)=_
  unfold realMatrixDisplacementNumerator
  ring

/-- Uniform Euclidean near-return length for an actual averaging word.
The denominator cost is explicit and the matrix slope is proved. -/
theorem averaging_euclidean_parameter_sublevel (G H : GL (Fin 2) ℝ)
    (hG : G.val.det=1) (hH : H.val.det=1) (B : ℝ) (hB : 0<B)
    (hGb : ∀ i j,|G.val i j|≤B) (hHb : ∀ i j,|H.val i j|≤B)
    (z : ℍ) (X Y D : ℝ) (hX : 0≤X) (hY : 0<Y) (hD : 0<D)
    (hx : |z.re|≤X) (hy : Y≤z.im)
    (hden : ∀ u∈Icc (0:ℝ) 1,‖denom (G*translation u*H) z‖≤D)
    (r : ℝ) (hr : 0<r) :
    volume {u∈Icc (0:ℝ) 1 | ‖(z:ℂ)-((G • (u+ᵥ(H•z)):ℍ):ℂ)‖<r}≤
      ENNReal.ofReal (4*(D*r)/((1/(B*(1+(X+1)/Y)))^2)) := by
  apply (measure_mono (show _⊆{u : ℝ |
      ‖realMatrixDisplacementNumerator (G.val*!![1,u;0,1]*H.val) z‖<D*r} from ?_)).trans
    (averaging_numerator_parameter_sublevel G.val H.val hG hH B hB hGb hHb z X Y hX hY hx hy
      (D*r) (mul_pos hD hr))
  intro u hu
  change ‖realMatrixDisplacementNumerator (G.val*!![1,u;0,1]*H.val) z‖<D*r
  rw [←averaging_action_displacement_identity G H hG hH u z,norm_mul]
  calc
    _<r*‖denom (G*translation u*H) z‖ :=
      mul_lt_mul_of_pos_right hu.2 (norm_pos_iff.mpr (denom_ne_zero _ _))
    _≤r*D := mul_le_mul_of_nonneg_left (hden u hu.1) hr.le
    _=D*r := mul_comm _ _

/-- The actual hyperbolic displacement has linear small sublevels in the
averaging parameter, uniformly up to the explicit geometry constants. -/
theorem averaging_hyperbolic_parameter_sublevel (G H : GL (Fin 2) ℝ)
    (hG : G.val.det=1) (hH : H.val.det=1) (B : ℝ) (hB : 0<B)
    (hGb : ∀ i j,|G.val i j|≤B) (hHb : ∀ i j,|H.val i j|≤B)
    (z : ℍ) (X Y D : ℝ) (hX : 0≤X) (hY : 0<Y) (hD : 0<D)
    (hx : |z.re|≤X) (hy : Y≤z.im)
    (hden : ∀ u∈Icc (0:ℝ) 1,‖denom (G*translation u*H) z‖≤D)
    (r : ℝ) (hr : 0<r) :
    volume {u∈Icc (0:ℝ) 1 | dist (G • (u+ᵥ(H•z))) z<r}≤
      ENNReal.ofReal ((1+4*D*localDisplacementScale z 0/((1/(B*(1+(X+1)/Y)))^2))*r) := by
  have hscale := localDisplacementScale_pos z 0
  have hm : 0<(1/(B*(1+(X+1)/Y)))^2 := by positivity
  by_cases hr1 : r≤1
  · apply (measure_mono (show _⊆{u∈Icc (0:ℝ) 1 |
        ‖(z:ℂ)-((G • (u+ᵥ(H•z)):ℍ):ℂ)‖<localDisplacementScale z 0*r} from ?_)).trans
      ((averaging_euclidean_parameter_sublevel G H hG hH B hB hGb hHb z X Y D hX hY hD hx hy hden
        _ (mul_pos hscale hr)).trans ?_)
    · intro u hu
      refine ⟨hu.1,?_⟩
      exact (euclidean_displacement_le_hyperbolic z z (G • (u+ᵥ(H•z))) 0 (by simp)
        (hu.2.le.trans hr1)).trans_lt (mul_lt_mul_of_pos_left hu.2 hscale)
    · apply ENNReal.ofReal_le_ofReal
      calc
        _ = (4*D*localDisplacementScale z 0/((1/(B*(1+(X+1)/Y)))^2))*r := by ring
        _ ≤ _ := by nlinarith
  · have hlarge : 1<r := lt_of_not_ge hr1
    apply (measure_mono (show {u∈Icc (0:ℝ) 1 | dist (G • (u+ᵥ(H•z))) z<r}⊆Icc (0:ℝ) 1 from
      fun _ hu => hu.1)).trans
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    have hn : 0≤4*D*localDisplacementScale z 0/((1/(B*(1+(X+1)/Y)))^2) := by positivity
    nlinarith

#print axioms averaging_action_displacement_identity
#print axioms averaging_euclidean_parameter_sublevel
#print axioms averaging_hyperbolic_parameter_sublevel

end QuantitativeMaass
