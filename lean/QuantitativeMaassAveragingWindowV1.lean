module

public import QuantitativeMaassAveragingIntegralV1
public import QuantitativeMaassCylinderWindowBranchV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open scoped Topology ENNReal FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- Bounded coefficients may be inserted into the actual averaging integral.
Its bound has no identity contribution and uses the proved sublevel estimate. -/
theorem averaging_weighted_profile_bound (G H : GL (Fin 2) ℝ)
    (hG : G.val.det=1) (hH : H.val.det=1) (B : ℝ) (hB : 0<B)
    (hGb : ∀ i j,|G.val i j|≤B) (hHb : ∀ i j,|H.val i j|≤B)
    (z : ℍ) (X Y : ℝ) (hX : 0≤X) (hY : 0<Y) (hx : |z.re|≤X) (hy : Y≤z.im)
    (g : ℝ→ℂ) (hg : ContinuousOn g (Ici 1)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d))
    (a : ℝ→ℂ) (A : ℝ) (hA : 0≤A)
    (ha : ∀ᵐ u ∂volume.restrict (Icc (0:ℝ) 1),‖a u‖≤A) :
    ‖∫ u in Icc (0:ℝ) 1,a u*g (Real.cosh (dist (G • (u+ᵥ(H•z))) z))‖≤
      A*(C*(Real.pi*(1+averagingSublevelConstant B X Y z))) := by
  obtain ⟨hi,hbound⟩ := averaging_profile_integral_bound G H hG hH B hB hGb hHb z X Y hX hY hx hy g hg C hC hb
  calc
    _≤∫ u in Icc (0:ℝ) 1,A*‖g (Real.cosh (dist (G • (u+ᵥ(H•z))) z))‖ := by
      apply norm_integral_le_of_norm_le (hi.norm.const_mul A)
      filter_upwards [ha] with u hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hu (norm_nonneg _)
    _=A*(∫ u in Icc (0:ℝ) 1,‖g (Real.cosh (dist (G • (u+ᵥ(H•z))) z))‖) := integral_const_mul _ _
    _≤_ := mul_le_mul_of_nonneg_left hbound hA

/-- The literal squared window has an averaging error of order square-root
of the spectral parameter, with the geometric factors explicit. -/
theorem averaging_window_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ C : ℝ,0<C ∧ ∀ (R ε t : ℝ) (hR : 1≤R),0≤ε → ε≤1 → 1≤t →
      ∀ (G H : GL (Fin 2) ℝ) (_hG : G.val.det=1) (_hH : H.val.det=1)
      (B : ℝ),0<B → (∀ i j,|G.val i j|≤B) → (∀ i j,|H.val i j|≤B) →
      ∀ (z : ℍ) (X Y : ℝ),0≤X → 0<Y → |z.re|≤X → Y≤z.im →
      ∀ (a : ℝ→ℂ) (A : ℝ),0≤A →
      (∀ᵐ u ∂volume.restrict (Icc (0:ℝ) 1),‖a u‖≤A) →
      ‖∫ u in Icc (0:ℝ) 1,a u*
        windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t
          (Real.cosh (dist (G • (u+ᵥ(H•z))) z))‖≤
        A*((C*Real.sqrt t*R^2*ε^2)*(Real.pi*(1+averagingSublevelConstant B X Y z))) := by
  obtain ⟨C,hC,hbound⟩ := windowTimeSquare_abel_decay K he hc
  refine ⟨C,hC,?_⟩
  intro R ε t hR hε hε1 ht G H hG hH B hB hGb hHb z X Y hX hY hx hy a A hA ha
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  exact averaging_weighted_profile_bound G H hG hH B hB hGb hHb z X Y hX hY hx hy
    (windowSquareProfile K hc R hRp ε t)
    (windowSquareProfile_continuous K he hc R hRp ε t)
    (C*Real.sqrt t*R^2*ε^2) (by positivity)
    (fun d hd => hbound R ε t d hR hε hε1 ht hd) a A hA ha

#print axioms averaging_weighted_profile_bound
#print axioms averaging_window_bound

end QuantitativeMaass
