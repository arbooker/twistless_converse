module

public import QuantitativeMaassCuspidalWideTailV1
public import QuantitativeMaassCylinderUnitWindowTailV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson QuantitativeArithmeticMaassCuspBand
open scoped Topology MatrixGroups SchwartzMap FourierTransform ENNReal

namespace QuantitativeMaass

/-- The actual cusp-projected unit-window column has O_N(t/H) energy
on each full cusp strip, uniformly in the cusp and smoothing scale. -/
theorem cuspidal_window_column_unit_tail (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ (R : ℝ) (hR : 0<R),1≤R →
      ∀ (t : ℝ),1≤t → ∀ (A : SL(2,ℤ)) (H : ℝ),0<H → B*R<Real.log H →
      (∫⁻ z in cuspTailSet N H,ENNReal.ofReal
        (‖localCuspidalProjection N hN
          (windowAbelColumn N K he hc R hR (t-3/4) (t+3/4) (cuspAction A z))‖^2))≤
        ENNReal.ofReal (C*t/H) := by
  obtain ⟨B,hB,hbound⟩ := cuspidal_window_column_sharp_tail K he hc
  obtain ⟨C,hC,hdiag⟩ := windowIdentityContribution_unit_uniform_bound K he hc hK hm
  refine ⟨B,2*(N:ℝ)^2*C,hB,by have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN;positivity,?_⟩
  intro R hR hR1 t ht A H hH hheight
  have hd := hdiag R hR hR1 t ht
  change (windowTimeSquareProfile K hc R hR (t-3/4) (t+3/4) 1).re≤C*t at hd
  have hcard : (Fintype.card (cuspAdmissibleResidues N A):ℝ)≤(N:ℝ) := by
    exact_mod_cast (show Fintype.card (cuspAdmissibleResidues N A)≤N from
      (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin N))
  calc
    _≤ENNReal.ofReal (2*(Fintype.card (cuspAdmissibleResidues N A):ℝ))*
        ((N:ℝ≥0∞)*(ENNReal.ofReal H⁻¹*ENNReal.ofReal
          (windowTimeSquareProfile K hc R hR (t-3/4) (t+3/4) 1).re)) :=
      hbound N hN R hR _ _ A H hH hheight
    _≤ENNReal.ofReal (2*(Fintype.card (cuspAdmissibleResidues N A):ℝ))*
        ((N:ℝ≥0∞)*(ENNReal.ofReal H⁻¹*ENNReal.ofReal (C*t))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hd)))
    _≤_ := by
      rw [←ENNReal.ofReal_mul (inv_nonneg.mpr hH.le),←ENNReal.ofReal_natCast N,
        ←ENNReal.ofReal_mul (Nat.cast_nonneg N),←ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      calc
        _≤(2*(N:ℝ))*((N:ℝ)*(H⁻¹*(C*t))) := by gcongr
        _=_ := by ring

#print axioms cuspidal_window_column_unit_tail

end QuantitativeMaass
