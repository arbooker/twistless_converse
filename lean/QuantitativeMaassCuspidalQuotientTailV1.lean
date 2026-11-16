module

public import QuantitativeMaassOrbitCuspCoverV1
public import QuantitativeMaassCuspidalUnitTailV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand QuantitativeSpectralObservability
open scoped Topology ENNReal MatrixGroups FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- The actual cusp-projected packet has O_N(t/H) quotient energy outside
the orbit-saturated compact core, uniformly in the smoothing scale. -/
theorem cuspidal_window_column_quotient_unit_tail (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ (R : ℝ) (hR : 0<R),1≤R →
      ∀ (t H : ℝ),1≤t → 0<H → B*R<Real.log H →
      (∫⁻ z in (orbitCore N (wideCompactCover N H))ᶜ,ENNReal.ofReal
        (‖localCuspidalProjection N hN
          (windowAbelColumn N K he hc R hR (t-3/4) (t+3/4) z)‖^2) ∂quotientMeasure N)≤
        ENNReal.ofReal (C*t/H) := by
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  obtain ⟨B,C,hB,hC,hbound⟩ := cuspidal_window_column_unit_tail N hN K he hc hK hm
  refine ⟨B,2*(Fintype.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ)*C,hB,by positivity,?_⟩
  intro R hR hR1 t H ht hH hheight
  let F := fun z : ℍ => ENNReal.ofReal (‖localCuspidalProjection N hN
    (windowAbelColumn N K he hc R hR (t-3/4) (t+3/4) z)‖^2)
  have hF : Measurable F :=
    (((localCuspidalProjection N hN).continuous.comp
      (windowAbelColumn_continuous N K he hc R hR _ _)).norm.pow 2).measurable.ennreal_ofReal
  have hFi : ∀ g : gamma N,∀ z,F (g.val•z)=F z := by
    intro g z
    exact congrArg (fun v => ENNReal.ofReal (‖localCuspidalProjection N hN v‖^2))
      (windowAbelColumn_invariant N K he hc R hR (t-3/4) (t+3/4) g z)
  apply (quotient_orbitCore_compl_cusps N hN H F hF hFi).trans
  calc
    _≤∑' _q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,∑' _b : Bool,ENNReal.ofReal (C*t/H) := by
      apply ENNReal.tsum_le_tsum
      intro q
      apply ENNReal.tsum_le_tsum
      intro b
      exact hbound R hR hR1 t ht (globalCuspChart N q b) H hH hheight
    _=_ := by
      simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_bool,nsmul_eq_mul]
      norm_num only [Nat.cast_ofNat]
      rw [←ENNReal.ofReal_natCast (Fintype.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N))]
      rw [show (2:ℝ≥0∞)=ENNReal.ofReal (2:ℝ) by norm_num,
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),←ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

#print axioms cuspidal_window_column_quotient_unit_tail

end QuantitativeMaass
