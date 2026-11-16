module

public import QuantitativeMaassLVDeficitOperatorV1
public import QuantitativeMaassLocalizedEigenmomentV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeSpectralObservability
open scoped Topology InnerProductSpace ENNReal FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- A finite cuspidal family has LV deficit controlled by the positive
complementary column trace and the actual cusp tail. Constants are uniform
before the prime and both filter degrees. -/
theorem cuspidal_unit_LV_deficit_localized (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ (p : ℕ) [Fact p.Prime]
      (hpN : ¬p∣N) (_hNp : (N:ZMod p)≠0) (_hpres : (p:ZMod N)=1)
      (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
      (R : ℝ) (hR : 0<R),1≤R → (∫ x,|x|^2*K x)/(R*(1/4))^2≤1 →
      ∀ t H : ℝ,1≤t → 0<H → B*R<Real.log H → ∀ d : ℕ,
      ∀ {ι : Type*} [Fintype ι] (v : ι→AutomorphicSpace N),Orthonormal ℂ v →
      (∀ i,v i∈localCuspidalSpace N hN) → ∀ (r τ : ι→ℝ),
      (∀ i,r i∈Icc (t-1/2) (t+1/2)) →
      (∀ i,FriedrichsGraph N (v i) (((1/4+(r i)^2:ℝ):ℂ) • v i)) →
      (∀ i,actualLVDeficit N p hN hpN a b hab d (v i)=(τ i:ℂ) • v i) →
      ENNReal.ofReal ((1-(∫ x,|x|^2*K x)/(R*(1/4))^2)^2)*∑ i,ENNReal.ofReal ((τ i)^2)≤
        (∫⁻ z in wideCompactCover N H,ENNReal.ofReal
          (inner ℂ (actualLVDeficit N p hN hpN a b hab (2*d)
            (windowAbelColumn N K he hc R hR (t-3/4) (t+3/4) z))
            (windowAbelColumn N K he hc R hR (t-3/4) (t+3/4) z)).re)+
        ENNReal.ofReal (C*t/H) := by
  obtain ⟨B,C,hB,hC,hbound⟩ := cuspidal_unit_eigenmoment_localized N hN K he hc hK hm
  refine ⟨B,C,hB,hC,?_⟩
  intro p _ hpN hNp hpres a b hab R hR hR1 hmom t H ht hH hheight d ι _ v hv hcus r τ hr hgraph heigen
  have hh := hbound R hR hR1 hmom t H ht hH hheight
    (actualLVDeficit N p hN hpN a b hab d)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (actualLVDeficit_selfAdjoint N p hN hpN a b hab d))
    v hv hcus r τ hr hgraph heigen 1
  simp only [pow_one,mul_one] at hh
  apply hh.trans
  apply add_le_add
  · apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    rw [←actualLVDeficit_norm_square]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (actualLVDeficit_cusp_projection_norm N p hN hpN a b hab hNp hpres d _) 2
  · have hn := pow_le_pow_left₀ (norm_nonneg (actualLVDeficit N p hN hpN a b hab d))
      (actualLVDeficit_order N p hN hpN a b hab d).2.2 2
    simp only [one_pow] at hn
    have he : ENNReal.ofReal (‖actualLVDeficit N p hN hpN a b hab d‖^2)≤1 := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hn
    simpa only [one_mul] using mul_le_mul' he (le_refl (ENNReal.ofReal (C*t/H)))

#print axioms cuspidal_unit_LV_deficit_localized
end QuantitativeMaass
