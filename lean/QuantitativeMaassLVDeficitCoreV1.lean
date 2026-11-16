module

public import QuantitativeMaassVolumeDeficitUpperV1
public import QuantitativeMaassHeckeCoreMomentV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeSpectralObservability
open scoped Topology FourierTransform SchwartzMap ENNReal MatrixGroups
namespace QuantitativeMaass

/-- The positive LV deficit on the actual compact core has a spherical
inverse-square-root main bound, uniformly in the degree and cusp cutoff. -/
theorem actualLVDeficit_unit_core_upper (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ A C D E : ℝ,0<A ∧ 0<C ∧ 0<D ∧ 1≤E ∧
      ∀ (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N) (_hNp : (N:ZMod p)≠0)
      (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
      (R : ℝ) (hR : 0<R),1≤R → ∀ t H : ℝ,2≤t → 2≤H →
      ∀ d : ℕ,0<d →
      windowVolumeOperatorTrace N K he hc R hR (t-3/4) (t+3/4)
        (wideCompactCover N H) (actualLVDeficit N p hN hpN a b hab d)≤
      D*t*lvSphericalDeficit p d+C*Real.sqrt t*
        Real.exp (A*R+30*Real.log (E*(H+3)^2)+
          (2+2*max 1 (heckeWordErrorGrowth p)+22*|Real.log p|)*(d:ℝ)) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := actualLVDeficit_volume_trace_upper K he hc hK hm (I:ℍ)
  obtain ⟨D,hD,hdiag⟩ := windowIdentityContribution_unit_uniform_bound K he hc hK hm
  obtain ⟨E,hE,hcore⟩ := wideCompactCover_log_radius N hN
  let V : ℝ := (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ)*40
  have hV : 0≤V := by dsimp only [V];positivity
  refine ⟨A,C,V*D+1,E,hA,hC,by positivity,hE,?_⟩
  intro p _ hpN hNp a b hab R hR hR1 t H ht hH d hd
  let S := wideCompactCover N H
  let L := Real.log (E*(H+3)^2)
  have hL : 0≤L := by
    apply Real.log_nonneg
    exact one_le_mul_of_one_le_of_one_le hE (by nlinarith only [hH])
  have harea : volume.real S≤V := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (by norm_num))
      (wideCompactCover_area_uniform N hN H)
    simpa only [V,S,Measure.real,ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofNat] using hh
  have hδ : 0≤lvSphericalDeficit p d :=
    (finitePlaceSymbol_deficit_bounds p d hd 0).1.trans (finitePlaceSymbol_deficit_bounds p d hd 0).2
  have hh := hbound N p hN hpN hNp a b hab L R (3/4) t hR1 hL
    (by norm_num) (by norm_num) ht S (wideCompactCover_compact N hN H) (hcore H hH) d hd
  apply hh.trans
  apply add_le_add
  · calc
      _ ≤ volume.real S*lvSphericalDeficit p d*(D*t) :=
        mul_le_mul_of_nonneg_left (hdiag R hR hR1 t (by linarith))
          (mul_nonneg (measureReal_nonneg (μ:=volume) (s:=S)) hδ)
      _ ≤ V*lvSphericalDeficit p d*(D*t) := by gcongr
      _ ≤ (V*D+1)*t*lvSphericalDeficit p d := by
        nlinarith only [mul_nonneg (show 0≤t by linarith) hδ]
  · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_of_le_one_right (by positivity) (by norm_num)

#print axioms actualLVDeficit_unit_core_upper
end QuantitativeMaass
