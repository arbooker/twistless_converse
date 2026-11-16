module

public import QuantitativeMaassCuspCoverIntegralV1
public import QuantitativeMaassWindowRawColumnV1
public import QuantitativeMaassUnitWindowIdentityV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeSpectralObservability
open scoped Topology MatrixGroups InnerProductSpace ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- The actual enlarged-unit-window column energy on a linearly growing
cuspidal core is O(t). No spectral count or trace estimate is assumed. -/
theorem windowAbelColumn_unit_core_energy (N : ℕ) (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 1≤R) (D : ℝ) (hD : 2≤D) :
    letI : NeZero N := ⟨hN.ne'⟩
    ∃ C : ℝ,0<C ∧ ∀ t : ℝ,1≤t →
      (∫ z in wideCompactCover N (D*t),
        ‖windowAbelColumn N K he hc R (lt_of_lt_of_le zero_lt_one hR) (t-3/4) (t+3/4) z‖^2)≤C*t := by
  let : NeZero N := ⟨hN.ne'⟩
  let hRp := lt_of_lt_of_le zero_lt_one hR
  let n : ℝ := Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  have hn : 0≤n := Nat.cast_nonneg _
  obtain ⟨A,hA,hid⟩ := windowIdentityContribution_unit_bound K he hc hK hm R hRp
  obtain ⟨B,hB,hgeo⟩ := windowGeometricRemainder_fixedRadius_core_integral K he hc R hR
  refine ⟨n*(40*A+B*(1+Real.sqrt D))+1,by positivity,?_⟩
  intro t ht
  let S := wideCompactCover N (D*t)
  let g := windowGeometricRemainder N K hc R hRp (t-3/4) (t+3/4)
  let c := windowAbelColumn N K he hc R hRp (t-3/4) (t+3/4)
  have hSc := wideCompactCover_compact N hN (D*t)
  have hi : IntegrableOn (fun z => ‖c z‖^2) S volume :=
    ((windowAbelColumn_continuous N K he hc R hRp (t-3/4) (t+3/4)).norm.pow 2).continuousOn.integrableOn_compact hSc
  have hg : IntegrableOn (fun z => ‖g z‖) S volume :=
    (windowGeometricRemainder_continuous N K he hc R hRp (t-3/4) (t+3/4)).norm.continuousOn.integrableOn_compact hSc
  have hconst : IntegrableOn (fun _ : ℍ => A*t) S volume :=
    continuous_const.continuousOn.integrableOn_compact hSc
  have hpoint (z : ℍ) : ‖c z‖^2≤A*t+‖g z‖ := by
    rw [windowAbelColumn_norm_square N K he hc R hRp (t-3/4) (t+3/4)]
    exact add_le_add (hid t ht) (Complex.re_le_norm _)
  have harea : volume.real S≤n*40 := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (by norm_num)) (wideCompactCover_area_uniform N hN (D*t))
    change (volume (wideCompactCover N (D*t))).toReal≤(Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ)*40
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofNat] using hh
  have hroot : Real.sqrt t*(1+Real.sqrt (D*t))≤(1+Real.sqrt D)*t := by
    have ht0 : 0≤t := by linarith
    rw [Real.sqrt_mul (by linarith : 0≤D)]
    calc
      _ = Real.sqrt t+Real.sqrt D*(Real.sqrt t)^2 := by ring
      _ = Real.sqrt t+Real.sqrt D*t := by rw [Real.sq_sqrt ht0]
      _ ≤ t+Real.sqrt D*t := add_le_add (show Real.sqrt t≤t by nlinarith [Real.sq_sqrt ht0,Real.sqrt_nonneg t]) le_rfl
      _ = _ := by ring
  have hroot' : Real.sqrt t*(3/4:ℝ)^2*(1+Real.sqrt (D*t))≤(1+Real.sqrt D)*t := by
    calc
      _ ≤ Real.sqrt t*(1+Real.sqrt (D*t)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [Real.sqrt_nonneg t]
      _ ≤ _ := hroot
  have hgb : (∫ z in S,‖g z‖)≤n*B*(1+Real.sqrt D)*t := by
    have hh := hgeo N hN (3/4) t (D*t) (by norm_num) (by norm_num) ht (by nlinarith)
    calc
      _ ≤ n*(B*Real.sqrt t*(3/4:ℝ)^2*(1+Real.sqrt (D*t))) := hh
      _ = (n*B)*(Real.sqrt t*(3/4:ℝ)^2*(1+Real.sqrt (D*t))) := by ring
      _ ≤ (n*B)*((1+Real.sqrt D)*t) := mul_le_mul_of_nonneg_left hroot' (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∫ z in S,A*t+‖g z‖ := integral_mono_ae hi (hconst.add hg) (Eventually.of_forall hpoint)
    _ = A*t*volume.real S+∫ z in S,‖g z‖ := by
      rw [integral_add hconst hg,setIntegral_const,smul_eq_mul,mul_comm (volume.real S)]
    _ ≤ A*t*(n*40)+n*B*(1+Real.sqrt D)*t :=
      add_le_add (mul_le_mul_of_nonneg_left harea (by positivity)) hgb
    _ ≤ _ := by nlinarith

#print axioms windowAbelColumn_unit_core_energy

end QuantitativeMaass
