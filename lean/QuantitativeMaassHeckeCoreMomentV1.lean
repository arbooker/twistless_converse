module

public import QuantitativeMaassHeckeGrowingErrorV1
public import QuantitativeMaassCylinderUnitWindowTailV1
public import QuantitativeMaassCuspCoreGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeSpectralObservability
open scoped Topology FourierTransform SchwartzMap ENNReal MatrixGroups

namespace QuantitativeMaass

/-- Actual compact-core moments, uniformly in Hecke degree, smoothing scale
and cusp cutoff. The main coefficient is the checked returning-walk count. -/
theorem upperWindowKernel_unit_core_growing (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ A C D E : ℝ,0<A ∧ 0<C ∧ 0<D ∧ 1≤E ∧
      ∀ (p : ℕ) [Fact p.Prime] (R : ℝ) (hR : 0<R),1≤R →
      ∀ t H : ℝ,1≤t → 2≤H → ∀ n : ℕ,
      (∫ z in wideCompactCover N H,
        (upperWindowKernel N p K hc R hR (t-3/4) (t+3/4) n HeckeUpper.root z).re)≤
        D*t*(Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)+
        C*(heckeWordErrorGrowth p)^n*Real.sqrt t*
          Real.exp (A*R+30*Real.log (E*(H+3)^2)) := by
  obtain ⟨A,C,hA,hC,herr⟩ := upperWindowRemainder_growing_bound K he hc (I:ℍ)
  obtain ⟨D,hD,hdiag⟩ := windowIdentityContribution_unit_uniform_bound K he hc hK hm
  obtain ⟨E,hE,hcore⟩ := wideCompactCover_log_radius N hN
  let V : ℝ := (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ)*40
  have hV : 0≤V := by dsimp only [V];positivity
  refine ⟨A,C*3^40,V*D+1,E,hA,by positivity,by positivity,hE,?_⟩
  intro p _ R hR hR1 t H ht hH n
  let S := wideCompactCover N H
  let L := Real.log (E*(H+3)^2)
  let α : ℝ := (Real.sqrt (p:ℝ))⁻¹
  let w : ℝ := treeWalkCount (p+1) n 0
  let F := upperWindowRemainder N p K hc R hR (t-3/4) (t+3/4) n HeckeUpper.root
  let G := upperWindowKernel N p K hc R hR (t-3/4) (t+3/4) n HeckeUpper.root
  have hα : 0≤α := by dsimp only [α];positivity
  have hw : 0≤w := Nat.cast_nonneg _
  have hroot : 0<HeckeUpper.root.matrix.det := by norm_num [HeckeUpper.det_matrix,HeckeUpper.root_det]
  have hSc := wideCompactCover_compact N hN H
  have hLc : 0≤L := by
    apply Real.log_nonneg
    have hh : 1≤(H+3)^2 := by nlinarith only [hH]
    exact one_le_mul_of_one_le_of_one_le hE hh
  have hfc : Continuous F := upperWindowRemainder_continuous N p K he hc R hR _ _ n _ hroot
  have hfi : IntegrableOn (fun z => ‖F z‖) S := hfc.norm.continuousOn.integrableOn_compact hSc
  have hfb : IntegrableOn (fun z => ‖F z‖) (Metric.closedBall I L) :=
    hfc.norm.continuousOn.integrableOn_compact (isCompact_closedBall I L)
  have hgi : IntegrableOn (fun z => (G z).re) S :=
    (Complex.continuous_re.comp (upperWindowKernel_continuous N p K he hc R hR _ _ n _)).continuousOn.integrableOn_compact hSc
  have hci : IntegrableOn (fun _ : ℍ => α^n*w*(D*t)) S :=
    continuous_const.continuousOn.integrableOn_compact hSc
  have hpoint (z : ℍ) : (G z).re≤α^n*w*(D*t)+‖F z‖ := by
    dsimp only [G]
    rw [upperWindowKernel_split N p K hc R hR _ _ n _ hroot z,HeckeUpper.rawWalks_root_eq_tree]
    simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,←Complex.ofReal_pow,Complex.ofReal_re,
      Complex.ofReal_im,Complex.natCast_re,Complex.natCast_im,zero_mul,mul_zero,zero_add,sub_zero]
    exact add_le_add (mul_le_mul_of_nonneg_left (hdiag R hR hR1 t ht) (mul_nonneg (pow_nonneg hα _) hw))
      (Complex.re_le_norm _)
  have harea : volume.real S≤V := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (by norm_num)) (wideCompactCover_area_uniform N hN H)
    simpa only [V,S,Measure.real,ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofNat] using hh
  have hfbound : (∫ z in S,‖F z‖)≤
      (heckeWordErrorGrowth p)^n*3^40*(C*Real.sqrt t*Real.exp (A*R+30*L)) := by
    apply (setIntegral_mono_set hfb (Eventually.of_forall (fun z => norm_nonneg (F z))) (Eventually.of_forall (hcore H hH))).trans
    have hh := herr N p L R (3/4) t hR1 hLc (by norm_num) (by norm_num) ht n HeckeUpper.root hroot
    have hrh : integralMatrixHeight HeckeUpper.root.matrix=3 := by norm_num [integralMatrixHeight,HeckeUpper.matrix,HeckeUpper.root]
    rw [hrh] at hh
    apply hh.trans
    change _≤(heckeWordErrorGrowth p)^n*3^40*(C*Real.sqrt t*Real.exp (A*R+30*L))
    have hQ : 0≤heckeWordErrorGrowth p := by unfold heckeWordErrorGrowth;positivity
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤(heckeWordErrorGrowth p)^n*3^40)
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_of_le_one_right (by positivity) (by norm_num)
  calc
    _ ≤ ∫ z in S,α^n*w*(D*t)+‖F z‖ := integral_mono hgi (hci.add hfi) hpoint
    _ = α^n*w*(D*t)*volume.real S+(∫ z in S,‖F z‖) := by
      rw [integral_add hci hfi,setIntegral_const,smul_eq_mul,mul_comm (volume.real S)]
    _ ≤ α^n*w*(D*t)*V+(heckeWordErrorGrowth p)^n*3^40*(C*Real.sqrt t*Real.exp (A*R+30*L)) :=
      add_le_add (mul_le_mul_of_nonneg_left harea (by positivity)) hfbound
    _ ≤ _ := by
      apply add_le_add
      · change α^n*w*(D*t)*V≤(V*D+1)*t*α^n*w
        have hh : V*D≤V*D+1 := le_add_of_nonneg_right zero_le_one
        calc
          _ = (V*D)*t*α^n*w := by ring
          _ ≤ _ := by gcongr
      · dsimp only [L]
        exact le_of_eq (by ac_rfl)

#print axioms upperWindowKernel_unit_core_growing

end QuantitativeMaass
