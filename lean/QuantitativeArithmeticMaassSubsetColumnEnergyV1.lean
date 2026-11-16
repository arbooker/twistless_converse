module

public import QuantitativeArithmeticMaassColumnEnergyExponentialV1
public import QuantitativeArithmeticMaassRectangleGradientV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap ContDiff FourierTransform
namespace QuantitativeMaass

/-- The leading diagonal sees only the area of the selected centre set.
The nonidentity remainder can be bounded on an enclosing ball. -/
theorem radialIntegralKernel_subset_energy (N : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (g : ℝ→ℂ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (o : ℍ) (L D E : ℝ) (hD : 0≤D) (hd : ‖g 1‖≤D)
    (hi : IntegrableOn (radialIntegralRemainder N M hM g) (Metric.closedBall o L))
    (hb : (∫ z in Metric.closedBall o L,‖radialIntegralRemainder N M hM g z‖)≤E)
    (S : Set ℍ) (hS : S⊆Metric.closedBall o L) :
    IntegrableOn (fun z => radialPoincareKernel N g z (positiveIntegralGL M hM • z)) S ∧
    (∫ z in S,‖radialPoincareKernel N g z (positiveIntegralGL M hM • z)‖)≤volume.real S*D+E := by
  classical
  let c : ℂ := if integralIdentityCoset N M then g 1 else 0
  have hc : ‖c‖≤D := by
    dsimp only [c]
    split_ifs
    · exact hd
    · simpa using hD
  have hic : IntegrableOn (fun _z : ℍ => c) S :=
    (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall o L)).mono_set hS
  have his := hi.mono_set hS
  have hsplit (z : ℍ) : radialPoincareKernel N g z (positiveIntegralGL M hM • z)=
      c+radialIntegralRemainder N M hM g z :=
    radialIntegralKernel_identity_split N M hM g R hR hs z
  have hik := (hic.add his).congr (Eventually.of_forall (fun z => (hsplit z).symm))
  refine ⟨hik,?_⟩
  have hrem := (setIntegral_mono_set hi.norm
    (Eventually.of_forall (fun z => norm_nonneg (radialIntegralRemainder N M hM g z)))
    (Eventually.of_forall hS)).trans hb
  calc
    _≤∫ z in S,‖c‖+‖radialIntegralRemainder N M hM g z‖ := by
      apply integral_mono_ae hik.norm (hic.norm.add his.norm)
      filter_upwards with z
      rw [hsplit]
      exact norm_add_le _ _
    _=volume.real S*‖c‖+∫ z in S,‖radialIntegralRemainder N M hM g z‖ := by
      rw [integral_add hic.norm his.norm]
      simp [measureReal_def]
    _≤_ := add_le_add (mul_le_mul_of_nonneg_left hc measureReal_nonneg) hrem

/-- Local source energy with a sharp area factor on the O(t epsilon)
diagonal and only a square-root-t remainder. This applies to thin collars. -/
theorem windowSourceColumn_subset_energy (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ) :
    ∃ A B D : ℝ,0<A ∧ 0<B ∧ 0<D ∧ ∀ (L R t ε : ℝ) (hR : 1≤R),
      0≤L → 1≤t → 0≤ε → ε≤1 → 1/R≤ε →
      let f := windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) t (t+ε)
      ∀ Rout : ℝ,∀ hOut : 0≤Rout,∀ hs : Function.support f⊆Icc (-Rout) Rout,
      ∀ S : Set ℍ,S⊆Metric.closedBall o L →
      (∫ z in S,‖cylinderTimeColumn f
        (symmetricWindowTimeTest_compact K hc R t (t+ε) (lt_of_lt_of_le zero_lt_one hR))
        (symmetricWindowTimeTest_even K he R t (t+ε)) Rout hOut hs z‖^2)≤
        volume.real S*(D*t*ε)+B*(Real.sqrt t*ε^2)*Real.exp (A*(R+L)) := by
  obtain ⟨U,hU,hsupp⟩ := symmetricWindowTimeTest_uniform_support K hc
  obtain ⟨C,hC,hdecay⟩ := oneSidedWindowSquare_abel_decay K he hc
  obtain ⟨D,hD,hdiag⟩ := windowIdentityContribution_resolved_bound K he hc hK hm
  obtain ⟨A,B,hA,hB,hgeom⟩ := column_geometry_exponential o U C 1 hU hC zero_lt_one
  refine ⟨A,B,D,hA,hB,hD,?_⟩
  intro L R t ε hR hL ht he0 he1 hresolve f Rout hOut hs S hS
  let g := abelProfile (evenCoshLift (timeConvolution f f))
  have hfc : HasCompactSupport (f:ℝ→ℂ) := symmetricWindowTimeTest_compact K hc R t (t+ε) (lt_of_lt_of_le zero_lt_one hR)
  have hfe : Function.Even f := symmetricWindowTimeTest_even K he R t (t+ε)
  have hfr : ∀ s,star (f s)=f s := symmetricWindowTimeTest_real K he R t (t+ε)
  have hg : ContinuousOn g (Ici 1) := evenTime_abel_continuous _
    ((timeConvolution f f).smooth ⊤) (timeConvolution_even f f hfe hfe)
    (timeConvolution_compact f f hfc hfc)
  have hfs := hsupp R (lt_of_lt_of_le zero_lt_one hR) t (t+ε)
  have hgs : Function.support g⊆Iic (Real.cosh (2*(U*R))) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity)
      (by simpa only [two_mul] using timeConvolution_support f f (U*R) (U*R) hfs hfs))
  have hId : 0<(1:Matrix (Fin 2) (Fin 2) ℤ).det := by simp
  have hact (z : ℍ) : positiveIntegralGL 1 hId • z=z := by
    apply UpperHalfPlane.ext
    rw [positiveIntegralGL_fractional]
    simp
  have hentry : ∀ i j : Fin 2,|((1:Matrix (Fin 2) (Fin 2) ℤ) i j:ℝ)|≤1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  obtain ⟨hi,hrem⟩ := radialIntegralRemainder_all_integral_bound 0 1 hId 1 (by norm_num)
    hentry o L (2*(U*R)) (by positivity) g hg hgs (C*Real.sqrt t*R^2*ε^2)
    (by positivity) (fun d hd => hdecay R ε t d hR he0 he1 ht hd)
  simp only [hact,dist_self,add_zero,mul_one] at hrem
  obtain ⟨hki,hbound⟩ := radialIntegralKernel_subset_energy 0 1 hId g (2*(U*R))
    (by positivity) hgs o L (D*t*ε) _ (by positivity)
    (hdiag R t ε hR ht he0 he1 hresolve) hi hrem S hS
  simp only [hact] at hki hbound
  have hgeo := hgeom L R (Real.sqrt t*ε^2) hL (by linarith) (by positivity)
  have hrem' : (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (2*(U*R)+2*L):ℝ)*
      (C*Real.sqrt t*R^2*ε^2)*(Real.pi*(volume.real (Metric.closedBall o L)+
        hyperbolicSublevelConstant o L (2*(U*R)+2*L+2*Real.log 2)))≤
      B*(Real.sqrt t*ε^2)*Real.exp (A*(R+L)) := by
    have hnon : 0≤volume.real (Metric.closedBall o L)*(1*(Real.sqrt t*ε^2)) := by positivity
    nlinarith only [hgeo,hnon]
  calc
    _=∫ z in S,(radialPoincareKernel 0 g z z).re := by
      apply integral_congr_ae
      filter_upwards with z
      rw [←inner_self_eq_norm_sq (𝕜:=ℂ),cylinderTimeSquare_kernel_cross f hfc hfe hfr Rout hOut hs]
      rfl
    _≤∫ z in S,‖radialPoincareKernel 0 g z z‖ :=
      integral_mono_ae hki.re hki.norm (Eventually.of_forall (fun _ => Complex.re_le_norm _))
    _≤_ := hbound.trans (add_le_add le_rfl hrem')

#print axioms radialIntegralKernel_subset_energy
#print axioms windowSourceColumn_subset_energy
end QuantitativeMaass
