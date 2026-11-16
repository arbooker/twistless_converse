module

public import QuantitativeArithmeticMaassSourceColumnEnergyV1
public import QuantitativeMaassCorrespondenceWindowV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeArithmeticMaassOverlap
open scoped Topology ContDiff FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- The support radius affects the proof of square integrability, not the
actual Hilbert-space column. -/
theorem cylinderTimeColumn_radius_eq (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f:ℝ→ℂ)) (he : Function.Even f)
    (R S : ℝ) (hR : 0≤R) (hS : 0≤S)
    (hr : Function.support f⊆Icc (-R) R) (hs : Function.support f⊆Icc (-S) S) :
    cylinderTimeColumn f hc he R hR hr=cylinderTimeColumn f hc he S hS hs := rfl

/-- All orbit and area terms in the finite-center column bound have one
exponential cost in the propagation and center radii. -/
theorem column_geometry_exponential (o : ℍ) (U C D : ℝ)
    (hU : 0<U) (hC : 0<C) (hD : 0<D) :
    ∃ A B : ℝ,0<A ∧ 0<B ∧ ∀ L R M : ℝ,0≤L → 0≤R → 0≤M →
      volume.real (Metric.closedBall o L)*(D*M)+
      (energyMultiplicity o 0 (2*(U*R)+2*L):ℝ)*(C*M*R^2)*
        (Real.pi*(volume.real (Metric.closedBall o L)+
          hyperbolicSublevelConstant o L (2*(U*R)+2*L+2*Real.log 2)))≤
      B*M*Real.exp (A*(R+L)) := by
  obtain ⟨G,hG,hgeom⟩ := correspondence_geometry_exp o 0 (2*Real.log 2)
    (by norm_num) (by positivity)
  refine ⟨20*U+32,Real.pi*D+C*G,by positivity,by positivity,?_⟩
  intro L R M hL hR hM
  have hg := hgeom L (2*(U*R)+2*L) hL (by positivity)
  simp only [add_zero] at hg
  have hr : R≤Real.exp R := by linarith [Real.add_one_le_exp R]
  have hr2 : R^2≤Real.exp (2*R) := by
    calc
      R^2 ≤ (Real.exp R)^2 := pow_le_pow_left₀ hR hr 2
      _ = Real.exp (2*R) := by rw [show 2*R=R+R by ring, Real.exp_add]; ring
  have he1 : Real.exp (4*L)≤Real.exp ((20*U+32)*(R+L)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hU.le hR,mul_nonneg hU.le hL]
  have he2 : Real.exp (2*R+10*(2*(U*R)+2*L+L))≤Real.exp ((20*U+32)*(R+L)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hU.le hL]
  have hmain : volume.real (Metric.closedBall o L)*(D*M)≤
      (Real.pi*D)*M*Real.exp ((20*U+32)*(R+L)) := by
    calc
      _ ≤ (Real.pi*Real.exp (4*L))*(D*M) :=
        mul_le_mul_of_nonneg_right (centre_ball_volume_exp o L) (by positivity)
      _ ≤ (Real.pi*Real.exp ((20*U+32)*(R+L)))*(D*M) := by gcongr
      _ = _ := by ring
  have hrem : (energyMultiplicity o 0 (2*(U*R)+2*L):ℝ)*(C*M*R^2)*
      (Real.pi*(volume.real (Metric.closedBall o L)+
        hyperbolicSublevelConstant o L (2*(U*R)+2*L+2*Real.log 2)))≤
      (C*G)*M*Real.exp ((20*U+32)*(R+L)) := by
    calc
      _ = (C*M*R^2)*((energyMultiplicity o 0 (2*(U*R)+2*L):ℝ)*
        (Real.pi*(volume.real (Metric.closedBall o L)+
          hyperbolicSublevelConstant o L (2*(U*R)+2*L+2*Real.log 2)))) := by ring
      _ ≤ (C*M*R^2)*(G*Real.exp (10*(2*(U*R)+2*L+L))) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      _ ≤ (C*M*Real.exp (2*R))*(G*Real.exp (10*(2*(U*R)+2*L+L))) := by gcongr
      _ = (C*G)*M*Real.exp (2*R+10*(2*(U*R)+2*L+L)) := by rw [Real.exp_add]; ring
      _ ≤ _ := by gcongr
  nlinarith only [hmain,hrem]

/-- Actual source column energy, uniform in both growing geometric radii.
No global cylinder Hilbert--Schmidt assumption is made. -/
theorem windowSourceColumn_exponential_energy (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ) :
    ∃ A B : ℝ,0<A ∧ 0<B ∧ ∀ (L R t ε : ℝ) (hR : 1≤R),
      0≤L → 1≤t → 0≤ε → ε≤1 → 1/R≤ε →
      let f := windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) t (t+ε)
      ∀ Rout : ℝ,∀ hOut : 0≤Rout,∀ hs : Function.support f⊆Icc (-Rout) Rout,
      (∫ z in Metric.closedBall o L,‖cylinderTimeColumn f
        (symmetricWindowTimeTest_compact K hc R t (t+ε) (lt_of_lt_of_le zero_lt_one hR))
        (symmetricWindowTimeTest_even K he R t (t+ε)) Rout hOut hs z‖^2)≤
        B*(t*ε)*Real.exp (A*(R+L)) := by
  obtain ⟨U,C,D,hU,hC,hD,henergy⟩ := windowSourceColumn_integrated_energy K he hc hK hm
  obtain ⟨A,B,hA,hB,hgeom⟩ := column_geometry_exponential o U C D hU hC hD
  refine ⟨A,B,hA,hB,?_⟩
  intro L R t ε hR hL ht he0 he1 hresolve f Rout hOut hs
  obtain ⟨hs0,hbound⟩ := henergy o L R t ε hR ht he0 he1 hresolve
  have ht0 : 0≤t := by linarith
  have hroot : Real.sqrt t≤t := by
    nlinarith [Real.sq_sqrt ht0,Real.sqrt_nonneg t]
  have hε2 : ε^2≤ε := by nlinarith
  apply hbound.trans
  apply le_trans _ (hgeom L R (t*ε) hL (by linarith) (by positivity))
  refine add_le_add (le_of_eq (by ring)) ?_
  apply mul_le_mul_of_nonneg_right _
    (mul_nonneg Real.pi_pos.le (add_nonneg (measureReal_nonneg) (hyperbolicSublevelConstant_nonneg _ _ _)))
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    C*Real.sqrt t*R^2*ε^2 ≤ C*t*R^2*ε := by gcongr
    _ = C*(t*ε)*R^2 := by ring

/-- The same exponential cost controls the actual residual column after
factoring out t^3 epsilon, as required by the off-band flux inequality. -/
theorem windowResidualColumn_exponential_energy (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ) :
    ∃ A B : ℝ,0<A ∧ 0<B ∧ ∀ (L R t ε : ℝ) (hR : 1≤R),
      0≤L → 1≤t → 0≤ε → ε≤1 →
      let f := windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) t (t+ε)
      ∀ Rout : ℝ,∀ hOut : 0≤Rout,∀ hs : Function.support f⊆Icc (-Rout) Rout,
      (∫ z in Metric.closedBall o L,
        ‖cylinderTimeColumn (spectralResidualSchwartz t f)
          (spectralResidualSchwartz_compact t f
            (symmetricWindowTimeTest_compact K hc R t (t+ε) (lt_of_lt_of_le zero_lt_one hR)))
          (spectralResidualSchwartz_even t f (symmetricWindowTimeTest_even K he R t (t+ε)))
          Rout hOut (spectralTimeResidual_support t f Rout hs) z‖^2)≤
        B*(t^3*ε)*Real.exp (A*(R+L)) := by
  obtain ⟨U,C,hU,hC,henergy⟩ := windowResidualColumn_integrated_energy K he hc hK hm
  let D := 576*(1+∫ x,|x|^5*K x)/(4*Real.pi)
  have hD : 0<D := by
    have hmoment : 0≤∫ x,|x|^5*K x := integral_nonneg (fun x => mul_nonneg (pow_nonneg (abs_nonneg _) _) (hK x))
    dsimp [D]
    positivity
  obtain ⟨A,B,hA,hB,hgeom⟩ := column_geometry_exponential o U C D hU hC hD
  refine ⟨A,B,hA,hB,?_⟩
  intro L R t ε hR hL ht he0 he1 f Rout hOut hs
  obtain ⟨hs0,hbound⟩ := henergy o L R t ε hR ht he0 he1
  have ht0 : 0≤t := by linarith
  have hroot : Real.sqrt t≤t := by
    nlinarith [Real.sq_sqrt ht0,Real.sqrt_nonneg t]
  have hε2 : ε^2≤ε := by nlinarith
  apply hbound.trans
  apply le_trans _ (hgeom L R (t^3*ε) hL (by linarith) (by positivity))
  apply add_le_add
  · apply le_of_eq
    ring
  · apply mul_le_mul_of_nonneg_right _
      (mul_nonneg Real.pi_pos.le (add_nonneg (measureReal_nonneg) (hyperbolicSublevelConstant_nonneg _ _ _)))
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc
      C*t^2*Real.sqrt t*R^2*ε^2 ≤ C*t^2*t*R^2*ε := by gcongr
      _ = C*(t^3*ε)*R^2 := by ring

#print axioms cylinderTimeColumn_radius_eq
#print axioms column_geometry_exponential
#print axioms windowSourceColumn_exponential_energy
#print axioms windowResidualColumn_exponential_energy
end QuantitativeMaass
