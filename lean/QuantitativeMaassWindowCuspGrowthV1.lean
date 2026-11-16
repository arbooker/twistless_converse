module

public import QuantitativeMaassCuspGeometricGrowthV1
public import QuantitativeMaassCuspCoverIntegralV1
public import QuantitativeMaassIntegratedWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped Topology MatrixGroups FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- Uniform growing-propagation remainder bound on every actual truncated
cusp chart, with an explicit exponential dependence on the radius. -/
theorem windowGeometricRemainder_exp_cusp_integral (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ A₀ C : ℝ,0<A₀ ∧ 0<C ∧ ∀ R : ℝ,∀ hR : 1≤R,
      ∀ (N : ℕ) (A : SL(2,ℤ)) (ε t H : ℝ),
      0≤ε → ε≤1 → 1≤t → (1:ℝ)/4≤H →
      (∫ z in QuantitativeSpectralObservability.wideBox H,
        ‖windowGeometricRemainder N K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) (A•z)‖)≤
        C*Real.sqrt t*ε^2*Real.exp (A₀*R)*(1+Real.sqrt H) := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  obtain ⟨C,hC,hbound⟩ := windowTimeSquare_abel_decay K he hc
  obtain ⟨D,hD,hgeom⟩ := radialNonidentity_cusp_truncation_exp
  refine ⟨80*B+2,D*C,by positivity,by positivity,?_⟩
  intro R hR N A ε t H hε hε1 ht hH
  let f := windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)
  have hfs : Function.support (f : ℝ → ℂ)⊆Icc (-(B*R)) (B*R) := by
    change Function.support (symmetricWindowTimeTest K R (t-ε) (t+ε))⊆_
    exact hs R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)
  have hgs : Function.support (timeConvolution f f : ℝ → ℂ)⊆Icc (-(2*(B*R))) (2*(B*R)) := by
    simpa only [two_mul] using timeConvolution_support f f (B*R) (B*R) hfs hfs
  have hps : Function.support (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t)⊆Iic (Real.cosh (2*(B*R))) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity) hgs)
  have hp : ∀ d : ℝ,0<d → ‖windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t (Real.cosh d)‖≤
      (C*Real.sqrt t*R^2*ε^2)/Real.sqrt (Real.sinh d) := by
    intro d hd
    dsimp only [windowSquareProfile]
    exact hbound R ε t d hR hε hε1 ht hd
  have hh := hgeom (2*(B*R)) (by positivity) N A (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t)
    (windowSquareProfile_continuous K he hc R (lt_of_lt_of_le zero_lt_one hR) ε t) hps
    (C*Real.sqrt t*R^2*ε^2) (by positivity) hp H hH
  apply hh.trans
  calc
    _ = D*C*Real.sqrt t*ε^2*(R^2*Real.exp ((80*B)*R))*(1+Real.sqrt H) := by
      rw [show 40*(2*(B*R))=(80*B)*R from by ring]
      ring
    _ ≤ D*C*Real.sqrt t*ε^2*Real.exp ((80*B+2)*R)*(1+Real.sqrt H) := by
      gcongr
      exact radius_square_exp_le (80*B) R (by linarith)

/-- The same uniform estimate on the full raw compact reduction core. -/
theorem windowGeometricRemainder_exp_core_integral (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ A C : ℝ,0<A ∧ 0<C ∧ ∀ R : ℝ,∀ hR : 1≤R,∀ N : ℕ,0<N →
      ∀ ε t H : ℝ,0≤ε → ε≤1 → 1≤t → (1:ℝ)/4≤H →
      (∫ z in QuantitativeSpectralObservability.wideCompactCover N H,
        ‖windowGeometricRemainder N K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z‖)≤
        (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ)*
          (C*Real.sqrt t*ε^2*Real.exp (A*R)*(1+Real.sqrt H)) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := windowGeometricRemainder_exp_cusp_integral K he hc
  refine ⟨A,C,hA,hC,?_⟩
  intro R hR N hN ε t H hε hε1 ht hH
  exact wideCompactCover_integral_bound N hN H _
    (windowGeometricRemainder_continuous N K he hc R _ (t-ε) (t+ε)).norm
    (fun z => norm_nonneg _) _ (by positivity)
    (fun S => hbound R hR N S ε t H hε hε1 ht hH)

#print axioms windowGeometricRemainder_exp_cusp_integral
#print axioms windowGeometricRemainder_exp_core_integral

end QuantitativeMaass
