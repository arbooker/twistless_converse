module

public import QuantitativeArithmeticMaassCuspidalColumnCompressionV1
public import QuantitativeArithmeticMaassTransferCenterSupportV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
namespace QuantitativeMaass
local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

/-- Full-cylinder LV trace compression, with all source and residual costs
confined to the explicit propagated compact rectangle. The centre restriction
has been removed using actual finite propagation. -/
theorem cylinderTimeColumn_supported_global_window_error {ι : Type*}
    (N : ℕ) (hN : 0<N) (b : SmoothUpperSeed)
    (K : Set ℍ) (hK : IsCompact K) (hbK : tsupport (upperFunction b.toFun) ⊆ K)
    (mN m0 : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N), (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ mN)
    (hm0 : ∀ z : ℍ, ∀ S : Finset (gamma 0), (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ m0)
    (B C : ℝ) (hB : 0≤B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖≤B)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re≤C^2)
    (hreal : ∀ Z, star (b.toFun Z)=b.toFun Z)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι → ℝ)
    (he : ∀ i, 0≤e i)
    (hgraph : ∀ i, FriedrichsGraph N (basis i : AutomorphicSpace N)
      ((e i : ℂ) • (basis i : AutomorphicSpace N)))
    (f : SchwartzMap ℝ ℂ) (hfc : HasCompactSupport (f : ℝ → ℂ))
    (hfe : Function.Even f) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f ⊆ Icc (-R) R) (t L : ℝ) (hL : 0<L) (ht : L+3≤t)
    (lo hi : ℝ) (hlo : 0<lo)
    (hheight : ∀ x∈K, lo≤x.im ∧ x.im≤hi)
    (T : AutomorphicSpace N→L[ℂ]AutomorphicSpace N) (hT : ‖T‖≤1)
    (hPT : (localCuspidalSpace N hN).starProjection*T=T)
    (hTP : T*(localCuspidalSpace N hN).starProjection=T)
    (η : ℝ) (hη : 0<η) :
    let S := upperRectangle 0 1 (lo*Real.exp (-R)) (hi*Real.exp R)
    let W := cuspPrincipalWindowSpace N hN basis e (t-(L+3)) (t+(L+3))
    let : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional
      N hN basis e he hgraph (t-(L+3)) (t+(L+3))
    let c := fun z => cylinderAutomorphic (cylinderTimeColumn f hfc hfe R hR hs z)
    let d := fun z => cylinderAutomorphic (cylinderTimeColumn (spectralResidualSchwartz t f)
      (spectralResidualSchwartz_compact t f hfc) (spectralResidualSchwartz_even t f hfe)
      R hR (spectralTimeResidual_support t f R hs) z)
    let A := crossQuotientLocalization N 0 K hK b hbound
    let u := fun z => (localCuspidalSpace N hN).orthogonalProjectionOnto (A (c z))
    let w := fun z => ((W.starProjection (u z) : localCuspidalSpace N hN) : AutomorphicSpace N)
    let a := 2*Real.sqrt (mN : ℝ)*|C| *Real.sqrt (m0 : ℝ)
    let b0 := Real.sqrt (mN : ℝ)*B*Real.sqrt (m0 : ℝ)
    let μ := volume.restrict S
    let V := T
    |columnLinearTrace (quotientMeasure 0) (fun z => A (c z)) V-
      columnLinearTrace (quotientMeasure 0) w V| ≤
      η*(‖A‖^2*(∫ z, ‖c z‖^2 ∂μ))+
        (1+η⁻¹)*((2/L^2)*(5*a^2*(∫ z, ‖c z‖^2 ∂μ)+
          (2*a^2+2*b0^2)*(∫ z, ‖d z‖^2 ∂μ)/(1+(t^2+1/4)))) := by
  intro S W inst c d A u w a b0 μ V
  let := inst
  have hS : IsCompact S := upperRectangle_compact 0 1 _ _ (mul_pos hlo (Real.exp_pos _))
  have hb := cylinderTimeColumn_supported_window_error_on_compact N hN b K hK hbK mN m0 hmN hm0
    B C hB hbound hgrad hreal basis e he hgraph f hfc hfe R hR hs t L hL ht S hS
    T hT hPT hTP η hη
  have hboundAE : ∀ᵐ z ∂volume.restrict K, ‖upperFunction b.toFun z‖≤B := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact hbound z hz
  have hid (Φ : AutomorphicSpace N → ℝ) (hΦ : Φ 0=0) :
      (∫ z, Φ (A (c z)) ∂quotientMeasure 0)=∫ z, Φ (A (c z)) ∂μ :=
    boundedCrossQuotientLocalization_column_integral N (evenCoshLift f)
      (evenCoshLift_smoothOn f (f.smooth ⊤) hfe hfc) R hR
      (evenCoshLift_support_of_time_support f R hR hs) K hK lo hi hlo hheight
      (upperFunction b.toFun) (upperFunction_continuous b.smooth).aestronglyMeasurable
      hboundAE Φ hΦ
  have hleft : columnLinearTrace (quotientMeasure 0) (fun z => A (c z)) V=
      columnLinearTrace μ (fun z => A (c z)) V :=
    hid (fun y => (inner ℂ (V y) y).re) (by simp)
  let J := (localCuspidalSpace N hN).subtypeL.comp
    (W.starProjection.comp (localCuspidalSpace N hN).orthogonalProjectionOnto)
  have hright : columnLinearTrace (quotientMeasure 0) w V=columnLinearTrace μ w V :=
    hid (fun y => (inner ℂ (V (J y)) (J y)).re) (by simp)
  rw [hleft,hright]
  exact hb


theorem cylinderTimeColumn_actualLV_global_window_error {ι : Type*}
    (N : ℕ) (hN : 0<N) (b : SmoothUpperSeed)
    (K : Set ℍ) (hK : IsCompact K) (hbK : tsupport (upperFunction b.toFun) ⊆ K)
    (mN m0 : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N), (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ mN)
    (hm0 : ∀ z : ℍ, ∀ S : Finset (gamma 0), (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ m0)
    (B C : ℝ) (hB : 0≤B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖≤B)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re≤C^2)
    (hreal : ∀ Z, star (b.toFun Z)=b.toFun Z)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι → ℝ)
    (he : ∀ i, 0≤e i)
    (hgraph : ∀ i, FriedrichsGraph N (basis i : AutomorphicSpace N)
      ((e i : ℂ) • (basis i : AutomorphicSpace N)))
    (f : SchwartzMap ℝ ℂ) (hfc : HasCompactSupport (f : ℝ → ℂ))
    (hfe : Function.Even f) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f ⊆ Icc (-R) R) (t L : ℝ) (hL : 0<L) (ht : L+3≤t)
    (lo hi : ℝ) (hlo : 0<lo)
    (hheight : ∀ x∈K, lo≤x.im ∧ x.im≤hi)
    (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (hpres : (p:ZMod N)=1) (Ap Bp : ℤ) (hAB : (p:ℤ)*Ap+(N:ℤ)*Bp=1)
    (degree : ℕ) (η : ℝ) (hη : 0<η) :
    let S := upperRectangle 0 1 (lo*Real.exp (-R)) (hi*Real.exp R)
    let W := cuspPrincipalWindowSpace N hN basis e (t-(L+3)) (t+(L+3))
    let : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional
      N hN basis e he hgraph (t-(L+3)) (t+(L+3))
    let c := fun z => cylinderAutomorphic (cylinderTimeColumn f hfc hfe R hR hs z)
    let d := fun z => cylinderAutomorphic (cylinderTimeColumn (spectralResidualSchwartz t f)
      (spectralResidualSchwartz_compact t f hfc) (spectralResidualSchwartz_even t f hfe)
      R hR (spectralTimeResidual_support t f R hs) z)
    let A := crossQuotientLocalization N 0 K hK b hbound
    let u := fun z => (localCuspidalSpace N hN).orthogonalProjectionOnto (A (c z))
    let w := fun z => ((W.starProjection (u z) : localCuspidalSpace N hN) : AutomorphicSpace N)
    let a := 2*Real.sqrt (mN : ℝ)*|C| *Real.sqrt (m0 : ℝ)
    let b0 := Real.sqrt (mN : ℝ)*B*Real.sqrt (m0 : ℝ)
    let μ := volume.restrict S
    let V := actualLVFilter N p hN hpN Ap Bp hAB degree
    |columnLinearTrace (quotientMeasure 0) (fun z => A (c z)) V-
      columnLinearTrace (quotientMeasure 0) w V| ≤
      η*(‖A‖^2*(∫ z, ‖c z‖^2 ∂μ))+
        (1+η⁻¹)*((2/L^2)*(5*a^2*(∫ z, ‖c z‖^2 ∂μ)+
          (2*a^2+2*b0^2)*(∫ z, ‖d z‖^2 ∂μ)/(1+(t^2+1/4)))) := by
  exact cylinderTimeColumn_supported_global_window_error N hN b K hK hbK mN m0 hmN hm0
    B C hB hbound hgrad hreal basis e he hgraph f hfc hfe R hR hs t L hL ht lo hi hlo hheight
    (actualLVFilter N p hN hpN Ap Bp hAB degree)
    (actualLVFilter_order N p hN hpN Ap Bp hAB degree).2.2
    (localCuspidalProjection_actualLVFilter N p hN hpN hNp hpres Ap Bp hAB degree)
    (actualLVFilter_localCuspidalProjection N p hN hpN hNp hpres Ap Bp hAB degree) η hη

#print axioms cylinderTimeColumn_actualLV_global_window_error
end QuantitativeMaass
