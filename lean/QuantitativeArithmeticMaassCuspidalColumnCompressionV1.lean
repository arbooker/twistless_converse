module

public import QuantitativeArithmeticMaassCrossSpectralTailV1
public import QuantitativeArithmeticMaassColumnTracePerturbationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped InnerProductSpace
namespace QuantitativeMaass

variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [MeasurableSpace α]

/-- A supported operator sees only the projected columns. No assertion
that a spatial cutoff preserves the subspace is needed. -/
theorem columnLinearTrace_supported_projection (μ : Measure α) (c : α → H)
    (P : Submodule ℂ H) [P.HasOrthogonalProjection] (T : H →L[ℂ] H)
    (hPT : P.starProjection*T=T) (hTP : T*P.starProjection=T) :
    columnLinearTrace μ c T=columnLinearTrace μ (fun x => P.starProjection (c x)) T := by
  apply integral_congr_ae
  filter_upwards with x
  have hleft : P.starProjection (T (c x))=T (c x) :=
    congrArg (fun A : H →L[ℂ] H => A (c x)) hPT
  have hright : T (P.starProjection (c x))=T (c x) :=
    congrArg (fun A : H →L[ℂ] H => A (c x)) hTP
  have hmem : T (c x) ∈ P := Submodule.starProjection_eq_self_iff.mp hleft
  have ho := inner_eq_zero_symm.mp (P.starProjection_inner_eq_zero (c x) (T (c x)) hmem)
  rw [inner_sub_right] at ho
  exact congrArg Complex.re (by rw [hright]; exact sub_eq_zero.mp ho)

/-- Compression to any closed subspace of the supported space costs only
the actual discarded column energy. In particular this applies to a finite
spectral window without assuming that the column is an eigenfunction. -/
theorem columnLinearTrace_supported_window (μ : Measure α) (c : α → H)
    (hc : MemLp c 2 μ) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (W : Submodule ℂ P) [W.HasOrthogonalProjection] (T : H →L[ℂ] H)
    (hPT : P.starProjection*T=T) (hTP : T*P.starProjection=T)
    (δ : ℝ) (hδ : 0<δ) :
    let u := fun x => P.orthogonalProjectionOnto (c x)
    let v := fun x => ((W.starProjection (u x) : P) : H)
    |columnLinearTrace μ c T-columnLinearTrace μ v T| ≤
      ‖T‖*(δ*(∫ x, ‖c x‖^2 ∂μ)+
        (1+δ⁻¹)*(∫ x, ‖u x-W.starProjection (u x)‖^2 ∂μ)) := by
  intro u v
  let cp := fun x => P.starProjection (c x)
  have hcp : MemLp cp 2 μ := hc.continuousLinearMap_comp P.starProjection
  have hu : MemLp u 2 μ := hc.continuousLinearMap_comp P.orthogonalProjectionOnto
  have hv : MemLp v 2 μ :=
    (hu.continuousLinearMap_comp W.starProjection).continuousLinearMap_comp P.subtypeL
  have hnorm (x : α) : ‖v x‖≤‖c x‖ :=
    (W.norm_starProjection_apply_le (u x)).trans (P.norm_starProjection_apply_le (c x))
  have hi : (∫ x, ‖v x‖^2 ∂μ)≤∫ x, ‖c x‖^2 ∂μ := by
    apply integral_mono
      ((memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv)
      ((memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc)
    intro x
    exact pow_le_pow_left₀ (norm_nonneg _) (hnorm x) 2
  have hdiff (x : α) : ‖cp x-v x‖=‖u x-W.starProjection (u x)‖ := rfl
  rw [columnLinearTrace_supported_projection μ c P T hPT hTP]
  have hb := columnLinearTrace_column_perturbation μ cp v hcp hv T δ hδ
  simp_rw [hdiff] at hb
  apply hb.trans
  gcongr

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

/-- The actual Lindenstrauss--Venkatesh filter satisfies the support
hypotheses in the preceding compression estimate. -/
theorem actualLVFilter_column_window_error (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ)
    (μ : Measure α) (c : α → AutomorphicSpace N) (hc : MemLp c 2 μ)
    (W : Submodule ℂ (localCuspidalSpace N hN)) [W.HasOrthogonalProjection]
    (δ : ℝ) (hδ : 0<δ) :
    let u := fun x => (localCuspidalSpace N hN).orthogonalProjectionOnto (c x)
    let v := fun x => ((W.starProjection (u x) : localCuspidalSpace N hN) : AutomorphicSpace N)
    |columnLinearTrace μ c (actualLVFilter N p hN hpN a b hab d)-
      columnLinearTrace μ v (actualLVFilter N p hN hpN a b hab d)| ≤
      δ*(∫ x, ‖c x‖^2 ∂μ)+(1+δ⁻¹)*(∫ x, ‖u x-W.starProjection (u x)‖^2 ∂μ) := by
  intro u v
  have hb := columnLinearTrace_supported_window μ c hc (localCuspidalSpace N hN) W
    (actualLVFilter N p hN hpN a b hab d)
    (localCuspidalProjection_actualLVFilter N p hN hpN hNp hpres a b hab d)
    (actualLVFilter_localCuspidalProjection N p hN hpN hNp hpres a b hab d) δ hδ
  apply hb.trans
  exact mul_le_of_le_one_left (by positivity)
    (actualLVFilter_order N p hN hpN a b hab d).2.2

#print axioms columnLinearTrace_supported_projection
#print axioms columnLinearTrace_supported_window
#print axioms actualLVFilter_column_window_error
/-- The actual LV-filtered trace of transferred cylinder packets can be
compressed to a finite spectral window, with explicit source/residual error. -/
theorem cylinderTimeColumn_supported_window_error_on_compact {ι : Type*}
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
    (S : Set ℍ) (hS : IsCompact S)
    (T : AutomorphicSpace N→L[ℂ]AutomorphicSpace N) (hT : ‖T‖≤1)
    (hPT : (localCuspidalSpace N hN).starProjection*T=T)
    (hTP : T*(localCuspidalSpace N hN).starProjection=T)
    (η : ℝ) (hη : 0<η) :
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
    |columnLinearTrace μ (fun z => A (c z)) V-columnLinearTrace μ w V| ≤
      η*(‖A‖^2*(∫ z, ‖c z‖^2 ∂μ))+
        (1+η⁻¹)*((2/L^2)*(5*a^2*(∫ z, ‖c z‖^2 ∂μ)+
          (2*a^2+2*b0^2)*(∫ z, ‖d z‖^2 ∂μ)/(1+(t^2+1/4)))) := by
  intro W inst c d A u w a b0 μ V
  let := inst
  have hcc : Continuous c := cylinderAutomorphic.continuous.comp
    (cylinderAbelColumn_continuous _ _ R hR _)
  have hc : MemLp c 2 μ :=
    (memLp_two_iff_integrable_sq_norm hcc.aestronglyMeasurable).mpr
      ((hcc.norm.pow 2).continuousOn.integrableOn_compact hS)
  have hv : MemLp (fun z => A (c z)) 2 μ := hc.continuousLinearMap_comp A
  have hi : (∫ z, ‖A (c z)‖^2 ∂μ)≤‖A‖^2*(∫ z, ‖c z‖^2 ∂μ) := by
    have hci := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc
    have hvi := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
    calc
      _ ≤ ∫ z, ‖A‖^2*‖c z‖^2 ∂μ := by
        apply integral_mono hvi (hci.const_mul _)
        intro z
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm (c z)) 2
      _ = _ := integral_const_mul _ _
  have htail := cylinderTimeColumn_cuspidal_window_tail_on_compact N hN b K hK hbK mN m0 hmN hm0
    B C hB hbound hgrad hreal basis e he hgraph f hfc hfe R hR hs t L hL ht S hS
  have hb0 := columnLinearTrace_supported_window μ (fun z => A (c z)) hv
    (localCuspidalSpace N hN) W T hPT hTP η hη
  have hb := hb0.trans (mul_le_of_le_one_left (by positivity) hT)
  apply hb.trans
  exact add_le_add (mul_le_mul_of_nonneg_left hi hη.le)
    (mul_le_mul_of_nonneg_left htail (by positivity))


theorem cylinderTimeColumn_actualLV_window_error_on_compact {ι : Type*}
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
    (S : Set ℍ) (hS : IsCompact S)
    (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (hpres : (p:ZMod N)=1) (Ap Bp : ℤ) (hAB : (p:ℤ)*Ap+(N:ℤ)*Bp=1)
    (degree : ℕ) (η : ℝ) (hη : 0<η) :
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
    |columnLinearTrace μ (fun z => A (c z)) V-columnLinearTrace μ w V| ≤
      η*(‖A‖^2*(∫ z, ‖c z‖^2 ∂μ))+
        (1+η⁻¹)*((2/L^2)*(5*a^2*(∫ z, ‖c z‖^2 ∂μ)+
          (2*a^2+2*b0^2)*(∫ z, ‖d z‖^2 ∂μ)/(1+(t^2+1/4)))) := by
  exact cylinderTimeColumn_supported_window_error_on_compact N hN b K hK hbK mN m0 hmN hm0
    B C hB hbound hgrad hreal basis e he hgraph f hfc hfe R hR hs t L hL ht S hS
    (actualLVFilter N p hN hpN Ap Bp hAB degree)
    (actualLVFilter_order N p hN hpN Ap Bp hAB degree).2.2
    (localCuspidalProjection_actualLVFilter N p hN hpN hNp hpres Ap Bp hAB degree)
    (actualLVFilter_localCuspidalProjection N p hN hpN hNp hpres Ap Bp hAB degree) η hη


theorem cylinderTimeColumn_actualLV_window_error {ι : Type*}
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
    (o : ℍ) (D : ℝ)
    (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (hpres : (p:ZMod N)=1) (Ap Bp : ℤ) (hAB : (p:ℤ)*Ap+(N:ℤ)*Bp=1)
    (degree : ℕ) (η : ℝ) (hη : 0<η) :
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
    let μ := volume.restrict (Metric.closedBall o D)
    let V := actualLVFilter N p hN hpN Ap Bp hAB degree
    |columnLinearTrace μ (fun z => A (c z)) V-columnLinearTrace μ w V| ≤
      η*(‖A‖^2*(∫ z, ‖c z‖^2 ∂μ))+
        (1+η⁻¹)*((2/L^2)*(5*a^2*(∫ z, ‖c z‖^2 ∂μ)+
          (2*a^2+2*b0^2)*(∫ z, ‖d z‖^2 ∂μ)/(1+(t^2+1/4)))) := by
  exact cylinderTimeColumn_actualLV_window_error_on_compact N hN b K hK hbK mN m0 hmN hm0 B C hB hbound hgrad hreal basis e he hgraph f hfc hfe R hR hs t L hL ht (Metric.closedBall o D) (isCompact_closedBall o D) p hpN hNp hpres Ap Bp hAB degree η hη

#print axioms cylinderTimeColumn_actualLV_window_error

end QuantitativeMaass
