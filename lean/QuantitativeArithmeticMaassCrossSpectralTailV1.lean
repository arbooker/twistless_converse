module

public import QuantitativeArithmeticMaassResidualColumnLeakageV1
public import QuantitativeMaassCuspidalCutoffTailV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ContDiff InnerProductSpace

namespace QuantitativeMaass

/-- The actual residual estimate extends to infinite orthonormal families;
summability follows from the finite-subfamily bound. -/
theorem crossQuotientLocalization_residual_tsum {ι : Type*}
    (N M : ℕ) (b : SmoothUpperSeed) (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N), (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M), (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ mM)
    (B C : ℝ) (hB : 0≤B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖≤B)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re≤C^2)
    (hreal : ∀ Z, star (b.toFun Z)=b.toFun Z)
    (r : ι → ℝ) (μ : ℝ) (f : ι → AutomorphicSpace N)
    (g d : AutomorphicSpace M) (hf : Orthonormal ℂ f)
    (hr : ∀ i, 0≤r i) (hμ : 0≤μ)
    (hgraph : ∀ i, FriedrichsGraph N (f i) ((r i : ℂ) • f i))
    (hg : FriedrichsGraph M g ((μ : ℂ) • g+d)) (L : ℝ) (hL : 0<L)
    (hsep : ∀ i, L≤|Real.sqrt (1+r i)-Real.sqrt (1+μ)|) :
    Summable (fun i => ‖inner ℂ (f i) (crossQuotientLocalization N M K hK b hbound g)‖^2) ∧
    (∑' i, ‖inner ℂ (f i) (crossQuotientLocalization N M K hK b hbound g)‖^2) ≤
      (2/L^2)*(5*(2*Real.sqrt (mN : ℝ)*|C| *Real.sqrt (mM : ℝ))^2*‖g‖^2+
        (2*(2*Real.sqrt (mN : ℝ)*|C| *Real.sqrt (mM : ℝ))^2+
          2*(Real.sqrt (mN : ℝ)*B*Real.sqrt (mM : ℝ))^2)*‖d‖^2/(1+μ)) := by
  classical
  have hfinite (S : Finset ι) :
      (∑ i ∈ S, ‖inner ℂ (f i) (crossQuotientLocalization N M K hK b hbound g)‖^2) ≤
      (2/L^2)*(5*(2*Real.sqrt (mN : ℝ)*|C| *Real.sqrt (mM : ℝ))^2*‖g‖^2+
        (2*(2*Real.sqrt (mN : ℝ)*|C| *Real.sqrt (mM : ℝ))^2+
          2*(Real.sqrt (mN : ℝ)*B*Real.sqrt (mM : ℝ))^2)*‖d‖^2/(1+μ)) := by
    rw [←Finset.sum_coe_sort]
    exact crossQuotientLocalization_residual_L2_bound N M b K hK hbK mN mM hmN hmM
      B C hB hbound hgrad hreal (fun i : S => r i) μ (fun i : S => f i) g d
      (hf.comp Subtype.val Subtype.val_injective) (fun i => hr i) hμ
      (fun i => hgraph i) hg L hL (fun i => hsep i)
  have hs := summable_of_sum_le (fun _ => sq_nonneg _) hfinite
  exact ⟨hs,hs.tsum_le_of_sum_le hfinite⟩

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

/-- Residual control gives leakage of the actual projected transferred
vector outside a finite principal spectral window. The source may be the
continuous-spectrum cylinder and need not have a discrete spectral basis. -/
theorem crossQuotientLocalization_cuspidal_wide_tail {ι : Type*}
    (N : ℕ) (hN : 0<N) (M : ℕ) (b : SmoothUpperSeed)
    (K : Set ℍ) (hK : IsCompact K) (hbK : tsupport (upperFunction b.toFun) ⊆ K)
    (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N), (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M), (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ mM)
    (B C : ℝ) (hB : 0≤B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖≤B)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re≤C^2)
    (hreal : ∀ Z, star (b.toFun Z)=b.toFun Z)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι → ℝ)
    (he : ∀ i, 0≤e i)
    (hgraph : ∀ i, FriedrichsGraph N (basis i : AutomorphicSpace N)
      ((e i : ℂ) • (basis i : AutomorphicSpace N)))
    (g d : AutomorphicSpace M) (μ : ℝ) (hμ : 0≤μ)
    (hg : FriedrichsGraph M g ((μ : ℂ) • g+d))
    (t L : ℝ) (hL : 0<L) (ht : L+3≤t)
    (hin : |Real.sqrt (μ-1/4)-t|≤1) :
    let W := cuspPrincipalWindowSpace N hN basis e (t-(L+3)) (t+(L+3))
    let : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional
      N hN basis e he hgraph (t-(L+3)) (t+(L+3))
    let u := (localCuspidalSpace N hN).orthogonalProjectionOnto
      (crossQuotientLocalization N M K hK b hbound g)
    ‖u-W.starProjection u‖^2 ≤
      (2/L^2)*(5*(2*Real.sqrt (mN : ℝ)*|C| *Real.sqrt (mM : ℝ))^2*‖g‖^2+
        (2*(2*Real.sqrt (mN : ℝ)*|C| *Real.sqrt (mM : ℝ))^2+
          2*(Real.sqrt (mN : ℝ)*B*Real.sqrt (mM : ℝ))^2)*‖d‖^2/(1+μ)) := by
  classical
  dsimp only
  let S := principalWindowIndices e (t-(L+3)) (t+(L+3))
  let W := cuspPrincipalWindowSpace N hN basis e (t-(L+3)) (t+(L+3))
  let : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional
    N hN basis e he hgraph (t-(L+3)) (t+(L+3))
  rw [hilbertBasis_projection_tail basis S]
  simp_rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have ho := basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  apply (crossQuotientLocalization_residual_tsum N M b K hK hbK mN mM hmN hmM B C hB
    hbound hgrad hreal (fun i : {i // i∉S} => e i.val) μ
    (fun i : {i // i∉S} => (basis i.val : AutomorphicSpace N)) g d
    (ho.comp Subtype.val Subtype.val_injective) (fun i => he i.val) hμ
    (fun i => hgraph i.val) hg L hL _).2
  intro i
  exact outside_wide_band_energy_separation (e i.val) μ t L (he i.val) hμ hin
    (Weighted.outside_principal_window_distance e t L ht i.val i.property)


/-- Integrated spectral leakage of the actual cylinder packet after a
smooth cross-quotient transfer and cuspidal projection. Both right-hand
energies have already been estimated for the one-sided window packet. -/
theorem cylinderTimeColumn_cuspidal_window_tail_on_compact {ι : Type*}
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
    (S : Set ℍ) (hS : IsCompact S) :
    let W := cuspPrincipalWindowSpace N hN basis e (t-(L+3)) (t+(L+3))
    let : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional
      N hN basis e he hgraph (t-(L+3)) (t+(L+3))
    let c := fun z => cylinderAutomorphic (cylinderTimeColumn f hfc hfe R hR hs z)
    let d := fun z => cylinderAutomorphic (cylinderTimeColumn (spectralResidualSchwartz t f)
      (spectralResidualSchwartz_compact t f hfc) (spectralResidualSchwartz_even t f hfe)
      R hR (spectralTimeResidual_support t f R hs) z)
    let A := crossQuotientLocalization N 0 K hK b hbound
    let u := fun z => (localCuspidalSpace N hN).orthogonalProjectionOnto (A (c z))
    let a := 2*Real.sqrt (mN : ℝ)*|C| *Real.sqrt (m0 : ℝ)
    let b0 := Real.sqrt (mN : ℝ)*B*Real.sqrt (m0 : ℝ)
    (∫ z in S, ‖u z-W.starProjection (u z)‖^2) ≤
      (2/L^2)*(5*a^2*(∫ z in S, ‖c z‖^2)+
        (2*a^2+2*b0^2)*(∫ z in S, ‖d z‖^2)/(1+(t^2+1/4))) := by
  intro W inst c d A u a b0
  let := inst
  have hcc : Continuous c := cylinderAutomorphic.continuous.comp
    (cylinderAbelColumn_continuous _ _ R hR _)
  have hdc : Continuous d := cylinderAutomorphic.continuous.comp
    (cylinderAbelColumn_continuous _ _ R hR _)
  have huc : Continuous u := (localCuspidalSpace N hN).orthogonalProjectionOnto.continuous.comp
    (A.continuous.comp hcc)
  have hic : IntegrableOn (fun z => ‖c z‖^2) S :=
    (hcc.norm.pow 2).continuousOn.integrableOn_compact hS
  have hid : IntegrableOn (fun z => ‖d z‖^2) S :=
    (hdc.norm.pow 2).continuousOn.integrableOn_compact hS
  have hil : IntegrableOn (fun z => ‖u z-W.starProjection (u z)‖^2) S :=
    ((huc.sub (W.starProjection.continuous.comp huc)).norm.pow 2).continuousOn.integrableOn_compact
      hS
  have hfreq : |Real.sqrt ((t^2+1/4)-1/4)-t|≤1 := by
    rw [add_sub_cancel_right,Real.sqrt_sq (by linarith : 0≤t)]
    simp
  have hp (z : ℍ) : ‖u z-W.starProjection (u z)‖^2 ≤
      (2/L^2)*(5*a^2*‖c z‖^2+(2*a^2+2*b0^2)*‖d z‖^2/(1+(t^2+1/4))) :=
    crossQuotientLocalization_cuspidal_wide_tail N hN 0 b K hK hbK mN m0 hmN hm0
      B C hB hbound hgrad hreal basis e he hgraph (c z) (d z) (t^2+1/4) (by positivity)
      (cylinderTimeColumn_spectralResidual_graph f hfc hfe R hR hs z t) t L hL ht hfreq
  calc
    _ ≤ ∫ z in S,
        (2/L^2)*(5*a^2*‖c z‖^2+(2*a^2+2*b0^2)*‖d z‖^2/(1+(t^2+1/4))) :=
      integral_mono_ae hil
        (((hic.const_mul _).add ((hid.const_mul _).div_const _)).const_mul _)
        (Eventually.of_forall hp)
    _ = _ := by
      rw [integral_const_mul,integral_add (hic.const_mul _)
        ((hid.const_mul _).div_const _),integral_const_mul,integral_div,integral_const_mul]


theorem cylinderTimeColumn_cuspidal_window_tail {ι : Type*}
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
    (o : ℍ) (D : ℝ) :
    let W := cuspPrincipalWindowSpace N hN basis e (t-(L+3)) (t+(L+3))
    let : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional
      N hN basis e he hgraph (t-(L+3)) (t+(L+3))
    let c := fun z => cylinderAutomorphic (cylinderTimeColumn f hfc hfe R hR hs z)
    let d := fun z => cylinderAutomorphic (cylinderTimeColumn (spectralResidualSchwartz t f)
      (spectralResidualSchwartz_compact t f hfc) (spectralResidualSchwartz_even t f hfe)
      R hR (spectralTimeResidual_support t f R hs) z)
    let A := crossQuotientLocalization N 0 K hK b hbound
    let u := fun z => (localCuspidalSpace N hN).orthogonalProjectionOnto (A (c z))
    let a := 2*Real.sqrt (mN : ℝ)*|C| *Real.sqrt (m0 : ℝ)
    let b0 := Real.sqrt (mN : ℝ)*B*Real.sqrt (m0 : ℝ)
    (∫ z in Metric.closedBall o D, ‖u z-W.starProjection (u z)‖^2) ≤
      (2/L^2)*(5*a^2*(∫ z in Metric.closedBall o D, ‖c z‖^2)+
        (2*a^2+2*b0^2)*(∫ z in Metric.closedBall o D, ‖d z‖^2)/(1+(t^2+1/4))) := by
  exact cylinderTimeColumn_cuspidal_window_tail_on_compact N hN b K hK hbK mN m0 hmN hm0 B C hB hbound hgrad hreal basis e he hgraph f hfc hfe R hR hs t L hL ht (Metric.closedBall o D) (isCompact_closedBall o D)

#print axioms cylinderTimeColumn_cuspidal_window_tail
#print axioms crossQuotientLocalization_residual_tsum
#print axioms crossQuotientLocalization_cuspidal_wide_tail

end QuantitativeMaass
