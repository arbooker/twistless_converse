module

public import QuantitativeArithmeticMaassWideInputNewtonV1
public import QuantitativeArithmeticMaassFiniteColumnEnergyV1
public import QuantitativeArithmeticMaassTransferCenterSupportV1
public import QuantitativeMaassCylinderPacketKernelV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open QuantitativeNinaMaass QuantitativeHolomorphic AsymptoticClassicalPetersson
open scoped Topology SchwartzMap ContDiff
namespace QuantitativeMaass.WideInput

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b

variable {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)

/-- The actual cross-level transfer followed by the cusp and spectral
projections. Its domain is the full translation cylinder. -/
def bandTransfer (t B : ℝ) (A : AutomorphicSpace 0→L[ℂ]AutomorphicSpace N) :
    Lp ℂ 2 (quotientMeasure 0)→L[ℂ]S.band (t-B) (t+B) :=
  (S.band (t-B) (t+B)).orthogonalProjectionOnto.comp
    ((localCuspidalSpace N hN).orthogonalProjectionOnto.comp
      (A.comp cylinderAutomorphic.toContinuousLinearMap))

theorem bandTransfer_norm (t B : ℝ) (A : AutomorphicSpace 0→L[ℂ]AutomorphicSpace N) :
    ‖bandTransfer S t B A‖≤‖A‖ := by
  apply opNorm_le_bound _ (norm_nonneg A)
  intro v
  apply ((S.band (t-B) (t+B)).norm_orthogonalProjectionOnto_apply_le _).trans
  apply ((localCuspidalSpace N hN).norm_orthogonalProjectionOnto_apply_le _).trans
  change ‖A (cylinderAutomorphic v)‖≤‖A‖*‖v‖
  simpa only [cylinderAutomorphic.norm_map] using A.le_opNorm (cylinderAutomorphic v)

theorem bandTransfer_column_memLp (t B : ℝ)
    (A : AutomorphicSpace 0→L[ℂ]AutomorphicSpace N)
    (c : ℍ→Lp ℂ 2 (quotientMeasure 0))
    (hc : MemLp (fun x => A (cylinderAutomorphic (c x))) 2 (quotientMeasure 0)) :
    MemLp (fun x => bandTransfer S t B A (c x)) 2 (quotientMeasure 0) := by
  exact (hc.continuousLinearMap_comp (localCuspidalSpace N hN).orthogonalProjectionOnto).continuousLinearMap_comp (S.band (t-B) (t+B)).orthogonalProjectionOnto

/-- Compact cross localization supplies the column integrability required
by the finite-band error estimate; it is not assumed for the cylinder. -/
theorem localized_band_column_memLp (t B : ℝ)
    (F : ℝ→ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1)) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R))
    (K : Set ℍ) (hK : IsCompact K) (a b : ℝ) (ha : 0<a)
    (hheight : ∀ x∈K,a≤x.im ∧ x.im≤b)
    (v : ℍ→ℂ) (hv : AEStronglyMeasurable v (volume.restrict K))
    {C : ℝ} (hC : ∀ᵐ x ∂volume.restrict K,‖v x‖≤C) :
    MemLp (fun x => bandTransfer S t B (boundedCrossQuotientLocalization N 0 K hK v hv hC)
      (cylinderAbelColumn F hF R hR hs x)) 2 (quotientMeasure 0) :=
  bandTransfer_column_memLp S t B _ _
    (boundedCrossQuotientLocalization_column_memLp N F hF R hR hs K hK a b ha hheight v hv hC)

/-- An arbitrary finite-source error is transported to the literal cylinder
packet columns with only the packet and cross-localization operator norms. -/
theorem cylinder_column_energy {ι : Type*} [Fintype ι]
    (t B : ℝ) (A : AutomorphicSpace 0→L[ℂ]AutomorphicSpace N)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f:ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ u,star (f u)=f u)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (hc : MemLp (fun x => A (cylinderAutomorphic (cylinderTimeColumn f hf he R hR hs x)))
      2 (quotientMeasure 0))
    (b : OrthonormalBasis ι ℂ (S.band (t-B) (t+B)))
    (D : S.band (t-B) (t+B)→L[ℂ]localCuspidalSpace N hN) :
    (∫ x,‖D (bandTransfer S t B A (cylinderTimeColumn f hf he R hR hs x))‖^2 ∂quotientMeasure 0)≤
      (‖cylinderTimePacket f (f.smooth ⊤) hf‖*‖A‖)^2*finiteSourceEnergy b D := by
  have hpacket (v : Lp ℂ 2 (quotientMeasure 0)) :
      cylinderTimePacket f (f.smooth ⊤) hf v=ᵐ[quotientMeasure 0]
        (fun x => inner ℂ (cylinderTimeColumn f hf he R hR hs x) v) :=
    cylinderTimePacket_column_coeFn f (f.smooth ⊤) he hf hr R hR hs
      (evenCoshLift_support_of_time_support f R hR hs) v
  have hh := finiteSourceEnergy_transferred_column_bound (quotientMeasure 0)
    (cylinderTimePacket f (f.smooth ⊤) hf) (cylinderTimeColumn f hf he R hR hs) hpacket
    (bandTransfer S t B A) (bandTransfer_column_memLp S t B A _ hc) b D
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (finiteSourceEnergy_nonneg b D)
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul_of_nonneg_left (bandTransfer_norm S t B A) (norm_nonneg _)

variable [NeZero N] {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
  (χ : admissibleGeneratorIndex N hN → ℂ)

def newtonDefect (t B Bouter : ℝ) (n : ℕ) :
    S.band (t-B) (t+B)→L[ℂ]localCuspidalSpace N hN :=
  (Polynomial.aeval (newSignWeightedGram N hN hδ hν χ) (inverseSqrtPolynomial n)).comp
    (S.band (t-B) (t+B)).subtypeL-
  (Polynomial.aeval ((projection S t Bouter).comp (newSignWeightedGram N hN hδ hν χ))
    (inverseSqrtPolynomial n)).comp (S.band (t-B) (t+B)).subtypeL

/-- Uniform weighted Newton error on actual cylinder columns. The integral
is global on the translation cylinder. The source operator norms are
retained explicitly for the subsequent propagation schedule. -/
theorem weighted_cylinder_newton (Dinput W : ℝ) (hDi : 0≤Dinput)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ D : ℝ,Dinput≤D ∧ 0<D ∧ ∃ F : ℝ→ℝ,
      Tendsto (fun t => Real.exp (W*Strong.strongScale t)*F t/(t*ε t)) atTop (𝓝 0) ∧
      ∀ᶠ t in atTop,∀ B : ℝ,1≤B → B≤Real.exp (Dinput*Strong.strongScale t) →
        ∀ Bouter : ℝ,radius B (Real.exp (D*Strong.strongScale t))
          (inverseSqrtPolynomial (Strong.bandNewtonDepth t)).natDegree≤Bouter →
        ∀ (A : AutomorphicSpace 0→L[ℂ]AutomorphicSpace N)
          (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f:ℝ→ℂ))
          (he : Function.Even f) (_hr : ∀ u,star (f u)=f u)
          (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R),
        MemLp (fun x => A (cylinderAutomorphic (cylinderTimeColumn f hf he R hR hs x)))
          2 (quotientMeasure 0) →
        (∫ x,‖newtonDefect S hδ hν χ t B Bouter (Strong.bandNewtonDepth t)
          (bandTransfer S t B A (cylinderTimeColumn f hf he R hR hs x))‖^2 ∂quotientMeasure 0)≤
          (‖cylinderTimePacket f (f.smooth ⊤) hf‖*‖A‖)^2*F t := by
  obtain ⟨D,hDiD,hD,F,hF,hbound⟩ := weighted_newton_compression N hN S hδ hν χ
    Dinput W hDi ε hε hproduct
  refine ⟨D,hDiD,hD,F,hF,?_⟩
  filter_upwards [hbound] with t ht
  intro B hB hBi Bouter hout A f hf he hr R hR hs hc
  let b := stdOrthonormalBasis ℂ (S.band (t-B) (t+B))
  exact (cylinder_column_energy S t B A f hf he hr R hR hs hc b
    (newtonDefect S hδ hν χ t B Bouter (Strong.bandNewtonDepth t))).trans
      (mul_le_mul_of_nonneg_left (ht B hB hBi Bouter hout b) (sq_nonneg _))

#print axioms localized_band_column_memLp
#print axioms cylinder_column_energy
#print axioms weighted_cylinder_newton
end QuantitativeMaass.WideInput
