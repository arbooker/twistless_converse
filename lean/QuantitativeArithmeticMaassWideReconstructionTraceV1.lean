module

public import QuantitativeArithmeticMaassScheduledCylinderNewtonV1
public import QuantitativeArithmeticMaassColumnTracePerturbationV1
public import QuantitativeMaassNewSignReconstructionTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open QuantitativeNinaMaass QuantitativeHolomorphic AsymptoticClassicalPetersson
open scoped Topology SchwartzMap
namespace QuantitativeMaass.WideInput

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b

variable {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
  {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
  (χ : admissibleGeneratorIndex N hN → ℂ)

/-- Ambient Newton reconstruction from an arbitrary input spectral band. -/
def ambientReconstruction (t B : ℝ) (n : ℕ) :
    S.band (t-B) (t+B)→L[ℂ]Lp ℂ 2 (quotientMeasure 0) :=
  (newSignExtendedWeightedEmbedding N hN hδ hν χ).comp
    ((Polynomial.aeval (newSignWeightedGram N hN hδ hν χ) (inverseSqrtPolynomial n)).comp
      (S.band (t-B) (t+B)).subtypeL)

/-- Newton reconstruction using one fixed outer compression. -/
def bandReconstruction (t B Bouter : ℝ) (n : ℕ) :
    S.band (t-B) (t+B)→L[ℂ]Lp ℂ 2 (quotientMeasure 0) :=
  (polynomialNormalizedReconstruction
    ((newSignExtendedWeightedEmbedding N hN hδ hν χ).comp
      (S.band (t-Bouter) (t+Bouter)).subtypeL) n).comp
    ((S.band (t-Bouter) (t+Bouter)).orthogonalProjectionOnto.comp
      (S.band (t-B) (t+B)).subtypeL)

theorem ambientReconstruction_norm (t B : ℝ) (n : ℕ) :
    ‖ambientReconstruction S hδ hν χ t B n‖≤1 := by
  have hn := polynomialNormalizedReconstruction_norm_le
    (newSignExtendedWeightedEmbedding N hN hδ hν χ)
    (newSignExtendedWeightedEmbedding_norm N hN hδ hν χ) n
  apply opNorm_le_bound _ zero_le_one
  intro x
  have hh := (polynomialNormalizedReconstruction (newSignExtendedWeightedEmbedding N hN hδ hν χ) n).le_of_opNorm_le hn x.val
  simp only [polynomialNormalizedReconstruction,newSignExtendedWeightedEmbedding_gram,
    comp_apply,one_mul] at hh ⊢
  exact hh

theorem bandReconstruction_norm (t B Bouter : ℝ) (n : ℕ) :
    ‖bandReconstruction S hδ hν χ t B Bouter n‖≤1 := by
  let K := S.band (t-Bouter) (t+Bouter)
  let R := (newSignExtendedWeightedEmbedding N hN hδ hν χ).comp K.subtypeL
  have hR : ‖R‖≤1 := by
    apply opNorm_le_bound _ zero_le_one
    intro x
    exact (newSignExtendedWeightedEmbedding N hN hδ hν χ).le_of_opNorm_le
      (newSignExtendedWeightedEmbedding_norm N hN hδ hν χ) x.val
  have hn := polynomialNormalizedReconstruction_norm_le R hR n
  apply opNorm_le_bound _ zero_le_one
  intro x
  have hh := (polynomialNormalizedReconstruction R n).le_of_opNorm_le hn (K.orthogonalProjectionOnto x.val)
  simp only [one_mul] at hh ⊢
  exact hh.trans (K.norm_orthogonalProjectionOnto_apply_le x.val)

theorem bandReconstruction_eq (t B Bouter : ℝ) (hB : B≤Bouter) (n : ℕ) :
    bandReconstruction S hδ hν χ t B Bouter n=
      (newSignExtendedWeightedEmbedding N hN hδ hν χ).comp
        ((Polynomial.aeval ((projection S t Bouter).comp
          (newSignWeightedGram N hN hδ hν χ)) (inverseSqrtPolynomial n)).comp
            (S.band (t-B) (t+B)).subtypeL) := by
  symm
  rw [←newSignExtendedWeightedEmbedding_gram N hN hδ hν χ]
  apply embedding_subspace_newton
  intro x
  exact cuspEnergyBand_mono S (by linarith : t-Bouter≤t-B)
    (by linarith : t+B≤t+Bouter) x.property

/-- The reconstruction error is the already controlled Gram error followed
by a contraction; no inverse of the Gram on the full cusp space is used. -/
theorem reconstruction_sub (t B Bouter : ℝ) (hB : B≤Bouter) (n : ℕ) :
    ambientReconstruction S hδ hν χ t B n-bandReconstruction S hδ hν χ t B Bouter n=
      (newSignExtendedWeightedEmbedding N hN hδ hν χ).comp
        (newtonDefect S hδ hν χ t B Bouter n) := by
  rw [bandReconstruction_eq S hδ hν χ t B Bouter hB n]
  exact (comp_sub _ _ _).symm

omit [NeZero N] in
/-- Crude mass bound needed only in the tunable trace inequality. Unlike
an error estimate, this may retain the input spectral dimension. -/
theorem contraction_column_mass {ι : Type*} [Fintype ι]
    (t B : ℝ) (A : AutomorphicSpace 0→L[ℂ]AutomorphicSpace N)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f:ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ u,star (f u)=f u)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (hc : MemLp (fun x => A (cylinderAutomorphic (cylinderTimeColumn f hf he R hR hs x)))
      2 (quotientMeasure 0))
    (b : OrthonormalBasis ι ℂ (S.band (t-B) (t+B)))
    (D : S.band (t-B) (t+B)→L[ℂ]Lp ℂ 2 (quotientMeasure 0)) (hD : ‖D‖≤1) :
    (∫ x,‖D (bandTransfer S t B A (cylinderTimeColumn f hf he R hR hs x))‖^2 ∂quotientMeasure 0)≤
      (‖cylinderTimePacket f (f.smooth ⊤) hf‖*‖A‖)^2*(Fintype.card ι:ℝ) := by
  have hpacket (v : Lp ℂ 2 (quotientMeasure 0)) :
      cylinderTimePacket f (f.smooth ⊤) hf v=ᵐ[quotientMeasure 0]
        (fun x => inner ℂ (cylinderTimeColumn f hf he R hR hs x) v) :=
    cylinderTimePacket_column_coeFn f (f.smooth ⊤) he hf hr R hR hs
      (evenCoshLift_support_of_time_support f R hR hs) v
  have hh := finiteSourceEnergy_transferred_column_bound (quotientMeasure 0)
    (cylinderTimePacket f (f.smooth ⊤) hf) (cylinderTimeColumn f hf he R hR hs) hpacket
    (bandTransfer S t B A) (bandTransfer_column_memLp S t B A _ hc) b D
  have hb : finiteSourceEnergy b D≤(Fintype.card ι:ℝ) := by
    calc
      _ ≤ ∑ _ : ι,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi : ‖D (b i)‖≤1 := by
          simpa only [b.orthonormal.norm_eq_one i,one_mul] using D.le_of_opNorm_le hD (b i)
        nlinarith [norm_nonneg (D (b i))]
      _ = _ := by simp
  apply hh.trans
  apply mul_le_mul
  · apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left (bandTransfer_norm S t B A) (norm_nonneg _)
  · exact hb
  · exact finiteSourceEnergy_nonneg b D
  · positivity

/-- Ordered trace comparison for the actual cylinder columns and arbitrary
output operator. In particular no commutation with an LV filter is needed. -/
theorem reconstruction_column_trace (t B Bouter : ℝ) (hB : B≤Bouter) (n : ℕ)
    (A : AutomorphicSpace 0→L[ℂ]AutomorphicSpace N)
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport (f:ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ u,star (f u)=f u)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (hc : MemLp (fun x => A (cylinderAutomorphic (cylinderTimeColumn f hf he R hR hs x)))
      2 (quotientMeasure 0))
    (T : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
    (η : ℝ) (hη : 0<η) :
    |columnLinearTrace (quotientMeasure 0)
      (fun x => ambientReconstruction S hδ hν χ t B n
        (bandTransfer S t B A (cylinderTimeColumn f hf he R hR hs x))) T-
      columnLinearTrace (quotientMeasure 0)
      (fun x => bandReconstruction S hδ hν χ t B Bouter n
        (bandTransfer S t B A (cylinderTimeColumn f hf he R hR hs x))) T|≤
      ‖T‖*(η*((‖cylinderTimePacket f (f.smooth ⊤) hf‖*‖A‖)^2*
        (Module.finrank ℂ (S.band (t-B) (t+B)):ℝ))+
        (1+η⁻¹)*(∫ x,‖newtonDefect S hδ hν χ t B Bouter n
          (bandTransfer S t B A (cylinderTimeColumn f hf he R hR hs x))‖^2 ∂quotientMeasure 0)) := by
  let c := fun x => bandTransfer S t B A (cylinderTimeColumn f hf he R hR hs x)
  have hm : MemLp c 2 (quotientMeasure 0) := bandTransfer_column_memLp S t B A _ hc
  have hh := columnLinearTrace_column_perturbation (quotientMeasure 0)
    (fun x => ambientReconstruction S hδ hν χ t B n (c x))
    (fun x => bandReconstruction S hδ hν χ t B Bouter n (c x))
    (hm.continuousLinearMap_comp _) (hm.continuousLinearMap_comp _) T η hη
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (le_of_lt hη)
    simpa only [Fintype.card_fin] using contraction_column_mass S t B A f hf he hr R hR hs hc
      (stdOrthonormalBasis ℂ (S.band (t-B) (t+B)))
      (bandReconstruction S hδ hν χ t B Bouter n)
      (bandReconstruction_norm S hδ hν χ t B Bouter n)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply integral_mono
    · exact (memLp_two_iff_integrable_sq_norm
        ((hm.continuousLinearMap_comp _).sub (hm.continuousLinearMap_comp _)).aestronglyMeasurable).mp
        ((hm.continuousLinearMap_comp _).sub (hm.continuousLinearMap_comp _))
    · exact (memLp_two_iff_integrable_sq_norm (hm.continuousLinearMap_comp
        (newtonDefect S hδ hν χ t B Bouter n)).aestronglyMeasurable).mp
        (hm.continuousLinearMap_comp (newtonDefect S hδ hν χ t B Bouter n))
    · intro x
      have hx := DFunLike.congr_fun (reconstruction_sub S hδ hν χ t B Bouter hB n) (c x)
      change ambientReconstruction S hδ hν χ t B n (c x)-
        bandReconstruction S hδ hν χ t B Bouter n (c x)=
          newSignExtendedWeightedEmbedding N hN hδ hν χ
            (newtonDefect S hδ hν χ t B Bouter n (c x)) at hx
      change ‖ambientReconstruction S hδ hν χ t B n (c x)-
        bandReconstruction S hδ hν χ t B Bouter n (c x)‖^2≤
          ‖newtonDefect S hδ hν χ t B Bouter n (c x)‖^2
      rw [hx]
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [one_mul] using
        (newSignExtendedWeightedEmbedding N hN hδ hν χ).le_of_opNorm_le
          (newSignExtendedWeightedEmbedding_norm N hN hδ hν χ) _

#print axioms ambientReconstruction_norm
#print axioms bandReconstruction_norm
#print axioms reconstruction_sub
#print axioms contraction_column_mass
#print axioms reconstruction_column_trace
end QuantitativeMaass.WideInput
