module

public import QuantitativeNinaMaassJointOperatorsV1
public import QuantitativeNinaMaassEulerConstructionV1
public import QuantitativeNinaMaassNewCountV1
public import QuantitativeConcreteGoalsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory QuantitativeMaass
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology

/-!
The lower-bound map uses the actual simultaneous new-parity eigenfamily.
Its coefficients are the proved normalized Fourier amplitudes. The finite
subset conclusion does not require finiteness of the full solution set;
the ncard corollary states that separate upper-bound obligation explicitly.
Compiler status, exact hashes and immutable audits are recorded in Nina's
collaboration reports.
-/

namespace QuantitativeNinaMaass

/-- Equality of normalized coefficients forces actual spectral vectors
to be proportional. Both normalizing constants are proved nonzero. -/
theorem actual_coefficients_proportional (N : ℕ) (hN : 0 < N) (r : ℝ)
    (f g : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hg : Continuous g.val) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hcf : AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN)
    (hcg : AutomorphicL2.denseEmbedding _ _ g ∈ localCuspidalSpace N hN)
    (s : ℂ)
    (hsf : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
      s • AutomorphicL2.denseEmbedding _ _ f)
    (hsg : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ g) =
      s • AutomorphicL2.denseEmbedding _ _ g)
    (hef : FriedrichsGraph N (AutomorphicL2.denseEmbedding _ _ f)
      (((1 / 4 + r ^ 2 : ℝ) : ℂ) • AutomorphicL2.denseEmbedding _ _ f))
    (heg : FriedrichsGraph N (AutomorphicL2.denseEmbedding _ _ g)
      (((1 / 4 + r ^ 2 : ℝ) : ℂ) • AutomorphicL2.denseEmbedding _ _ g))
    (ell eta : ℕ → ℂ)
    (hrf : PrimeHeightEigenrelations N ell (actualHeightCoefficients f.val))
    (hrg : PrimeHeightEigenrelations N eta (actualHeightCoefficients g.val))
    (he : canonicalEulerCoefficients N ell = canonicalEulerCoefficients N eta) :
    ∃ c d : ℂ, c ≠ 0 ∧ d ≠ 0 ∧
      c • AutomorphicL2.denseEmbedding _ _ f = d • AutomorphicL2.denseEmbedding _ _ g := by
  obtain ⟨C, hC, hF⟩ := actual_nonzero_bessel_amplitude N hN f hf hf0 hcf s hsf r hef ell hrf
  obtain ⟨D, hD, hG⟩ := actual_nonzero_bessel_amplitude N hN g hg hg0 hcg s hsg r heg eta hrg
  obtain ⟨hnF, hrF, hcF⟩ := normalize_actual_bessel_amplitude N r ell f hrf C hC hF
  obtain ⟨hnG, hrG, hcG⟩ := normalize_actual_bessel_amplitude N r eta g hrg D hD hG
  have hc (u : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
      (hu : AutomorphicL2.denseEmbedding _ _ u ∈ localCuspidalSpace N hN) (a : ℂ) :
      AutomorphicL2.denseEmbedding _ _ (a • u) ∈ localCuspidalSpace N hN := by
    rw [map_smul]
    exact (localCuspidalSpace N hN).smul_mem a hu
  have hs (u : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
      (hu : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ u) =
        s • AutomorphicL2.denseEmbedding _ _ u) (a : ℂ) :
      reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ (a • u)) =
        s • AutomorphicL2.denseEmbedding _ _ (a • u) := by
    simp only [map_smul, hu, smul_smul, mul_comm a]
  have h := normalized_physical_amplitudes_separate N hN r (C⁻¹ • f) (D⁻¹ • g)
    (continuous_const.mul hf) (continuous_const.mul hg) (hc f hcf _) (hc g hcg _)
    s (hs f hsf _) (hs g hsg _) ell eta hrF hrG hnF hnG (hcF.trans (he.trans hcG.symm))
  refine ⟨C⁻¹, D⁻¹, inv_ne_zero hC, inv_ne_zero hD, ?_⟩
  simpa only [map_smul] using congrArg
    (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N)) h

namespace CuspEnergySpectrum

theorem exists_new_band_euler_family {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b : ℝ) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) :
    ∃ q : Fin (Module.finrank ℂ (S.partialParityBand a b ((-1 : ℝ) ^ δ) univ)) →
        ℝ × (ℕ → ℂ), Function.Injective q ∧ ∀ j,
      0 ≤ (q j).1 ∧ (q j).1 ∈ Icc a b ∧
        MaassOriginal.IsEulerSolution N (.principal (q j).1) δ (q j).2 := by
  let σ : ℝ := (-1) ^ δ
  have hσ : σ ^ 2 = 1 := by rcases hδ with rfl | rfl <;> norm_num [σ]
  obtain ⟨v, hv, he⟩ := S.exists_full_new_eigenfamily a b σ hσ
  choose r hr hwin χ hχ heigen hfr ell hell using he
  let f j := S.newBandRepresentative a b σ (v j)
  let l j (p : ℕ) := if hp : p.Prime then ell j ⟨p, hp⟩ else 0
  have hrel j := S.allPrimeHecke_eigen_relations a b σ (v j) (l j) (by
    intro p
    simpa only [l, dite_eq_left p.property] using hell j p)
  have hf j : Continuous (f j).val := S.newBandRepresentative_continuous a b σ (v j)
  have hfemb j : AutomorphicL2.denseEmbedding _ _ (f j) =
      ((v j).val.val.val : AutomorphicSpace N) := S.newBandRepresentative_embedding a b σ (v j)
  have hf0 j : f j ≠ 0 := by
    intro hz
    have hh := hfemb j
    rw [hz, map_zero] at hh
    exact hv.ne_zero j (Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext hh.symm))))
  have hc j : AutomorphicL2.denseEmbedding _ _ (f j) ∈ localCuspidalSpace N hN := by
    rw [hfemb j]
    exact (v j).val.val.val.property
  have hn j : AutomorphicL2.denseEmbedding _ _ (f j) ∈ newSpace N hN := by
    rw [hfemb j]
    have hh := (v j).property
    rwa [mem_partialParityBand, partialNewSpace_univ] at hh
  have hs j : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ (f j)) =
      (-1 : ℂ) ^ δ • AutomorphicL2.denseEmbedding _ _ (f j) := by
    rw [hfemb j]
    simpa only [σ, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one] using
      S.newBand_reflection a b σ hσ (v j)
  have hg j : FriedrichsGraph N (AutomorphicL2.denseEmbedding _ _ (f j))
      (((1 / 4 + r j ^ 2 : ℝ) : ℂ) • AutomorphicL2.denseEmbedding _ _ (f j)) := by
    simpa only [hfemb j] using heigen j
  have hw j : frickeIsometry N hN (AutomorphicL2.denseEmbedding _ _ (f j)) =
      χ j • AutomorphicL2.denseEmbedding _ _ (f j) := by
    rw [hfemb j]
    exact congrArg (fun u : S.partialParityBand a b σ univ =>
      (u.val.val.val : AutomorphicSpace N)) (hfr j)
  have hp j : PrimeHeightEigenrelations N (l j) (actualHeightCoefficients (f j).val) :=
    physical_prime_height_relations N hN (f j) (hf j) (l j) (hrel j).1 (hrel j).2
  let q j : ℝ × (ℕ → ℂ) := (r j, canonicalEulerCoefficients N (l j))
  refine ⟨q, ?_, ?_⟩
  · intro i j hij
    have hrj : r i = r j := congrArg Prod.fst hij
    have hec : canonicalEulerCoefficients N (l i) = canonicalEulerCoefficients N (l j) :=
      congrArg Prod.snd hij
    obtain ⟨c, d, hc0, _hd0, hcd⟩ := actual_coefficients_proportional N hN (r i)
      (f i) (f j) (hf i) (hf j) (hf0 i) (hf0 j) (hc i) (hc j)
      ((-1 : ℂ) ^ δ) (hs i) (hs j) (hg i) (by rw [hrj]; exact hg j)
      (l i) (l j) (hp i) (hp j) hec
    rw [hfemb i, hfemb j] at hcd
    exact hv.eq_of_smul_apply_eq_smul_apply c d i j hc0
      (Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext hcd))))
  · intro j
    exact ⟨hr j, hwin j, actual_eigenform_euler_solution N hN (r j) δ hδ
      (f j) (hf j) (hf0 j) (hc j) (hn j) (hs j) (hg j)
      (χ j) (hχ j) (hw j) (l j) (hrel j).1 (hrel j).2⟩

#print axioms exists_new_band_euler_family

end CuspEnergySpectrum

/-- There are at least as many distinct literal solutions as the actual
new-parity dimension, without any assumption of automorphy on solutions. -/
theorem exists_literal_maass_lower_subset (N : ℕ) (hN : 0 < N)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (t ε : ℝ) :
    ∃ A : Set (ℝ × (ℕ → ℂ)), A.Finite ∧
      A ⊆ QuantitativeConcreteGoals.maassWindow N δ t ε ∧
      A.ncard = partialParityCount N univ t (t + ε) ((-1 : ℝ) ^ δ) := by
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨q, hq, hm⟩ := (geometricCuspSpectrum N hN).exists_new_band_euler_family
    t (t + ε) δ hδ
  refine ⟨range q, finite_range q, ?_, ?_⟩
  · rintro _ ⟨j, rfl⟩
    exact hm j
  · rw [← image_univ, ncard_image_of_injective _ hq, ncard_univ, Nat.card_fin,
      partialParityCount_eq N hN]

/-- The literal solution cardinality dominates the actual new-parity
dimension, also when finiteness has not yet been established. -/
theorem literal_maass_encard_lower (N : ℕ) (hN : 0 < N)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (t ε : ℝ) :
    (partialParityCount N univ t (t + ε) ((-1 : ℝ) ^ δ) : ENat) ≤
      (QuantitativeConcreteGoals.maassWindow N δ t ε).encard := by
  obtain ⟨A, hA, hsub, hcard⟩ := exists_literal_maass_lower_subset N hN δ hδ t ε
  rw [← hcard, hA.cast_ncard_eq]
  exact encard_le_encard hsub

/-- Unconditional finite-subset lower bound with exactly the manuscript's
shrinking-window hypotheses and arithmetic leading coefficient. -/
theorem original_maass_solution_lower (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop)
    (c : ℝ) (hc : c < AsymptoticTotalNewCorner.arithmeticCoefficient N) :
    ∀ᶠ t in atTop, ∃ A : Set (ℝ × (ℕ → ℂ)), A.Finite ∧
      A ⊆ QuantitativeConcreteGoals.maassWindow N δ t (ε t) ∧
      c * (t * ε t) ≤ (A.ncard : ℝ) := by
  filter_upwards [original_new_parity_count_lower N hN δ hδ ε hε hproduct c hc] with t ht
  obtain ⟨A, hA, hsub, hcard⟩ := exists_literal_maass_lower_subset N hN.1 δ hδ t (ε t)
  exact ⟨A, hA, hsub, by rwa [hcard]⟩

/-- An unconditional lower bound for the cardinality of the literal
solution set. Extended natural cardinality records infinite sets correctly;
no finiteness or automorphy premise is needed. -/
theorem original_maass_solution_encard_lower (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop)
    (c : ℝ) (hc : c < AsymptoticTotalNewCorner.arithmeticCoefficient N) :
    ∀ᶠ t in atTop, (Nat.ceil (c * (t * ε t)) : ENat) ≤
      (QuantitativeConcreteGoals.maassWindow N δ t (ε t)).encard := by
  filter_upwards [original_maass_solution_lower N hN δ hδ ε hε hproduct c hc] with t ht
  obtain ⟨A, hA, hsub, hcard⟩ := ht
  have hn : Nat.ceil (c * (t * ε t)) ≤ A.ncard := Nat.ceil_le.mpr hcard
  have hcast : (Nat.ceil (c * (t * ε t)) : ENat) ≤ (A.ncard : ENat) := by
    exact_mod_cast hn
  exact hcast.trans (by rw [hA.cast_ncard_eq]; exact encard_le_encard hsub)

/-- Finiteness of the whole literal solution window is the separate
upper-bound obligation; once available, the subset estimate is an ncard estimate. -/
theorem original_maass_solution_ncard_lower (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop)
    (hfinite : ∀ᶠ t in atTop, (QuantitativeConcreteGoals.maassWindow N δ t (ε t)).Finite)
    (c : ℝ) (hc : c < AsymptoticTotalNewCorner.arithmeticCoefficient N) :
    ∀ᶠ t in atTop, c * (t * ε t) ≤
      ((QuantitativeConcreteGoals.maassWindow N δ t (ε t)).ncard : ℝ) := by
  filter_upwards [original_maass_solution_lower N hN δ hδ ε hε hproduct c hc, hfinite]
    with t ht hfin
  obtain ⟨A, _hA, hsub, hcard⟩ := ht
  exact hcard.trans (by exact_mod_cast ncard_le_ncard hsub hfin)

#print axioms actual_coefficients_proportional
#print axioms exists_literal_maass_lower_subset
#print axioms literal_maass_encard_lower
#print axioms original_maass_solution_lower
#print axioms original_maass_solution_encard_lower
#print axioms original_maass_solution_ncard_lower

end QuantitativeNinaMaass
