module

public import QuantitativeArithmeticSmallLevelCircCoefficientsV1
public import FinitenessOriginalDiskIndependenceV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane FinitenessOriginalInput FinitenessOriginalFourier SmallLevelOriginal

/-- The q-expansion of an original modular solution is its literal
weight-adjusted Fourier sequence. The Dirichlet normalization stays in f. -/
theorem original_coefficient {N k : ℕ} {hN : 0<N} {f : ℕ → ℂ}
    (hf : IsSolution N k f) (F : space N hN k)
    (hF : (F.val : ℍ → ℂ) = fourierFunction k f) (n : ℕ) :
    coefficient N hN k n F = fullCoefficients f k n := by
  obtain ⟨σ, _, hg⟩ := hf.growth
  have hpoly := polynomial_bound hf.zero hg k
  apply Eq.symm
  apply ModularFormClass.qExpansion_coeff_unique zero_lt_one
    (AsymptoticClassicalCusp.level_one_period N) (f := F.val)
  intro z
  have hs := (FinitenessPolynomialSeries.summable hpoly
    (Function.Periodic.norm_qParam_lt_one zero_lt_one z.im_pos)).hasSum
  change HasSum (fun n => fullCoefficients f k n •
    Function.Periodic.qParam 1 (z : ℂ)^n) (F.val z)
  rw [show F.val z = fourierFunction k f z from congrFun hF z]
  simpa only [fourierFunction, FinitenessFourierConstruction.fourier,
    FinitenessPolynomialSeries.sum_eq_tsum, smul_eq_mul] using hs

/-- Actual Fourier extraction on M_k^circ is linear. -/
def coefficientSequence (N : ℕ) (hN : 0<N) (k : ℕ) :
    space N hN k →ₗ[ℂ] (ℕ → ℂ) := LinearMap.pi (coefficient N hN k)

/-- Original Euler independence transfers to ANY family of actual
M_k^circ representatives. No spectral or eigenbasis premise occurs. -/
theorem original_family_independent {N k : ℕ} {hN : 0<N}
    (F : S N k → space N hN k)
    (hF : ∀ f, ((F f).val : ℍ → ℂ) = fourierFunction k f.val) :
    LinearIndependent ℂ F := by
  apply LinearIndependent.of_comp (coefficientSequence N hN k)
  have he : (fun f => coefficientSequence N hN k (F f)) =
      (fun f : S N k => fullCoefficients f.val k) := by
    funext f n
    exact original_coefficient f.property (F f) (hF f) n
  change LinearIndependent ℂ (fun f => coefficientSequence N hN k (F f))
  rw [he]
  exact FinitenessOriginalDiskIndependence.normalized_independent N k

/-- Whenever original solutions are modular, they form a finite set
with cardinality at most the dimension of the literal M_k^circ.
The reverse inequality needs a full modular (including Eisenstein)
eigenbasis and is NOT assumed or asserted here. -/
theorem original_count_le {N k : ℕ} (hN : 0<N) (hk : 0<k) (heven : Even k)
    (hmod : ∀ f : ℕ → ℂ, IsSolution N k f → IsModular N k f) :
    Finite (S N k) ∧ Nat.card (S N k) ≤ Module.finrank ℂ (space N hN k) := by
  classical
  have hrep (f : S N k) :
      ∃ F : space N hN k, (F.val : ℍ → ℂ) = fourierFunction k f.val :=
    original_modular_mem_space hN hk heven f.property (hmod f.val f.property)
  let F : S N k → space N hN k := fun f => (hrep f).choose
  have hF : LinearIndependent ℂ F := original_family_independent F
    (fun f => (hrep f).choose_spec)
  have hfinite : Finite (S N k) := hF.finite
  let := hfinite
  let := Fintype.ofFinite (S N k)
  refine ⟨hfinite, ?_⟩
  rw [Nat.card_eq_fintype_card]
  exact hF.fintype_card_le_finrank

/-- Uniform specialization to precisely the small-level theorem range. -/
theorem smallLevels_count_le_of_modular (h : SmallLevelsTheorem)
    (N k : ℕ) (hN : 0<N) (h36 : N≤36) (h29 : N≠29) (h31 : N≠31)
    (hk : 0<k) (heven : Even k) :
    Finite (S N k) ∧ Nat.card (S N k) ≤ Module.finrank ℂ (space N hN k) :=
  original_count_le hN hk heven (h N k hN h36 h29 h31 hk heven)

#print axioms original_coefficient
#print axioms original_family_independent
#print axioms original_count_le
#print axioms smallLevels_count_le_of_modular
end QuantitativeArithmeticSmallLevelCirc
