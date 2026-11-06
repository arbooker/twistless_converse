module

public import QuantitativeArithmeticRadicalCountTheoremV1
public import QuantitativeArithmeticSmallLevelCircTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRadicalCircCount
open Filter Asymptotics UpperHalfPlane FinitenessOriginalInput SmallLevelOriginal
open QuantitativeArithmeticSmallLevelCirc AsymptoticClassicalCusp
open AsymptoticSectorComparison

/-- Fourier inversion for the unitary coefficients of any actual cusp form. -/
theorem cusp_isModular {N k : ℕ} [NeZero N]
    (f : CuspForm (AsymptoticClassicalCusp.level N) (k:ℤ)) :
    IsModular N k (AsymptoticClassicalLSeries.coefficients f) := by
  refine ⟨CuspForm.toModularFormₗ f,?_⟩
  have hc : FinitenessOriginalFourier.fullCoefficients (AsymptoticClassicalLSeries.coefficients f) k =
      fun n => (qExpansion 1 f).coeff n := by
    funext n
    by_cases hn : n=0
    · subst n
      rw [FinitenessOriginalFourier.fullCoefficients_zero
        (AsymptoticClassicalLSeries.coefficients_zero f),
        CuspFormClass.qExpansion_coeff_zero f zero_lt_one (level_one_period N)]
    · exact AsymptoticClassicalLSeries.coefficients_recover f n (Nat.pos_of_ne_zero hn)
  funext z
  change f z=FinitenessPolynomialSeries.sum
    (FinitenessOriginalFourier.fullCoefficients (AsymptoticClassicalLSeries.coefficients f) k)
    (Function.Periodic.qParam 1 z)
  rw [hc,FinitenessPolynomialSeries.sum_eq_tsum]
  exact (ModularForm.hasSum_qExpansion (f:=CuspForm.toModularFormₗ f) zero_lt_one
    (level_one_period N) z).tsum_eq.symm

/-- The classical cuspidal newspace embeds in the modular Euler solution
family, hence its dimension is at most the full trace-new modular dimension. -/
theorem new_dimension_le_circ (N k : ℕ) [NeZero N]
    (hN : 0<N) (hk : 0<k) (heven : Even k) :
    Module.finrank ℂ (newSpace N hN (k:ℤ))≤Module.finrank ℂ (space N hN k) := by
  obtain ⟨f,hf,hone,he⟩ := exists_normalized_new_prime_family N hN (k:ℤ)
  obtain ⟨hfinite,hcount⟩ := modularSolutions_count N k hN hk heven
  let := hfinite
  have hsol (j) : IsSolution N k (AsymptoticClassicalLSeries.coefficients (f j).val) := by
    obtain ⟨e,he⟩ := he j
    exact new_prime_eigen_isSolution N k hN hk heven (f j).val (f j).property (hone j) e he
  let J : Fin (Module.finrank ℂ (newSpace N hN (k:ℤ))) → modularSolutions N k :=
    fun j => ⟨AsymptoticClassicalLSeries.coefficients (f j).val,hsol j,cusp_isModular (f j).val⟩
  have hJ : Function.Injective J := by
    intro i j hij
    apply hf
    exact Subtype.ext (AsymptoticClassicalLSeries.coefficients_injective (congrArg Subtype.val hij))
  have hl := Nat.card_le_card_of_injective J hJ
  rw [Nat.card_fin,hcount] at hl
  exact hl

/-- The full Mcirc eigenbasis contributes distinct original Euler solutions. -/
theorem circ_dimension_le_count (N k : ℕ) [NeZero N]
    (hN : 0<N) (hk : 0<k) (heven : Even k) (hs : (S N k).Finite) :
    Module.finrank ℂ (space N hN k)≤(S N k).ncard := by
  let := hs.fintype
  obtain ⟨hfinite,hcount⟩ := modularSolutions_count N k hN hk heven
  let J : modularSolutions N k → S N k := fun f => ⟨f.val,f.property.1⟩
  have hJ : Function.Injective J := fun f g he => Subtype.ext (congrArg (fun v : S N k => v.val) he)
  have hl := Nat.card_le_card_of_injective J hJ
  rw [hcount] at hl
  simpa only [Nat.card_coe_set_eq] using hl

/-- Theorem 1.2 with the literal M_k^circ target: the exact full modular
intersection differs from the original Euler count by O_N(k/loglog(2k)).
No modularity, growth, or quantitative-count hypothesis is added. -/
theorem literal_endpoint (N : ℕ) (hN : 0<N)
    (hrad : N<(∏p∈N.primeFactors,p)^2) :
    (fun k : ℕ => ((S N k).ncard:ℝ)-
      (Module.finrank ℂ (space N hN k):ℝ))
      =O[evenWeights] (fun k : ℕ => (k:ℝ)/Real.log (Real.log (2*(k:ℝ)))) := by
  let : NeZero N := ⟨hN.ne'⟩
  have hmain := QuantitativeArithmeticRadicalCountTheorem.literal_endpoint N hN hrad
  apply Asymptotics.IsBigO.trans _ hmain
  apply IsBigO.of_bound 1
  obtain ⟨C,hC,hfinite⟩ := QuantitativeArithmeticRadicalFiniteness.even_weight N hN hrad
  have he : ∀ᶠ k in evenWeights,Even k :=
    Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr (fun _ h => h))
  have hk : ∀ᶠ k in evenWeights,0<k := (eventually_gt_atTop 0).filter_mono inf_le_left
  filter_upwards [hk,he] with k hk he
  have hlo := circ_dimension_le_count N k hN hk he (hfinite k hk he).1
  have hdim := new_dimension_le_circ N k hN hk he
  have hl : (Module.finrank ℂ (space N hN k):ℝ)≤((S N k).ncard:ℝ) := by exact_mod_cast hlo
  have hd : (Module.finrank ℂ (newSpace N hN (k:ℤ)):ℝ)≤
      (Module.finrank ℂ (space N hN k):ℝ) := by exact_mod_cast hdim
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hl),one_mul,
    Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hd.trans hl))]
  linarith

/-- Finiteness and the quantitative Mcirc count in a single release theorem. -/
theorem theorem12 (N : ℕ) (hN : 0<N)
    (hrad : N<(∏p∈N.primeFactors,p)^2) :
    (∀k : ℕ,0<k → Even k → (S N k).Finite) ∧
    (fun k : ℕ => ((S N k).ncard:ℝ)-(Module.finrank ℂ (space N hN k):ℝ))
      =O[evenWeights] (fun k : ℕ => (k:ℝ)/Real.log (Real.log (2*(k:ℝ)))) := by
  obtain ⟨C,hC,hfinite⟩ := QuantitativeArithmeticRadicalFiniteness.even_weight N hN hrad
  exact ⟨fun k hk he => (hfinite k hk he).1,literal_endpoint N hN hrad⟩

#print axioms cusp_isModular
#print axioms new_dimension_le_circ
#print axioms circ_dimension_le_count
#print axioms literal_endpoint
#print axioms theorem12
end QuantitativeArithmeticRadicalCircCount
