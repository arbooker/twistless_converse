module

public import QuantitativeSpectralObservabilityFundamentalSamplingV1
public import QuantitativeSpectralObservabilityUniformV1
public import QuantitativeSpectralExceptionalFundamentalWordsV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open Matrix UpperHalfPlane Set
open AsymptoticCongruenceLabels AsymptoticHyperbolicArea
open AsymptoticOrbitDecode AsymptoticCompactBranch AsymptoticOrbitDiagonal
open QuantitativeSpectralWordDefect
open scoped MatrixGroups BigOperators lp

theorem finite_terminal_fundamental_words (N : ℕ) (hN : 0<N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ W : Finset (List SL(2,ℤ)),
      (∀ l∈W, ∀ a∈l, a∈S ∨ a⁻¹∈S) ∧
      ∀ H : ℝ, max ε⁻¹ 4≤H → ∀ z∈terminalBand ε H,
        ∃ l∈W, integralLabel l.prod • z∈fundamentalCompact N H := by
  classical
  obtain ⟨W,hW,hw⟩ := finite_terminal_words_retained N S hS hε
  obtain ⟨V,hV,hv⟩ := QuantitativeSpectralExceptionalGeometry.finite_wide_fundamental_words
    N hN S hS
  let f : List SL(2,ℤ) × List SL(2,ℤ) → List SL(2,ℤ) := fun p => p.2++p.1
  refine ⟨(W.product V).image f,?_,?_⟩
  · intro l hl a ha
    obtain ⟨⟨u,v⟩,huv,rfl⟩ := Finset.mem_image.mp hl
    rcases List.mem_append.mp ha with ha | ha
    · exact hV v (Finset.mem_product.mp huv).2 a ha
    · exact hW u (Finset.mem_product.mp huv).1 a ha
  · intro H hH z hz
    obtain ⟨l,hl,hlz⟩ := hw H ((le_max_left _ _).trans hH) z hz.1 hz.2
    obtain ⟨m,hm,hmz⟩ := hv H ((le_max_right _ _).trans hH) _ hlz
    refine ⟨m++l,Finset.mem_image.mpr ⟨(l,m),Finset.mem_product.mpr ⟨hl,hm⟩,rfl⟩,?_⟩
    simpa only [List.prod_append,map_mul,mul_smul] using hmz

theorem terminalBand_fundamental_energy (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε)
    (H : ℝ) (t : ℕ) (W : Finset (List SL(2,ℤ)))
    (hW : ∀ z∈terminalBand ε H, ∃ l∈W,
      integralLabel l.prod • z∈fundamentalCompact N H)
    (x : ℍ) (v : ℓ²(OrbitGroup,ℂ)) :
    ‖corner (terminalBand ε H) x v‖^2 ≤
      2 * ∑ l : W, (‖fundamentalRawSampling N hN H hε t x v‖^2+
        ‖AsymptoticCongruenceDefect.operator l.val.prod
          (terminalRectangle_compact hε H) hε t x v‖^2) := by
  classical
  let u (l : W) := AsymptoticOrbitBranch.reindexLinear
    (Equiv.mulLeft (integralLabel l.val.prod)) (fundamentalRawSampling N hN H hε t x v)
  let d (l : W) := AsymptoticCongruenceDefect.operator l.val.prod
    (terminalRectangle_compact hε H) hε t x v
  have he := finite_reconstruction_energy (corner (terminalBand ε H) x v) u d (by
    intro g
    by_cases hg : g • x∈terminalBand ε H
    · obtain ⟨l,hl,hlg⟩ := hW (g • x) hg
      right
      refine ⟨⟨l,hl⟩,?_⟩
      have hrect := terminalBand_subset_rectangle ε H hg
      have himg : (integralLabel l.prod*g) • x∈fundamentalCompact N H := by
        simpa only [mul_smul] using hlg
      change corner (terminalBand ε H) x v g =
        fundamentalRawSampling N hN H hε t x v (integralLabel l.prod*g) -
          AsymptoticCongruenceDefect.operator l.prod (terminalRectangle_compact hε H) hε t x v g
      rw [corner_apply,ite_eq_left hg,fundamentalRawSampling_decode,ite_eq_left himg,
        AsymptoticCongruenceDefect.operator_decode,ite_eq_left hrect,
        cap_eq_one_of_terminal hε t (g • x) hg.1,
        decode_eq_self_of_terminal hε t x v g hg.1]
      simp
    · left
      rw [corner_apply,ite_eq_right hg])
  simpa only [u,d,AsymptoticOrbitBranch.reindex_norm] using he

/-- Polynomial terminal observability through the literal normalized
quotient sampler and the actual fixed signed-generator residuals. -/
theorem exists_polynomial_fundamental_observability (N : ℕ) (hN : 0<N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (B : ℝ), 1≤B ∧
      (∀ l∈W, ∀ a∈l, a∈S ∨ a⁻¹∈S) ∧
      ∀ (H : ℝ), max ε⁻¹ 4≤H → ∀ (t : ℕ) (ht : 1≤t) (x : ℍ),
        fundamentalGood N x → ∀ (v : ℓ²(OrbitGroup,ℂ)),
        ‖corner (terminal ε) x v‖^2 ≤
          2 * ∑ l : W, (‖fundamentalSampling N hN H hε ht x v‖^2+
            (l.val.length*transportPolynomial B H t*
              generatorResidual S (wordRegion_compact W hε H) hε t x v)^2)+
          ‖corner (terminal H) x v‖^2 := by
  obtain ⟨W,hW,hw⟩ := finite_terminal_fundamental_words N hN S hS hε
  obtain ⟨B,hB,hmat⟩ := finite_word_matrix_bound W
  refine ⟨W,B,hB,hW,?_⟩
  intro H hH t ht x hx v
  rw [fundamentalSampling_norm_eq_raw N hN H hε ht x hx v]
  apply (terminal_energy_split ε H x v).trans
  apply add_le_add _ le_rfl
  apply (terminalBand_fundamental_energy N hN hε H t W (hw H hH) x v).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro l _
  apply add_le_add le_rfl
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  apply word_norm_polynomial l.val hB (hmat l.val l.property) hε t
    (wordRegion_compact W hε H)
    (subset_iUnion (fun l : W => region l.val (terminalRectangle ε H)) l)
  intro a ha
  exact generator_le_residual S (wordRegion_compact W hε H) hε t x v a
    (hW l.val l.property a ha)

#print axioms finite_terminal_fundamental_words
#print axioms terminalBand_fundamental_energy
#print axioms exists_polynomial_fundamental_observability

end QuantitativeSpectralObservability
