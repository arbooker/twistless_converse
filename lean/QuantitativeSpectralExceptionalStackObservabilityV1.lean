module

public import QuantitativeSpectralExceptionalStackEnlargementV1
public import QuantitativeSpectralObservabilityFundamentalEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane Set ContinuousLinearMap AsymptoticObservationStack AsymptoticOrbitDiagonal
open AsymptoticRegularBranchFamily QuantitativeSpectralWordDefect
open QuantitativeSpectralObservability
open QuantitativeSpectralExceptionalUnweight (G Space)
open scoped MatrixGroups lp

variable {J : Type*} [Fintype J] {I K : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, Fintype (K j)]

/-- Every actual generator defect on the extra region is one restricted
coordinate of the single enlarged observation stack. -/
theorem generator_norm_le_enlarged (A : Finset SL(2,ℤ)) (b : ∀ j, I j → Branch)
    (w : ∀ j, K j → I j → List SL(2,ℤ)) (c : ∀ j, I j → ℂ)
    (s : J → Set ℍ) (hs : ∀ j, IsCompact (s j)) {v : Set ℍ} (hv : IsCompact v)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (a : SL(2,ℤ)) (ha : a∈A) (f : Space) :
    ‖AsymptoticCongruenceDefect.operator a hv hε t x f‖≤
      ‖stack (enlargedRows A b c (enlargedRegion_compact b w s hs hv) hε t x) f‖ := by
  apply (defect_restrict_norm hv (enlargedRegion_compact b w s hs hv)
    (fun _ hz => Or.inl hz) a hε t x f).trans
  exact PiLp.norm_apply_le
    (stack (enlargedRows A b c (enlargedRegion_compact b w s hs hv) hε t x) f)
    (Sum.inr ⟨a,ha⟩)

/-- The sum of generator and inverse-generator norms in terminal
observability is controlled by the same enlarged finite stack. -/
theorem generatorResidual_le_enlarged (S : Finset SL(2,ℤ)) (b : ∀ j, I j → Branch)
    (w : ∀ j, K j → I j → List SL(2,ℤ)) (c : ∀ j, I j → ℂ)
    (s : J → Set ℍ) (hs : ∀ j, IsCompact (s j)) {v : Set ℍ} (hv : IsCompact v)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (f : Space) :
    generatorResidual S hv hε t x f≤(2*(S.card:ℝ))*
      ‖stack (enlargedRows (signedGenerators S) b c (enlargedRegion_compact b w s hs hv) hε t x) f‖ := by
  let D := stack (enlargedRows (signedGenerators S) b c
    (enlargedRegion_compact b w s hs hv) hε t x) f
  calc
    _ ≤ ∑ a : ↥S, (2*‖D‖) := by
      apply Finset.sum_le_sum
      intro a _
      have ha := generator_norm_le_enlarged (signedGenerators S) b w c s hs hv hε t x
        a.val (mem_signedGenerators S a.val (Or.inl a.property)) f
      have hi := generator_norm_le_enlarged (signedGenerators S) b w c s hs hv hε t x
        a.val⁻¹ (mem_signedGenerators S a.val⁻¹ (Or.inr (by rw [inv_inv]; exact a.property))) f
      change _≤2*‖D‖
      dsimp only [D] at *
      linarith
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]; ring

/-- The actual quotient sampler and one common finite residual stack
control the terminal source. The compact region is constructed from all
row reduction words plus the terminal observability words. -/
theorem exists_enlarged_terminal_observability (N : ℕ) (hN : 0<N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (b : ∀ j, I j → Branch) (w : ∀ j, K j → I j → List SL(2,ℤ)) (c : ∀ j, I j → ℂ)
    (s : ℝ → J → Set ℍ) (hs : ∀ H j, IsCompact (s H j))
    {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (B : ℝ), 1≤B ∧
      (∀ l∈W, ∀ a∈l, a∈S ∨ a⁻¹∈S) ∧
      ∀ (H : ℝ), max ε⁻¹ 4≤H → ∀ (t : ℕ) (ht : 1≤t) (x : ℍ),
        fundamentalGood N x → ∀ (f : Space),
        let hu := enlargedRegion_compact b w (s H) (hs H) (wordRegion_compact W hε H)
        let D := stack (enlargedRows (signedGenerators S) b c hu hε t x)
        ‖corner (AsymptoticHyperbolicArea.terminal ε) x f‖^2 ≤
          2*∑ l : ↥W, (‖fundamentalSampling N hN H hε ht x f‖^2+
            (l.val.length*transportPolynomial B H t*((2*(S.card:ℝ))*‖D f‖))^2)+
          ‖corner (AsymptoticHyperbolicArea.terminal H) x f‖^2 := by
  obtain ⟨W,B,hB,hW,hobs⟩ := exists_polynomial_fundamental_observability N hN S hS hε
  refine ⟨W,B,hB,hW,?_⟩
  intro H hH t ht x hx f
  apply (hobs H hH t ht x hx f).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro l _
  apply add_le_add le_rfl
  have hpoly : 0≤transportPolynomial B H t := by unfold transportPolynomial; positivity
  have hgen : 0≤generatorResidual S (wordRegion_compact W hε H) hε t x f :=
    Finset.sum_nonneg (fun a _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
  apply pow_le_pow_left₀ (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hpoly) hgen) _ 2
  exact mul_le_mul_of_nonneg_left
    (generatorResidual_le_enlarged S b w c (s H) (hs H) (wordRegion_compact W hε H) hε t x f)
    (mul_nonneg (Nat.cast_nonneg _) hpoly)

#print axioms generatorResidual_le_enlarged
#print axioms exists_enlarged_terminal_observability

end QuantitativeSpectralExceptionalReducedRows
