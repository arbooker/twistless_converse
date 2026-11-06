module

public import SmallLevelNormalizedEvenFrickeV1
public import Mathlib.NumberTheory.ModularForms.NormTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc

open UpperHalfPlane FinitenessOriginalInput SmallLevelOriginal
open scoped ModularForm

abbrev level (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))

/-- The literal unnormalised modular-form trace to level N/p. -/
def primeTrace (N : ℕ) (hN : 0 < N) (k : ℤ)
    (p : {p : ℕ // p.Prime ∧ p ∣ N}) (F : ModularForm (level N) k) :
    ModularForm (level (N / p.val)) k := by
  let : NeZero N := ⟨hN.ne'⟩
  let : NeZero (N / p.val) := ⟨(Nat.div_pos (Nat.le_of_dvd hN p.property.2)
    p.property.1.pos).ne'⟩
  let : (level N).IsFiniteRelIndex (level (N / p.val)) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level (N / p.val))).symm).1
  exact ModularForm.trace (level (N / p.val)) F

/-- Membership in the paper's M_k^circ: genuine modular forms F and F|W_N,
vanishing at infinity (equivalently F at infinity and zero), with both
literal traces to N/p zero for every prime divisor p. No vanishing at
other cusps is imposed. The existential G simply bundles F|W_N as a form. -/
def IsCirc (N : ℕ) (hN : 0 < N) (k : ℕ) (f : ℕ → ℂ) : Prop :=
  ∃ F G : ModularForm (level N) (k : ℤ),
    (F : ℍ → ℂ) = fourierFunction k f ∧
    (G : ℍ → ℂ) = (F : ℍ → ℂ) ∣[(k : ℤ)] SmallLevelNormalized.fricke N hN ∧
    IsZeroAtImInfty (F : ℍ → ℂ) ∧ IsZeroAtImInfty (G : ℍ → ℂ) ∧
    ∀ p : {p : ℕ // p.Prime ∧ p ∣ N},
      primeTrace N hN (k : ℤ) p F = 0 ∧ primeTrace N hN (k : ℤ) p G = 0

/-- The corrected literal target for all thirty-four levels. -/
def SmallLevelsCircTheorem : Prop :=
  ∀ N k : ℕ, ∀ hN : 0 < N, N ≤ 36 → N ≠ 29 → N ≠ 31 → 0 < k → Even k →
    ∀ f : ℕ → ℂ, IsSolution N k f → IsCirc N hN k f

theorem IsCirc.isModular {N k : ℕ} {hN : 0 < N} {f : ℕ → ℂ}
    (h : IsCirc N hN k f) : IsModular N k f := by
  obtain ⟨F, _, hF, _⟩ := h
  exact ⟨F, hF⟩

theorem primeTrace_smul (N : ℕ) (hN : 0 < N) (k : ℤ)
    (p : {p : ℕ // p.Prime ∧ p ∣ N}) (c : ℂ) (F : ModularForm (level N) k) :
    primeTrace N hN k p (c • F) = c • primeTrace N hN k p F := by
  classical
  unfold primeTrace
  ext z
  simp only [ModularForm.coe_trace, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  induction q using Quotient.inductionOn with
  | h r =>
    simp only [SlashInvariantForm.quotientFunc_mk, FunLike.coe_smul, ModularForm.smul_slash,
      σ, Subgroup.HasDetOne.det_eq ((level (N / p.val)).inv_mem r.property),
      Units.val_one, zero_lt_one, ite_true, ContinuousAlgEquiv.refl_apply, Pi.smul_apply, smul_eq_mul]

/-- The original untwisted functional equation proves the two required
cusp vanishings, even before modularity is established. -/
theorem original_two_cusps {N m : ℕ} (hN : 0 < N) {f : ℕ → ℂ}
    (hf : IsSolution N (2*m) f) :
    IsZeroAtImInfty (fourierFunction (2*m) f) ∧
    IsZeroAtImInfty (fourierFunction (2*m) f ∣[((2*m : ℕ) : ℤ)]
      SmallLevelNormalized.fricke N hN) := by
  have hz := fourierFunction_zeroAtInfty hf
  obtain ⟨χ, _, hχ⟩ := SmallLevelNormalized.original_fricke_sign hN m hf
  refine ⟨hz, ?_⟩
  rw [hχ]
  change Filter.Tendsto (fun z => χ * fourierFunction (2*m) f z) atImInfty (nhds 0)
  simpa only [mul_zero] using hz.const_mul χ

/-- Only the ordinary trace remains after modularity: Fricke and the
second trace, as well as the two cusp vanishings, follow from original
input. This is a reduction lemma, not an assertion that trace vanishing
has already been proved. -/
theorem of_modular_trace {N m : ℕ} (hN : 0 < N) {f : ℕ → ℂ}
    (hf : IsSolution N (2*m) f) (F : ModularForm (level N) ((2*m : ℕ) : ℤ))
    (hF : (F : ℍ → ℂ) = fourierFunction (2*m) f)
    (ht : ∀ p : {p : ℕ // p.Prime ∧ p ∣ N}, primeTrace N hN _ p F = 0) :
    IsCirc N hN (2*m) f := by
  obtain ⟨χ, _, hχ⟩ := SmallLevelNormalized.original_fricke_sign hN m hf
  refine ⟨F, χ • F, hF, ?_, ?_, ?_, ?_⟩
  · change χ • (F : ℍ → ℂ) = _
    rw [hF]
    exact hχ.symm
  · rw [hF]
    exact (original_two_cusps hN hf).1
  · change IsZeroAtImInfty (χ • (F : ℍ → ℂ))
    rw [hF]
    change Filter.Tendsto (fun z => χ * fourierFunction (2*m) f z) atImInfty (nhds 0)
    simpa only [mul_zero] using (original_two_cusps hN hf).1.const_mul χ
  · intro p
    exact ⟨ht p, by rw [primeTrace_smul, ht p, smul_zero]⟩

#print axioms primeTrace_smul
#print axioms original_two_cusps
#print axioms of_modular_trace

end QuantitativeArithmeticSmallLevelCirc
